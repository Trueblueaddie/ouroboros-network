{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Test.Consensus.Mempool.State.SUT (semantics, TestLedgerDB) where

import           Control.Exception (ErrorCall, throw)
import           Control.Monad (void, when)
import           Control.Monad.Class.MonadSTM.Strict
import           Control.Monad.Trans.Class (lift)
import           Control.Monad.Trans.Reader
import           Control.Tracer
import           Data.Bifunctor (Bifunctor(bimap))
import           Data.Foldable
import           Data.IORef
import           Data.Maybe (fromJust)

import           Cardano.Slotting.Slot

import           Ouroboros.Consensus.Ledger.Basics
import           Ouroboros.Consensus.Ledger.Extended
import           Ouroboros.Consensus.Ledger.SupportsMempool
import           Ouroboros.Consensus.Ledger.SupportsProtocol
import           Ouroboros.Consensus.Mempool
import qualified Ouroboros.Consensus.Mempool.TxSeq as TxSeq
import           Ouroboros.Consensus.Storage.LedgerDB.HD.BackingStore
import           Ouroboros.Consensus.Storage.LedgerDB.HD.DiffSeq
import           Ouroboros.Consensus.Storage.LedgerDB.OnDisk
import           Ouroboros.Consensus.Util.IOLike hiding (newTVarIO)
import qualified Ouroboros.Consensus.Util.MonadSTM.RAWLock as RAWLock

import           Ouroboros.Network.Block

import           Test.StateMachine

import           Test.Consensus.Mempool.State.Types
import           Test.Consensus.Mempool.State.Model

import           Debug.Trace
import qualified Data.List.NonEmpty as NE
import Data.Function (on)
import Data.List.NonEmpty (NonEmpty)

-- | A mock LedgerDB that has the bare minimum to fulfill the LedgerInterface
data TestLedgerDB m blk =
  TestLedgerDB
    !(LedgerBackingStore m (ExtLedgerState blk))
    !(StrictTVar m (WithOrigin SlotNo, NonEmpty (LedgerState blk ValuesMK))) --(LedgerState blk EmptyMK, MempoolChangelog blk))

newLedgerInterface ::
  ( IOLike m
  , LedgerSupportsProtocol blk
  , SufficientSerializationForAnyBackingStore (LedgerState blk)
  )
  => LedgerState blk ValuesMK
 -> m ( TestLedgerDB m blk
      , LedgerInterface m blk
      , RAWLock.RAWLock m ()
      )
newLedgerInterface st = do
  bkst   <- createTVarBackingStore (ExtLedgerStateTables $ projectLedgerTables st)
  ledger <- newTVarIO ((pointSlot $ getTip st), st NE.:| [])
  rw <- RAWLock.new ()
  pure $ ( TestLedgerDB bkst ledger
         , LedgerInterface {
               getCurrentLedgerAndChangelog = do
                   (s, values) <- readTVar ledger
                   let projected = [ (slot, projectLedgerTables thisst) | thisst <- NE.toList values, let slot = pointSlot $ getTip thisst, slot > s ]
                       zipped = zip projected $ tail projected
                       diffs = foldl'
                         (\acc ((_, prev), (thisslot, next)) -> zipLedgerTables (ext (withOrigin' thisslot)) acc (zdiff prev next))
                         polyEmptyLedgerTables
                         zipped
                   pure $ (forgetLedgerTables $ NE.last values,) $ MempoolChangelog s diffs
             , getBackingStore              = pure bkst
             , withReadLock                 = \m -> RAWLock.withReadAccess rw (\() -> m)
             }
         , rw)

ext :: (Ord k, Eq v) => SlotNo -> SeqDiffMK k v -> DiffMK k v -> SeqDiffMK k v
ext sl (ApplySeqDiffMK sq) (ApplyDiffMK d) = ApplySeqDiffMK $ extend sq sl d

semantics ::
  ( LedgerSupportsMempool blk
  , LedgerSupportsProtocol blk
  , HasTxId (GenTx blk)
  , Eq (GenTx blk)
  , SufficientSerializationForAnyBackingStore (LedgerState blk)
  )
  => LedgerConfig blk
  -> Bool
  -> Action blk Concrete
  -> ReaderT (IORef (Mempool IO blk TicketNo, TestLedgerDB IO blk, RAWLock.RAWLock IO ()))
             IO
             (Response blk Concrete)
semantics cfg trc action = do
  ref <- ask
  lift $ do
   myId <- myThreadId
   case action of
    Init st -> do
      when trc $ traceM $ "START " <> show myId <> " INIT"
      (testDb, iface, rwl) <- newLedgerInterface st
      -- The mempool has to be opened without the sync thread so that we are the
      -- ones that perform the sync manually
      mp <- openMempoolWithoutSyncThread iface cfg NoMempoolCapacityBytesOverride nullTracer txInBlockSize
      atomicWriteIORef ref (mp, testDb, rwl)
      when trc $ traceM $ "END " <> show myId <> " INIT"
      pure ResponseOk

    TryAddTxs txs -> do
      when trc $ traceM $ "START " <> show myId <> " TRYADDTXS"
      (mp, _, _) <- readIORef ref
      -- Get the transactions before this call
      txsOld <- atomically $ snapshotTxs <$> getSnapshot mp
      stOrig <- unsafeGetMempoolState mp
      -- Process the transactions
      (processed, pending) <- tryAddTxs mp DoNotIntervene txs
      -- Get the transactions after
      snap <- atomically $ getSnapshot mp
      let txsNew = snapshotTxs snap
          -- The transactions removed are the ones that are missing in the txsNew
          -- It cannot be the case that a transactions that is removed is then added again, so we should be fine.
          removed = [ t' | t <- map fst txsOld
                         , let t' = txForgetValidated t
                         , not (elem t' $ map (txForgetValidated . fst) txsNew)
                         ]
          -- The transactions that were processed succesfully necesarily must appear
          -- in the later snapshot with a ticket number, so we can safely search for
          -- it.
          processedPlus = [ case t of
                              MempoolTxAdded t' -> MempoolTxAddedPlus
                                                   (TxSeq.TxTicket t'
                                                     ( snd
                                                       $ fromJust
                                                       $ find (\(ntx, _) -> txForgetValidated ntx == txForgetValidated t') txsNew
                                                     )
                                                     (txInBlockSize (txForgetValidated t'))
                                                   )
                              MempoolTxRejected t' _ -> MempoolTxRejectedPlus t'
                          | t <- processed
                          ]
      st <- unsafeGetMempoolState mp
      when trc $ traceM $ "END " <> show myId <> " TRYADDTXS"
      pure $ RespTryAddTxs (pointSlot (getTip stOrig) /= pointSlot (getTip st)) st (snapshotNextTicket snap) processedPlus pending removed

    SyncLedger -> do
      when trc $ traceM $ "START " <> show myId <> " SYNCLEDGER"
      (mp, TestLedgerDB _ stv, _) <- readIORef ref
      -- Getting the transactions before
      stOrig <- unsafeGetMempoolState mp
      (_, states) <- atomically $ readTVar stv
      txs <- atomically $ snapshotTxs <$> getSnapshot mp
      -- Peforming the sync with ledger, which happens to return the resulting snapshot, so we extract the new transactions
      txs' <- map (txForgetValidated . fst) . snapshotTxs <$> syncWithLedger mp

      st' <- unsafeGetMempoolState mp
      if pointSlot (getTip stOrig) /= pointSlot (getTip st') then do
        -- The difference are the transactions that have been removed
        when trc $ traceM $ "END " <> show myId <> " SYNCLEDGER"
        pure $ SyncOk states st' [ t' | (t, _) <- txs
                             , let t' = txForgetValidated t
                             , not (elem t' txs')
                             ]
      else
        pure ResponseOk

    GetSnapshot -> do
      when trc $ traceM $ "START " <> show myId <> " GETSNAP"
      (mp, _, _) <- readIORef ref
      t <- atomically $ Snapshot . snapshotTxs <$> getSnapshot mp
      when trc $ traceM $ "END " <> show myId <> " GETSNAP"
      pure t

    GetSnapshotFor st ch -> do
      when trc $ traceM $ "START " <> show myId <> " GETSNAPFOR"
      (mp, TestLedgerDB bs _, rwl) <- readIORef ref
      (sl, vs) <- readValues bs
      let !slot = withOrigin' $ pointSlot $ getTip st
          f :: (Ord k, Eq v) => SlotNo -> SeqDiffMK k v -> DiffMK k v -> SeqDiffMK k v
          f s (ApplySeqDiffMK sq) (ApplyDiffMK d) = ApplySeqDiffMK $ extend sq s d
      snap <- RAWLock.withReadAccess rwl (\() -> do
                                             let projected = map (\x -> (pointSlot $ getTip x, projectLedgerTables x)) ch
                                                 zipped = zip ((sl, vs):projected) projected
                                                 diffs = foldl'
                                                           (\acc ((_, prev), (s, next)) -> zipLedgerTables (f (withOrigin' s)) acc (zdiff prev next))
                                                           polyEmptyLedgerTables
                                                           zipped
                                             getSnapshotFor mp slot st $ MempoolChangelog sl diffs
                                         )
      when trc $ traceM $ "END " <> show myId <> " GETSNAPFOR"
      pure $ SnapshotFor $ fmap (fmap fst . snapshotTxs) snap

    UnsyncAnchor -> do
      when trc $ traceM $ "START " <> show myId <> " UnsyncAnchor"
      (_, TestLedgerDB (LedgerBackingStore bs) stv, rwl) <- readIORef ref
      RAWLock.withWriteAccess rwl (\() -> do
                                      (s, states) <- atomically $ readTVar stv
                                      case states of
                                        anchor NE.:| theTail@(next:_:_) -> do
                                          bsWrite bs (withOrigin' $ pointSlot $ getTip next) $ ExtLedgerStateTables $ zipLedgerTables (\a b -> rawForgetValues $ rawCalculateDifference a b) (projectLedgerTables anchor) (projectLedgerTables next)
                                          atomically $ writeTVar stv (pointSlot $ getTip next, fromJust $ NE.nonEmpty theTail)
                                        anchor NE.:| next:[] -> pure ()
                                        _ NE.:| [] -> pure ()
                                      pure ((), ()))
      when trc $ traceM $ "END " <> show myId <> " UnsyncAnchor"
      pure ResponseOk

    UnsyncTip states f -> do
      when trc $ traceM $  "START " <> show myId <> " UnsyncTip"
      when f $ void $ runReaderT (semantics cfg trc UnsyncAnchor) ref
      (_, TestLedgerDB bs stv, _) <- readIORef ref
      (sl, vs) <- readValues bs
      let projected = [ (slot, projectLedgerTables st) | st <- NE.toList states, let slot = pointSlot $ getTip st, slot > sl ]
          zipped = zip ((sl, vs):projected) projected
          diffs = foldl'
                    (\acc ((_, prev), (s, next)) -> zipLedgerTables (ext (withOrigin' s)) acc (zdiff prev next))
                    polyEmptyLedgerTables
                    zipped
      (anch, oldAnchor NE.:| _) <- atomically $ readTVar stv
      atomically $ writeTVar stv (anch, oldAnchor NE.:| NE.filter ((sl <) . pointSlot . getTip) states)
      when trc $ traceM $  "END " <> show myId <> " UnsyncTip"
      pure ResponseOk

readValues :: LedgerBackingStore IO (ExtLedgerState blk)
           -> IO (WithOrigin SlotNo, LedgerTables (LedgerState blk) ValuesMK)
readValues (LedgerBackingStore bs ) = (\(a,b) -> (a, unExtLedgerStateTables b)) . fromJust <$> unsafeRead bs
