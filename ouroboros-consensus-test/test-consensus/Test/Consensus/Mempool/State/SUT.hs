{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RecordWildCards #-}

module Test.Consensus.Mempool.State.SUT (semantics, TestLedgerDB) where

import           Control.Monad.Class.MonadSTM.Strict
import           Control.Monad.Trans.Class (lift)
import           Control.Monad.Trans.Reader
import           Control.Tracer
import           Data.Foldable
import           Data.IORef

import           Cardano.Slotting.Slot

import           Ouroboros.Consensus.Ledger.Basics
import           Ouroboros.Consensus.Ledger.Extended
import           Ouroboros.Consensus.Ledger.SupportsMempool
import           Ouroboros.Consensus.Ledger.SupportsProtocol
import           Ouroboros.Consensus.Mempool
import           Ouroboros.Consensus.Storage.LedgerDB.HD.BackingStore
import           Ouroboros.Consensus.Storage.LedgerDB.HD.DiffSeq
import           Ouroboros.Consensus.Storage.LedgerDB.OnDisk
import           Ouroboros.Consensus.Util.IOLike hiding (newTVarIO)
import qualified Ouroboros.Consensus.Util.MonadSTM.RAWLock as RAWLock

import           Ouroboros.Network.Block

import           Test.StateMachine

import           Test.Consensus.Mempool.State.Types

import qualified Data.List.NonEmpty as NE
import Data.List.NonEmpty (NonEmpty)

-- | A mock LedgerDB that has the bare minimum to fulfill the LedgerInterface
data TestLedgerDB m blk =
  TestLedgerDB
    !(LedgerBackingStore m (ExtLedgerState blk))
    !(StrictTVar m (NonEmpty (LedgerState blk ValuesMK)))

newLedgerInterface :: forall m blk.
  ( IOLike m
  , LedgerSupportsProtocol blk
  , SufficientSerializationForAnyBackingStore (LedgerState blk)
  )
  => LedgerState blk ValuesMK
 -> m ( TestLedgerDB m blk
      , LedgerInterface m blk
      )
newLedgerInterface st = do
  bkst   <- createTVarBackingStore (ExtLedgerStateTables $ projectLedgerTables st)
  ledger <- newTVarIO (st NE.:| [])
  rw <- RAWLock.new ()
  pure $ ( TestLedgerDB bkst ledger
         , LedgerInterface {
               getCurrentLedgerAndChangelog = do
                   states <- readTVar ledger
                   let diffs = changelogFromStates states
                   pure $ (forgetLedgerTables $ NE.last states,) $ MempoolChangelog (pointSlot $ getTip $ NE.head states) diffs
             , getBackingStore              = pure bkst
             , withReadLock                 = \m -> RAWLock.withReadAccess rw (\() -> m)
             }
         )

ext :: (Ord k, Eq v) => SlotNo -> SeqDiffMK k v -> DiffMK k v -> SeqDiffMK k v
ext sl (ApplySeqDiffMK sq) (ApplyDiffMK d) = ApplySeqDiffMK $ extend sq sl d

changelogFromStates ::
  ( TableStuff (LedgerState blk)
  , GetTip (LedgerState blk ValuesMK)
  )
  => NonEmpty (LedgerState blk ValuesMK)
  -> LedgerTables (LedgerState blk) SeqDiffMK
changelogFromStates (anchorState NE.:| states) =
  let projected = [ (slot, projectLedgerTables thisSt)
                  | thisSt <- states
                  , let slot = pointSlot $ getTip thisSt
                  , slot > pointSlot (getTip anchorState)
                  ]
      zipped = maybe [] (\s -> zip (NE.toList s) (NE.tail s)) $ NE.nonEmpty projected
  in foldl'
        (\acc ((_, prev), (thisslot, next)) ->
           zipLedgerTables
             (ext (withOrigin' thisslot))
             acc
             (zipLedgerTables (\a b -> rawForgetValues $ rawCalculateDifference a b) prev next)
        )
        polyEmptyLedgerTables
        zipped

semantics ::
  ( LedgerSupportsMempool blk
  , LedgerSupportsProtocol blk
  , HasTxId (GenTx blk)
  , SufficientSerializationForAnyBackingStore (LedgerState blk)
  )
  => LedgerConfig blk
  -> Action blk Concrete
  -> ReaderT (IORef ( Mempool IO blk TicketNo
                    , TestLedgerDB IO blk)
             )
             IO
             (Response blk Concrete)
semantics cfg action = do
  ref <- ask
  lift $ do
   case action of
    Init st -> do
      (testDb, iface) <- newLedgerInterface st
      -- The mempool has to be opened without the sync thread so that we are the
      -- ones that perform the sync manually
      mp <- openMempoolWithoutSyncThread iface cfg NoMempoolCapacityBytesOverride nullTracer txInBlockSize -- TODO @js trace the removed txs
      atomicWriteIORef ref (mp, testDb)
      pure ResponseOk

    TryAddTxs txs -> do
      (mp, _) <- readIORef ref
      (addTxsProcessed_, addTxsPending_, is) <- tryAddTxs' mp DoNotIntervene txs
      let (addTxsResult, addTxsUsedValues, addTxsCurrentTxs) = undefined is  -- TODO @js return the state, the forwarded tables (either combined with the ones from sync or only for add), and the resulting transactions in the same atomic block
      pure $ RespTryAddTxs{..}

    SyncLedger -> do
      (mp, _) <- readIORef ref
      snap <- syncWithLedger mp
      pure $ SyncOk undefined undefined (snapshotTxs snap) undefined -- TODO @js return the state, the forwarded tables, and the removed transactions (gather the chan from the trace above)

    GetSnapshot -> do
      (mp, _) <- readIORef ref
      fmap Snapshot . atomically $ getSnapshot mp

    GetSnapshotFor states@(anchor NE.:| _) -> do
      (mp, _) <- readIORef ref
      let slot  = pointSlot $ getTip anchor
          state' = applyChainTick cfg (withOrigin 1 (+ 1) slot) (forgetLedgerTables $ NE.last states)
      SnapshotFor <$> getSnapshotFor mp state' (MempoolChangelog slot (changelogFromStates states))


    Flush -> do
      (_, TestLedgerDB (LedgerBackingStore bs) stv) <- readIORef ref
      states <- atomically $ readTVar stv
      case states of
        anchor NE.:| (next:more@(_:_)) -> do
          bsWrite bs (withOrigin' $ pointSlot $ getTip next)
            $ ExtLedgerStateTables
            $ zipLedgerTables
                (\a b -> rawForgetValues $ rawCalculateDifference a b)
                (projectLedgerTables anchor)
                (projectLedgerTables next)
          atomically $ writeTVar stv (next NE.:| more)
        _ NE.:| _:[] -> pure ()
        _ NE.:| [] -> pure ()
      pure ResponseOk

    Switch states -> do
      (_, TestLedgerDB _ stv) <- readIORef ref
      (anchor NE.:| _) <- atomically $ readTVar stv
      atomically $ writeTVar stv (anchor NE.:| states)
      pure ResponseOk
