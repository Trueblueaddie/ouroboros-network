{-# LANGUAGE DeriveAnyClass       #-}
{-# LANGUAGE DeriveGeneric        #-}
{-# LANGUAGE DerivingStrategies   #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE KindSignatures       #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE PolyKinds            #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE StandaloneDeriving   #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE NamedFieldPuns  #-}

{-# OPTIONS_GHC -Wno-partial-fields -Wno-incomplete-record-updates -Wno-orphans #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Test.Consensus.Mempool.State -- (prop, prop')
where

import Control.Monad.Trans.Reader
import Data.IORef
import Data.Proxy (Proxy (..))

import Ouroboros.Consensus.Ledger.Basics
import Ouroboros.Consensus.Ledger.SupportsMempool
import Ouroboros.Consensus.Ledger.SupportsProtocol
import Ouroboros.Consensus.Mempool

import Test.QuickCheck
import Test.QuickCheck.Monadic
import Test.StateMachine
import Test.StateMachine.Types (
  ParallelCommandsF(..), Command(..), Commands(..), Pair(..), History (..), HistoryEvent (..))


import Test.Consensus.Mempool.State.Model
import Test.Consensus.Mempool.State.SUT
import Test.Consensus.Mempool.State.Types
import Test.Consensus.Mempool.Block

import qualified Data.List.NonEmpty as NE
import Data.List (intercalate)
import Ouroboros.Network.Block (pointSlot)
import NoThunks.Class
import GHC.Generics (Generic)
import Test.Util.TestBlock hiding (TestBlock)
import Control.Monad.Except (throwError)
import Control.Monad (foldM)
import Data.Maybe (fromJust, isNothing)

import Text.Layout.Table
import Data.List.NonEmpty (NonEmpty)
import qualified Ouroboros.Consensus.Mempool.TxSeq as TxSeq
import Data.Function (on)
import Data.Foldable
import qualified Ouroboros.Consensus.Storage.LedgerDB.HD.DiffSeq as DS
import qualified Data.Map.Strict as Map
import Control.Monad.IO.Class
import Cardano.Slotting.Slot (withOrigin)
import Data.Maybe (catMaybes)
import Cardano.Slotting.Time (slotLengthFromSec)
import Ouroboros.Consensus.HardFork.History.EraParams
import Ouroboros.Consensus.Protocol.Abstract

{-------------------------------------------------------------------------------
  Generation
-------------------------------------------------------------------------------}

genListOfStates :: LedgerState TestBlock ValuesMK
                  -> Gen (NonEmpty (LedgerState TestBlock ValuesMK))
genListOfStates firstState = do
  numStates <- listOf1 (pure ())
  valueChangelog <- snd <$> foldM (\(lastValues, acc) () ->  do
                                      nextValues <- nextRandomState lastValues

                                      pure (nextValues, nextValues:acc)) (firstState, []) numStates
  pure $ fromJust $ NE.nonEmpty $ reverse valueChangelog

generator ::
     Model TestBlock Symbolic
  -> Maybe (Gen (Action TestBlock Symbolic))
generator = \case
  NeedsInit -> Just $ Init <$> initialState
  model     -> Just $ frequency $
   [ (2, fmap TryAddTxs $ listOf1 $ arbitrary)
   , (1, pure GetSnapshot)
   , (1, do
         anchorSt <-
           if modelIsUnsynced model
           then randomState $ NE.head $ modelState model
           else pure $ NE.head $ modelState model
         GetSnapshotFor <$> genListOfStates anchorSt
     )
   , (1, Switch <$> frequency
                      [ (1, pure [])
                      , (10, NE.toList <$> genListOfStates (NE.head $ modelState model))
                      ]
     )
   , (1, pure Flush)
   ]

shrinker :: Model blk Symbolic -> Action blk Symbolic -> [Action blk Symbolic]
shrinker _ _ = []

preconditions :: Model blk Symbolic -> Action blk Symbolic -> Logic
-- When need init, only init
preconditions NeedsInit Init{} = Top
preconditions NeedsInit _      = Bot

-- Do not re-init
preconditions Model{}   Init{} = Bot
-- Ensure there are no switching/flushing concurrently
preconditions Model{modelIsUnsyncing} Flush    = Boolean (not modelIsUnsyncing)
preconditions Model{modelIsUnsyncing} Switch{} = Boolean (not modelIsUnsyncing)

-- Everything else is allowed
preconditions _ _ = Top

-- | Postconditions:
--
-- * Init
--
-- - Top
--
-- * Switch/Flush
--
--   They don't modify the mempool, so Top
--
-- * Adding transactions
--
-- - The transactions I gave were included/tried in increasing order
--
-- - The final accepted transactions must be valid wrt the last ledger state the
--   mempool was revalidated against.
--
-- - The newly added transactions must have ticket number greater than any
--   previous transaction and increasing.
--
-- - The new set of transactions must be a subset of the initial transactions \cup added txs
--
-- - Due to QSM trying all the interleavings, and not having switches
--   concurrently, there must be one in which the switch is performed, then
--   tryadd. In that case we can ensure that the transactions which are no
--   longer in the mempool and the ones that were rejected must fail in one
--   of the states. However we cannot not in which one they failed.
--
-- - If there are pending transactions, the set of included transctions must
--   saturate (or be over) the capacity
--
-- * Syncing with the ledger:
--
-- - The resulting transactions must be a subseteq of the initial transactions
--
-- - All removed transactions must fail in the new state. All kept transactions must succeed.
--
-- * Getting a snapshot:
--
-- - All transactions in the mempool must be returned.
--
-- * Getting a snapshot for a state:
--
-- - All returned transactions must succeed at the given state.
--
postconditions :: forall blk.
  ( LedgerSupportsMempool blk
  , Eq (GenTx blk)
  , Eq (LedgerTables (LedgerState blk) KeysMK)
  , Eq (TickedLedgerState blk DiffMK)
  , Eq (TxSeq.TxSeq (Validated (GenTx blk)))
  , Eq (Validated (GenTx blk))
  , Show (LedgerTables (LedgerState blk) KeysMK)
  , Show (TickedLedgerState blk DiffMK)
  )
  => LedgerConfig blk
  -> Model blk Concrete
  -> Action blk Concrete
  -> Response blk Concrete
  -> Logic
postconditions cfg model cmd resp = case model of
  NeedsInit -> case cmd of
    Init{} -> Top
    _ -> error $ "postconditions: non initialized model running something different to Init: " <> cmdName cmd
  Model{..} -> case (cmd, resp) of

    (Flush, _)                            -> Top

    (Switch{}, _)                         -> Top

    (GetSnapshot, Snapshot{..})           ->
      Annotate
        "The returned txs are all the txs in the model"
        (snapshotTxs snapshot_ .== modelTxs)

    (GetSnapshotFor{..}, SnapshotFor{..}) ->
      if modelIsUnsynced
      then Annotate
             "Snapshot must fail as model is unsynced"
             (Boolean . isNothing $ snapshotFor_)

      else case snapshotFor_ of
        Nothing -> Annotate "Snapshot failed and model was synced!" Bot
        Just snap ->
              Annotate
                "Transactions are a sublist of the ones in the model"
                ((isSublistOf `on` TxSeq.toList) (snapshotTxs snap) modelTxs)
          .&& Annotate
                "All returned transactions succesfully apply"
                ((./= []) $ snd $ txsApply (tick cfg $ NE.last snapshotChangelog) (map (txForgetValidated . TxSeq.txTicketTx) $ TxSeq.toList $ snapshotTxs snap))

    (SyncLedger, SyncOk{..})              ->
          Annotate
            "The tables used had all the values requested by the model txs"
            (let f :: ValuesMK k v -> KeysMK k v
                 f (ApplyValuesMK (DS.Values vals)) = ApplyKeysMK $ DS.Keys $ Map.keysSet vals
                 keysForCurrentTxs = foldl' (zipLedgerTables (<>)) polyEmptyLedgerTables [ getTransactionKeySets $ txForgetValidated $ TxSeq.txTicketTx t | t <- TxSeq.toList modelTxs]
             in mapLedgerTables f syncValuesUsed .== keysForCurrentTxs
            )
      .&& (let firstState = syncNewTip `withLedgerTablesTicked` syncValuesUsed
               newTxs = [ txForgetValidated $ TxSeq.txTicketTx t | t <- TxSeq.toList syncNewTxs ]
           in     Annotate
                    "Applying the new transactions gives back the same result"
                    (case txsApply firstState newTxs of
                        (ls, []) -> ls .== syncNewTip
                        _ -> Bot
                    )
              .&& Annotate
                    "Applying all the transactions gives back the same result, even rejected"
                    (let (ls, remain) =  txsApply firstState [ txForgetValidated $ TxSeq.txTicketTx t | t <- TxSeq.toList modelTxs ]
                      in ls .== syncNewTip .&& remain .== syncRemoveTxs_
                    )
          )
      .&& Annotate
            "Removed and new transactions are disjoint"
            (let newTxs = [ txForgetValidated $ TxSeq.txTicketTx t | t <- TxSeq.toList syncNewTxs ]
              in     newTxs ./= []
                 .&& syncRemoveTxs_ ./= []
                 .=>
                     forall newTxs (`notMember` syncRemoveTxs_)
                 .&& forall syncRemoveTxs_ (`notMember` newTxs)
            )
      .&& Annotate
            "New transactions are a subset of previous transactions, even tickets didn't change"
            (TxSeq.toList syncNewTxs `isSublistOf` TxSeq.toList modelTxs)
    (TryAddTxs{..}, RespTryAddTxs{..})    ->
          Annotate
            "Txs were processed in the same order as given"
            ((map (\case
                      MempoolTxAdded t -> txForgetValidated t
                      MempoolTxRejected t _ -> t) addTxsProcessed_ ++ addTxsPending_) .== txsToAdd)
      .&& Annotate
            "New txs have increasing ticket number and above old ones"
            (case catMaybes [ fmap TxSeq.txTicketNo $ find ((== tx) . TxSeq.txTicketTx) (TxSeq.toList modelTxs) | MempoolTxAdded tx <- addTxsProcessed_] of
               [] -> Top
               (tk1:tks) -> tk1 .> maximum [ TxSeq.txTicketNo t | t <- TxSeq.toList modelTxs]
                 .&& snd (foldl' (\(acc, val) t -> (t, val .&& t .> acc)) (tk1, Top) tks)
            )
      .&& Annotate
            "Resulting set of transactions is a subseteq of previous and the ones to add"
            (forall [ txForgetValidated . TxSeq.txTicketTx $ t | t <- TxSeq.toList addTxsCurrentTxs]
                    (`member` ([ txForgetValidated . TxSeq.txTicketTx $ t | t <- TxSeq.toList modelTxs] ++ txsToAdd)))
      .&& Annotate
            "If there are pending transactions it is because the mempool is full"
            (    addTxsPending_ ./= []
             .=>     sum [ TxSeq.txTicketTxSizeInBytes t | t <- TxSeq.toList modelTxs]
                 .>= getMempoolCapacityBytes (computeMempoolCapacity addTxsResult NoMempoolCapacityBytesOverride)
            )
      .&& Annotate "" Top


    _ -> error $ "postconditions: unexpected cmd " <> cmdName cmd

isSublistOf :: Eq a => [a] -> [a] -> Logic
isSublistOf []    _  = Top
isSublistOf (_:_) [] = Bot
isSublistOf xxs@(x:xs) (y:ys)
  | x == y = isSublistOf xs ys
  | otherwise = isSublistOf xxs ys

tick ::
  ( IsLedger (LedgerState blk)
  , TickedTableStuff (LedgerState blk)
  )
  => LedgerConfig blk
  -> LedgerState blk ValuesMK
  -> TickedLedgerState blk ValuesMK
tick cfg st = zipOverLedgerTablesTicked
                (flip rawApplyDiffs)
                (applyChainTick cfg (withOrigin undefined (+1) . pointSlot $ getTip st) (forgetLedgerTables st))
                (projectLedgerTables st)

txsApply ::
     TickedLedgerState blk ValuesMK
  -> [GenTx blk]
  -> (TickedLedgerState blk DiffMK, [GenTx blk])
txsApply = undefined -- fold txs

sm :: ( LedgerSupportsMempool TestBlock
      , LedgerSupportsProtocol TestBlock
      , HasTxId (GenTx TestBlock)
      , SufficientSerializationForAnyBackingStore (LedgerState TestBlock)
      , Eq (GenTx TestBlock)
      , Eq (TxSeq.TxSeq (Validated (GenTx TestBlock)))
      , Eq (TickedLedgerState TestBlock DiffMK)
      , Eq (LedgerTables (LedgerState TestBlock) KeysMK)
      )
   => LedgerConfig TestBlock
   -> StateMachine (Model TestBlock) (Action TestBlock) (ReaderT (IORef (Mempool IO TestBlock TicketNo, TestLedgerDB IO TestBlock)) IO) (Response TestBlock)
sm cfg =
  StateMachine
    initModel
    transitions
    preconditions
    (postconditions cfg)
    Nothing
    generator
    shrinker
    (semantics cfg)
    mock
    noCleanup

prop_mempoolParallel :: (
    LedgerSupportsMempool TestBlock
  , LedgerSupportsProtocol TestBlock
  , HasTxId (GenTx TestBlock)
  , SufficientSerializationForAnyBackingStore (LedgerState TestBlock)
  , Eq (TickedLedgerState TestBlock DiffMK)
  , Eq (LedgerTables (LedgerState TestBlock) KeysMK)
  )
  => Proxy TestBlock
  -> LedgerConfig TestBlock
  -> Property
prop_mempoolParallel _ lcfg = forAllParallelCommands (sm lcfg) Nothing $ \cmds ->
    monadic (\p   -> counterexample (treeDraw cmds) $ ioProperty $ do
                putStrLn $ treeDraw cmds
                ref <- newIORef undefined
                flip runReaderT ref p
            )
            (runParallelCommandsNTimes 100 (sm lcfg) cmds >>= prettyParallelCommands cmds)

treeDraw :: ParallelCommandsF Pair (Action TestBlock) (Response TestBlock) -> String
treeDraw (ParallelCommands prefix suffixes) =
  "\nTEST CASE\nPrefix\n" ++ (unlines $ map ('\t':) $ lines (tableString [def]
    unicodeRoundS
    def
    (map (\(Command c _ _) -> rowG [g c]) (unCommands prefix))
  )) ++ "\nParallel suffix\n" ++ (unlines $ map ('\t':) $ lines (tableString [def, def]
    unicodeRoundS
    def
    (map (\(Pair p1 p2) -> rowG [ f p1
                                , f p2]) suffixes)))

  where
    f (Commands cs) = intercalate "," $ map (\(Command c _ _) -> g c) cs
    g c = head $ words $ show c

prop_mempoolSequential :: (
    LedgerSupportsMempool TestBlock
  , LedgerSupportsProtocol TestBlock
  , HasTxId (GenTx TestBlock)
  , SufficientSerializationForAnyBackingStore (LedgerState TestBlock)
  , Eq (TxSeq.TxSeq (Validated (GenTx TestBlock)))
  , Eq (TickedLedgerState TestBlock DiffMK)
  , Eq (LedgerTables (LedgerState TestBlock) KeysMK)
  )
  => Proxy TestBlock
  -> LedgerConfig TestBlock
  -> Property
prop_mempoolSequential _ lcfg = forAllCommands (sm lcfg) Nothing $ \cmds ->
    monadic (\p   -> ioProperty $ do
                ref <- newIORef undefined
                flip runReaderT ref p
            )
    (do
        let sm' = sm lcfg
        (History hist, _model, res) <- runCommands sm' cmds
        case res of
          Ok -> pure ()
          _ -> do
            liftIO $ do
              print res
              putStrLn $ unlines [ head $ words $ show c | (_, Invocation c _)<- hist  ]
              error "STOP")

prop :: IO ()
prop = quickCheck $ prop_mempoolParallel (Proxy @TestBlock) (defaultEraParams (SecurityParam 2) (slotLengthFromSec 2))

prop' :: IO ()
prop' = quickCheck $ prop_mempoolSequential (Proxy @TestBlock) (defaultEraParams (SecurityParam 2) (slotLengthFromSec 2))

{-------------------------------------------------------------------------------
  Instances
-------------------------------------------------------------------------------}
instance NoThunks (TickedLedgerState TestBlock TrackingMK)

instance Eq (Validated (GenTx TestBlock)) where
  (==) = (==) `on` txForgetValidated

instance Eq (TxSeq.TxSeq (Validated (GenTx TestBlock))) where
  (==) = (==) `on` TxSeq.toList

instance Eq (LedgerState TestBlock mk) => Eq (TickedLedgerState TestBlock mk) where
  (TickedTestLedger l) == (TickedTestLedger r) = l == r

instance Eq (LedgerTables (LedgerState TestBlock) KeysMK) where
  a == b = head $ foldLedgerTables2 f a b
     where f :: Eq k => KeysMK k v -> KeysMK k v -> [Bool]
           f (ApplyKeysMK k1) (ApplyKeysMK k2) = [k1 == k2]

instance Show (MempoolChangelog TestBlock) where
  show (MempoolChangelog a _) = "MempoolChangelog " <> show a -- <> " " <> showsLedgerState sMapKind tbs ""
instance IsApplyMapKind mk => Show (TickedLedgerState TestBlock mk) where
  show (TickedTestLedger (TestLedger lap _) ) = unwords [
    "Ticked"
    , "LedgerState"
    , show lap
--    , showsLedgerState sMapKind (utxtoktables pds) ""
    ]

instance Arbitrary (GenTx TestBlock) where
  arbitrary = TestGenTx <$> (Tx <$> arbitrary <*> arbitrary) <*> fmap TestTxId arbitrary

instance Arbitrary (LedgerState TestBlock mk) => Arbitrary (TickedLedgerState TestBlock mk) where
  arbitrary = TickedTestLedger <$> arbitrary

type instance ApplyTxErr TestBlock = TxErr

instance HasTxId (GenTx TestBlock) where
  txId (TestGenTx _ t) = t

instance LedgerSupportsMempool TestBlock where
  applyTx _ _ _ (TestGenTx tx txid) (TickedTestLedger st@TestLedger{..}) =
    case applyPayload payloadDependentState tx of
        Left err  -> throwError err
        Right st' -> return     $ (,TestValidatedTx tx txid)
                                $ TickedTestLedger
                                $ st {
                                   payloadDependentState = st'
                                  }
  reapplyTx cfg s tx st = fmap fst $ applyTx cfg DoNotIntervene s (txForgetValidated tx) st
  txForgetValidated (TestValidatedTx tx txid) = TestGenTx tx txid

  getTransactionKeySets (TestGenTx tx _) = getPayloadKeySets tx
  txsMaxBytes = const 1
  txInBlockSize = const 1

data instance GenTx TestBlock = TestGenTx Tx (GenTxId TestBlock)
  deriving (Generic, NoThunks, Show, Eq)

data instance Validated (GenTx TestBlock) = TestValidatedTx Tx (GenTxId TestBlock)
  deriving (Generic, NoThunks, Show)

newtype instance TxId (GenTx TestBlock) = TestTxId Word
  deriving newtype (NoThunks, Show, Ord, Eq)

instance Show (PayloadDependentState Tx mk) where
  show = const "PDS"
