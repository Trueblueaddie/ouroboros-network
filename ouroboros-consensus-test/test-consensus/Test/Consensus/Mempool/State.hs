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

{-# OPTIONS_GHC -Wno-partial-fields -Wno-incomplete-record-updates -Wno-orphans #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Test.Consensus.Mempool.State (prop) where

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
  ParallelCommandsF(..), Command(..), Commands(..), Pair(..))

import Cardano.Slotting.Time

import Test.Consensus.Mempool.State.Model
import Test.Consensus.Mempool.State.SUT
import Test.Consensus.Mempool.State.Types
import Test.Consensus.Mempool.Block

import qualified Data.List.NonEmpty as NE
import qualified Data.Sequence.NonEmpty as NESeq
import Data.List (intercalate)
import Ouroboros.Network.Block (pointSlot)
import NoThunks.Class
import GHC.Generics (Generic)
import Test.Util.TestBlock hiding (TestBlock)
import Control.Monad.Except (throwError)
import Ouroboros.Consensus.HardFork.History (defaultEraParams)
import Ouroboros.Consensus.Config.SecurityParam (SecurityParam(..))
import Control.Monad (foldM)
import Data.Maybe (fromJust, isNothing, isJust)
import qualified Ouroboros.Consensus.Util.MonadSTM.RAWLock as RAWLock

import Text.Layout.Table
import Data.List.NonEmpty (NonEmpty)
import qualified Ouroboros.Consensus.Mempool.TxSeq as TxSeq
import qualified Data.Set as Set
import Data.Function (on)
import Data.Foldable
import qualified Ouroboros.Consensus.Storage.LedgerDB.HD.DiffSeq as DS
import qualified Data.Map.Strict as Map
import Debug.Trace

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
  ( Arbitrary (GenTx TestBlock)
  , TableStuff (LedgerState TestBlock)
  )
  => LedgerConfig TestBlock
  -> Model TestBlock Symbolic
  -> Maybe (Gen (Action TestBlock Symbolic))
generator lcfg = \case
  NeedsInit -> Just $ Init <$> initialState
  model     -> Just $ frequency $
   [ (2, fmap TryAddTxs $ listOf $ oneof
         [ arbitrary
         , TestGenTx <$> genSucceedingTransaction (NE.last (modelLedgerDB model)) <*> fmap TestTxId arbitrary
         ])
   , (1, pure GetSnapshot)
   , (1, do
         let anchorSt = NE.head $ modelLedgerDB model
             pds = anchorSt { payloadDependentState  = UTxTok (projectLedgerTables anchorSt) $ utxhist $ payloadDependentState anchorSt }
         valueChangelog <- genListOfStates pds
         let tip = NE.last valueChangelog
         let st = applyChainTick lcfg ((+1) . withOrigin' . pointSlot $ getTip tip) (forgetLedgerTables tip)
         pure $ GetSnapshotFor st $ NE.toList valueChangelog)
   , (1, do
         case modelNextSync model of
           Nothing -> do
             let anchorSt = NE.head $ modelLedgerDB model
             valueChangelog <- genListOfStates anchorSt
             UnsyncTip valueChangelog <$> arbitrary
           Just nldb -> do
             let anchorSt = NE.head nldb
             valueChangelog <- genListOfStates anchorSt
             UnsyncTip valueChangelog <$> arbitrary
     )
--   , (1, pure UnsyncAnchor)
   , (1, pure SyncLedger)
   ]

-- TODO: @js fill this shrinker
shrinker :: Model blk Symbolic -> Action blk Symbolic -> [Action blk Symbolic]
shrinker _ _ = []

preconditions :: Model blk Symbolic -> Action blk Symbolic -> Logic
-- When need init, only init
preconditions NeedsInit Init{} = Top
preconditions NeedsInit _      = Bot
-- Do not re-init
preconditions Model{}   Init{} = Bot
preconditions Model{}   _      = Top

-- TODO: @js Add postconditions
postconditions :: forall blk. ( LedgerSupportsMempool blk
                              , Eq (GenTx blk)
                              , GetTip (TickedLedgerState blk EmptyMK)) => Model blk Concrete -> Action blk Concrete -> Response blk Concrete -> Logic
postconditions (Model oldTxs oldSt _ oldLdb _ needSync) (TryAddTxs txs) (RespTryAddTxs resynced st _ added pending removed) = (txs ./= []) .=> (
      -- No transactions have gone missing
      forall txs     (flip member (map resultToTx added ++ pending))
      -- all removed transactions were present in the model
  .&& forall removed (`member` (map (txForgetValidated . TxSeq.txTicketTx) $ TxSeq.toList oldTxs))
      -- no removed transactions have been added again
  .&& (Boolean (not $ null added) .=> forall removed (`notMember` (map resultToTx added)))
      -- no added transactions were just removed
  .&& (Boolean (not $ null removed) .=> forall (map resultToTx added) (`notMember` removed))
      -- The state did not change if we didnt need to resync (only the slot could change)
  .&& case needSync of
        Nothing -> Annotate "No need to sync" $ (on (.==) (pointSlot . getTip))
                   (st    `withLedgerTablesTicked` polyEmptyLedgerTables)
                   (oldSt `withLedgerTablesTicked` polyEmptyLedgerTables @EmptyMK)
        Just nextSync ->
          if resynced
          then Annotate "Synced and changed state" $ (pointSlot $ getTip $ st               `withLedgerTablesTicked` polyEmptyLedgerTables @EmptyMK)
               .== (pointSlot $ getTip $ NE.last nextSync `withLedgerTables` polyEmptyLedgerTables @EmptyMK)
          else Annotate "Synced and not changed state" $ (on (.==) (pointSlot . getTip))
                   (st    `withLedgerTablesTicked` polyEmptyLedgerTables)
                   (oldSt `withLedgerTablesTicked` polyEmptyLedgerTables @EmptyMK)

      -- All the new diffs which are deletes are Consumed txins
  .&& head (foldLedgerTables2 areRequested
              (projectLedgerTablesTicked st)
              txIns)
      )
  where
    addedTxs = map resultToTx $ filter (\case
                                           MempoolTxAddedPlus{} -> True
                                           _ -> False ) added
    keptTxs =  [t' | t <- TxSeq.toList oldTxs, let t' = txForgetValidated $ TxSeq.txTicketTx t, t' `notElem` removed]

    txIns :: LedgerTables (LedgerState blk) KeysMK

    txIns = foldl' (zipLedgerTables (<>)) polyEmptyLedgerTables $ map getTransactionKeySets $ addedTxs ++ keptTxs
    areRequested :: (Eq k, Show k) => DiffMK k v -> KeysMK k v -> [Logic]
    areRequested (ApplyDiffMK (DS.Diff d)) (ApplyKeysMK (DS.Keys keys)) = forall (map (fst) $ Map.toList $ Map.filterWithKey filterDiffs d) (`member` (Set.toList keys)):[]

    filterDiffs k (DS.MkNEDiffHistory (DS.UnsafeDiffHistory ne)) = not $ null $ NESeq.filter (\case
                                                                         DS.Delete{} -> True
                                                                         _ -> False) ne

    forgetValues :: TrackingMK k v -> DiffMK k v
    forgetValues (ApplyTrackingMK _ d) = ApplyDiffMK d

postconditions _ _ _ = Top

sm :: ( LedgerSupportsMempool TestBlock
      , LedgerSupportsProtocol TestBlock
      , HasTxId (GenTx TestBlock)
      , SufficientSerializationForAnyBackingStore (LedgerState TestBlock)
      --  Can I use the test block with payload for this?
      , Eq (GenTx TestBlock)
      )
   => LedgerConfig TestBlock
   -> Bool
   -> StateMachine (Model TestBlock) (Action TestBlock) (ReaderT (IORef (Mempool IO TestBlock TicketNo, TestLedgerDB IO TestBlock, RAWLock.RAWLock IO ())) IO) (Response TestBlock)
sm cfg trc =
  StateMachine
    initModel
    (transitions cfg)
    preconditions
    postconditions
    Nothing
    (generator cfg)
    shrinker
    (semantics cfg trc)
    (mock cfg)
    noCleanup

prop_mempoolParallel :: ( LedgerSupportsMempool TestBlock
      , LedgerSupportsProtocol TestBlock
      , HasTxId (GenTx TestBlock)
      , SufficientSerializationForAnyBackingStore (LedgerState TestBlock)
      ) => Proxy TestBlock -> LedgerConfig TestBlock -> Bool -> Property
prop_mempoolParallel _ lcfg trc = forAllParallelCommands (sm lcfg trc) Nothing $ \cmds ->
    monadic (\p   -> counterexample (treeDraw cmds) $ ioProperty $ do
                putStrLn $ treeDraw cmds
                ref <- newIORef undefined
                flip runReaderT ref p
            )
            (runParallelCommandsNTimes 100 (sm lcfg trc) cmds >>= prettyParallelCommands cmds)

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
    g (UnsyncTip _ b) = (if b then "UnsyncAnchor," else "") <> "UnsyncTip"
    g c = head $ words $ show c

{-
prop_mempoolSequential :: ( LedgerSupportsMempool TestBlock
      , LedgerSupportsProtocol TestBlock
      , HasTxId (GenTx TestBlock)
      , SufficientSerializationForAnyBackingStore (LedgerState TestBlock)
      ) => Proxy TestBlock -> LedgerConfig TestBlock -> Bool -> Property
prop_mempoolSequential _ lcfg trc = forAllCommands (sm lcfg trc) Nothing $ \cmds ->
    monadic (\p   -> ioProperty $ do
                ref <- newIORef undefined
                flip runReaderT ref p
            )
    (do
        let sm' = sm lcfg trc
        (History hist, _model, res) <- runCommands sm' cmds
        case res of
          Ok -> pure ()
          _ -> do
            liftIO $ do
              print res
              putStrLn $ unlines [ head $ words $ show c | (_, Invocation c _)<- hist  ]
              error "STOP")
-}

prop :: Bool -> IO ()
prop = quickCheck . prop_mempoolParallel (Proxy @TestBlock) (defaultEraParams (SecurityParam 2) (slotLengthFromSec 2))

{-
prop' :: Bool -> IO ()
prop' = quickCheck . prop_mempoolSequential (Proxy @TestBlock) (defaultEraParams (SecurityParam 2) (slotLengthFromSec 2))
-}

instance NoThunks (TickedLedgerState TestBlock TrackingMK)

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

instance Show (ApplyTxErr TestBlock) => LedgerSupportsMempool TestBlock where
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
  deriving (Generic, NoThunks, Show, Ord, Eq)

instance Show (PayloadDependentState Tx mk) where
  show = const "PDS"
