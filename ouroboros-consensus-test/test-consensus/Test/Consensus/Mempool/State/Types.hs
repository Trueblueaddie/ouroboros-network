{-# LANGUAGE DeriveAnyClass       #-}
{-# LANGUAGE DeriveGeneric        #-}
{-# LANGUAGE DerivingStrategies   #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE PolyKinds            #-}
{-# LANGUAGE StandaloneDeriving   #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -Wno-partial-fields #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE GADTs #-}

module Test.Consensus.Mempool.State.Types (
    -- * Actions
    Action (..)
  , Response (..)
    -- * Model
  , MempoolAddTxResultPlus (..)
  , resultToTx
  , MockLedgerDB
  , Model (..)
  , initModel
    -- * Helpers
  , withOrigin'
  ) where

import           Data.Kind
import           Data.List.NonEmpty (NonEmpty)
import           GHC.Generics
import           GHC.Stack (HasCallStack)

import           Cardano.Slotting.Slot

import           Ouroboros.Consensus.Ledger.Basics
import           Ouroboros.Consensus.Ledger.SupportsMempool
import           Ouroboros.Consensus.Mempool
import           Ouroboros.Consensus.Mempool.TxSeq (TxSeq)
import qualified Ouroboros.Consensus.Mempool.TxSeq as TxSeq

import           Test.StateMachine
import qualified Test.StateMachine.Types.Rank2 as Rank2
import qualified Data.List.NonEmpty as NE

{-------------------------------------------------------------------------------
  Actions
-------------------------------------------------------------------------------}

type Action :: Type -> (Type -> Type) -> Type
data Action blk r
    -- | Initialize the mempool and mock ledger DB with this state
  = Init {
      -- | The initial state that will be the first block in the LedgerDB.
      -- Models what was loaded from a snapshot when starting the node.
      stateForInit :: !(LedgerState blk ValuesMK) }

    -- | Try to add the given transactions into the mempool
  | TryAddTxs {
      -- | A list of transactions to add.
      txsToAdd :: ![GenTx blk] }

    -- | Perform a sync with the mock ledger DB
  | SyncLedger

    -- | Request a snapshot to the current mempool
  | GetSnapshot

    -- | Request a snapshot for a specific ledger state
  | GetSnapshotFor
      {
      -- | The previous states as the SUT requires a mempool changelog.
      snapshotChangelog :: !(NonEmpty (LedgerState blk ValuesMK))
      }

    -- | Make the ledger go out of sync with the mempool by giving a new fork
    --
    -- This means @switchToFork@
  | Switch ![LedgerState blk ValuesMK]

    -- | Flush one state to the disk.
  | Flush

  deriving stock Generic1
  deriving anyclass (Rank2.Functor, Rank2.Foldable, Rank2.Traversable)

instance CommandNames (Action blk) where
  cmdName Init{}           = "Init"
  cmdName TryAddTxs{}      = "TryAddTxs"
  cmdName SyncLedger{}     = "SyncLedger"
  cmdName GetSnapshot{}    = "GetSnapshot"
  cmdName GetSnapshotFor{} = "GetSnapshotFor"
  cmdName Switch{}         = "Switch"
  cmdName Flush{}          = "Flush"

  cmdNames _ = [ "Init"
               , "TryAddTxs"
               , "SyncLedger"
               , "GetSnapshot"
               , "GetSnapshotFor"
               , "Switch"
               , "Flush"
               ]

instance ( Show (LedgerState blk EmptyMK)
         , Show (TickedLedgerState blk TrackingMK)
         , Show (LedgerState blk ValuesMK)
         , Show (TickedLedgerState blk EmptyMK)
         , Show (GenTx blk)
         , Show (LedgerTables (LedgerState blk) DiffMK)
         , Show (MempoolChangelog blk)
         ) => Show (Action blk r) where
  show x = case x of
    Init ls             -> "Init " <> show ls
    TryAddTxs gts       -> "TryAddTxs [" <> show (length gts) <> " txs]"
    SyncLedger          -> "SyncLedger"
    GetSnapshot         -> "GetSnapshot"
    GetSnapshotFor _ -> "GetSnapshotFor "
    Flush               -> "Flush"
    Switch sts          -> "Switch to ["
                           <> (maybe "Empty" (\ne -> show (NE.head ne)
                                                     <> ", "
                                                     <> show (length ne - 2)
                                                     <> " states, "
                                                     <> show (NE.last ne)) . NE.nonEmpty) sts
                           <> "] "


{-------------------------------------------------------------------------------
  Response
-------------------------------------------------------------------------------}

data MempoolAddTxResultPlus blk =
    MempoolTxAddedPlus    !(TxSeq.TxTicket (Validated (GenTx blk)))
  | MempoolTxRejectedPlus !(GenTx blk)

resultToTx :: LedgerSupportsMempool blk => MempoolAddTxResultPlus blk -> GenTx blk
resultToTx (MempoolTxAddedPlus t)    = txForgetValidated $ TxSeq.txTicketTx t
resultToTx (MempoolTxRejectedPlus t) = t

deriving instance ( Show (Validated (GenTx blk))
                  , Show (GenTx blk)
                  ) => Show (MempoolAddTxResultPlus blk)

type Response :: Type -> (Type -> Type) -> Type
data Response blk r
 = -- | There's nothing to tell
    ResponseOk

  | -- | Transactions were pushed onto the mempool
    RespTryAddTxs {

        -- | The resulting ledger state after the transactions (and ticking if a
        -- resync was needed)
        addTxsResult :: !(TickedLedgerState blk DiffMK)

      , addTxsUsedValues :: !(LedgerTables (LedgerState blk) ValuesMK)

      , -- | The list of results of processing the transactions Notice that the
        -- system gathers these while executing each transaction. It can be the
        -- case that a transaction is added, then the mempool is revalidated and
        -- that same transaction is removed, so we must not blindly assume that
        -- this transaction was in fact added to the mempool.
        addTxsProcessed_ :: ![MempoolAddTxResult blk]

      , -- | The transactions that were not included because the mempool was full
        addTxsPending_ :: ![GenTx blk]

      , addTxsCurrentTxs :: !(TxSeq.TxSeq (Validated (GenTx blk)))
      }

  | -- | A Sync with a new state was performed
    SyncOk {
          syncValuesUsed :: !(LedgerTables (LedgerState blk) ValuesMK)
        , syncNewTip     :: !(TickedLedgerState blk DiffMK)
        , syncNewTxs     :: !(TxSeq.TxSeq (Validated (GenTx blk)))
        , syncRemoveTxs_ :: ![GenTx blk]
        }

  | -- | A snapshot was taken
    Snapshot {
        -- | The transactions in the snapshot
        snapshot_ :: !(MempoolSnapshot blk TicketNo)
      }

  | -- | A snapshot for a specific state was requested
    SnapshotFor {
      -- | Nothing if the query fails, otherwise the list of valid transactions
      -- for the given ledger state
      snapshotFor_ :: !(Maybe (MempoolSnapshot blk TicketNo))
      }

  deriving stock (Generic1)
  deriving anyclass Rank2.Foldable

instance ( Show (Validated (GenTx blk))
                  , Show (GenTx blk)
                  , Show (TickedLedgerState blk DiffMK)
                  , Show (TickedLedgerState blk ValuesMK)
                  , Show (LedgerState blk ValuesMK)
                  ) => Show (Response blk r) where
  show ResponseOk = "ResponseOk"
  show (RespTryAddTxs st _ processed pending _) = "RespTryAdd " <> show st <> ", txs proc:pen:removed " <> show (length processed, length pending)
  show (SyncOk _ st _ removed) = "SyncOk " <> show st <> " txs removed: " <> show (length removed)
  show (Snapshot _) = "Snapshot"
  show (SnapshotFor _) = "SnapshotFor"

{-------------------------------------------------------------------------------
  Model
-------------------------------------------------------------------------------}

-- | Mock a minimal LedgerDB for the model
--
-- This mock contains both the tip state and the sequence of slot x tables that
-- are represented by the db changelog. In particular, the list of tables has to
-- be sorted and the last one corresponds to the values for the tip. It is as if
-- we applied each table of differences to the backing store values.
--
-- Invariants:
--
--  * fst (NE.last mockTables) = slot mockTip
--
--  * sorted (NE.map fst mockTables)
type MockLedgerDB blk          = NonEmpty (LedgerState blk ValuesMK)

type Model :: Type -> (Type -> Type) -> Type
data Model blk r where
  -- | The model is yet to be initialized
  NeedsInit :: Model blk r
  -- | The model is initialized
  Model :: {

      -- | The current sequence of validated transactions
      modelTxs       :: !(TxSeq (Validated (GenTx blk)))

      -- | Was the last command an Unsync? makes sure that we don't run unsyncs
      -- in parallel. Intended to be used /ONLY/ during command generation
    , modelIsUnsyncing :: !Bool

    , modelIsUnsynced :: !Bool

    , modelState      :: !(NonEmpty (LedgerState blk ValuesMK))

    } -> Model blk r
  deriving Generic

deriving instance ( Eq (TickedLedgerState blk ValuesMK)
                  , Eq (LedgerState blk ValuesMK)
                  , Eq (TxSeq (Validated (GenTx blk)))
                  ) => Eq (Model blk r)
deriving instance ( Show (TickedLedgerState blk ValuesMK)
                  , Show (LedgerState blk ValuesMK)
                  , Show (Validated (GenTx blk))
                  ) => Show (Model blk r)

initModel :: Model blk r
initModel = NeedsInit

{-------------------------------------------------------------------------------
  Helpers
-------------------------------------------------------------------------------}

withOrigin' :: HasCallStack => WithOrigin b -> b
withOrigin' = withOrigin (error "unexpected origin") id
