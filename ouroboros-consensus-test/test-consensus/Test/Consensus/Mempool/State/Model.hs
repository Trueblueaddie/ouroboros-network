{-# LANGUAGE RecordWildCards  #-}

module Test.Consensus.Mempool.State.Model (transitions, mock) where

import qualified Ouroboros.Consensus.Mempool.TxSeq as TxSeq

import           Test.StateMachine

import           Test.Consensus.Mempool.State.Types
import qualified Data.List.NonEmpty as NE

{-------------------------------------------------------------------------------
  Model transition
-------------------------------------------------------------------------------}
transitions :: Model blk r
            -> Action blk r
            -> Response blk r
            -> Model blk r
transitions model cmd resp = case model of
    NeedsInit -> case (cmd, resp) of
      (Init st, ResponseOk) -> Model TxSeq.Empty False False (st NE.:| [])

      _ -> error "transitions: Model is not initialized"

    Model{..} -> case (cmd, resp) of
      (GetSnapshot, _)         -> Model { modelIsUnsyncing = False, .. }
      (GetSnapshotFor{}, _)    -> Model { modelIsUnsyncing = False, .. }
      (SyncLedger, SyncOk{..}) ->
        Model { modelTxs         = syncNewTxs
              , modelIsUnsyncing = False
              , modelIsUnsynced  = False
              , ..
              }

      (TryAddTxs{}, RespTryAddTxs{..}) ->
        Model { modelTxs         = addTxsCurrentTxs
              , modelIsUnsyncing = False
              , modelIsUnsynced  = False
              , ..
              }

      (Flush, _) ->
        Model { modelIsUnsyncing = True
              , modelIsUnsynced  = False -- TODO @js is this False or true?
              , modelState       = maybe modelState id $ NE.nonEmpty $ NE.tail modelState
              , ..
              }
      (Switch sts, _) ->
        Model { modelIsUnsyncing = True
              , modelIsUnsynced  = True
              , modelState       = maybe modelState id $ NE.nonEmpty sts
              , ..
              }

      (Init{}, _) -> error "transitions: Model re-initialized"

      _           -> error $ "transitions: unexpected command "
                          <> cmdName cmd
                          <> " with unexpected response"

mock :: Model blk Symbolic
     -> Action blk Symbolic
     -> GenSym (Response blk Symbolic)
mock _ _ = pure ResponseOk
