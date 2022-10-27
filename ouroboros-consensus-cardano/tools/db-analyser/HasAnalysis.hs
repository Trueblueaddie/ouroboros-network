{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies     #-}

module HasAnalysis (
    HasAnalysis (..)
  , HasProtocolInfo (..)
  , SizeInBytes
  , WithLedgerState (..)
  ) where

import           Data.Map.Strict (Map)
import           Options.Applicative

import           Ouroboros.Consensus.Block
import           Ouroboros.Consensus.HeaderValidation (HasAnnTip (..))
import           Ouroboros.Consensus.Ledger.Abstract
import           Ouroboros.Consensus.Node.ProtocolInfo
import           Ouroboros.Consensus.Storage.Serialisation (SizeInBytes)
import           Ouroboros.Consensus.Util.Condense (Condense)

{-------------------------------------------------------------------------------
  HasAnalysis
-------------------------------------------------------------------------------}

data WithLedgerState blk = WithLedgerState
  { wlsBlk         :: blk
  , wlsStateBefore :: LedgerState blk
  , wlsStateAfter  :: LedgerState blk
  }

class (HasAnnTip blk, GetPrevHash blk, Condense (HeaderHash blk)) => HasAnalysis blk where

  countTxOutputs :: blk -> Int
  blockTxSizes   :: blk -> [SizeInBytes]
  knownEBBs      :: proxy blk -> Map (HeaderHash blk) (ChainHash blk)

  -- | Emit trace markers at points in processing.
  emitTraces     :: WithLedgerState blk -> [String]

  -- | This method was introduced for the sake of the 'BenchmarkLedgerOps' pass.
  blockStats     :: blk -> [String]

class HasProtocolInfo blk where
  data Args blk
  argsParser     :: proxy blk -> Parser (Args blk)
  mkProtocolInfo :: Args blk -> IO (ProtocolInfo IO blk)
