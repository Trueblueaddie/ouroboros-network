{-# LANGUAGE NamedFieldPuns #-}

module Ouroboros.Network.PeerSharing where

import           Control.Concurrent.Class.MonadSTM.Strict (MonadSTM, StrictTVar,
                     atomically, modifyTVar, newTVarIO)
import           Control.Monad.Class.MonadMVar (MVar,
                     MonadMVar (newEmptyMVar, putMVar), takeMVar)
import           Control.Monad.Class.MonadThrow (MonadThrow, bracket)
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import           Ouroboros.Network.Protocol.PeerSharing.Client
                     (PeerSharingClient (..))
import           Ouroboros.Network.Protocol.PeerSharing.Server
                     (PeerSharingServer (..))
import           Ouroboros.Network.Protocol.PeerSharing.Type (PeerSharingAmount)

-- | Request and Result queue for the peer sharing client implementation.
--
-- Although Peer Sharing is a request-response protocol we can not run it as
-- one, i.e. starting and terminating the protocol on demand since protocol
-- termination as a different semantics. We have to keep the client and server
-- protocol sides running and only issue the requests on demand.
--
-- A workaround to this is to implement the client side with the help of a
-- PeerSharingController which contains two queues: request and result.
-- The client side will be waiting to receive a 'PeerSharingAmount' from the
-- request queue and as soon as it gets something it will send a
-- 'SendMsgShareRequest' and wait for a response before writing it to the
-- result queue.
--
data PeerSharingController peer m = PeerSharingController {
  -- | Request queue of depth 1
  requestQueue :: MVar m PeerSharingAmount,
  -- | Result queue of depth 1
  resultQueue  :: MVar m [peer]
}

-- | Peer Sharing Registry is a registry that stores a 'PeerSharingController'
-- for every peer that we connect to.
--
-- 'bracketPeerSharingClient' should be used.
newtype PeerSharingRegistry peer m = PeerSharingRegistry {
  getPeerSharingRegistry :: StrictTVar m (Map peer (PeerSharingController peer m))
}

newPeerSharingRegistry :: (MonadSTM m, Ord peer) => m (PeerSharingRegistry peer m)
newPeerSharingRegistry = PeerSharingRegistry <$> newTVarIO mempty

bracketPeerSharingClient :: (Ord peer, MonadSTM m, MonadThrow m, MonadMVar m)
                         => PeerSharingRegistry peer m
                         -> peer
                         -> (PeerSharingController peer m -> m a) -> m a
bracketPeerSharingClient (PeerSharingRegistry registry) peer k = do
  -- Create new PeerSharingController
  newPSController <- PeerSharingController <$> newEmptyMVar <*> newEmptyMVar
  -- Add peer to registry with fresh controller. Call continuation with new
  -- controller. If something goes wrong, unregister peer.
  bracket (atomically (modifyTVar registry (Map.insert peer newPSController)))
          (\_ -> atomically (modifyTVar registry (Map.delete peer)))
          (\_ -> k newPSController)

peerSharingClient :: MonadMVar m => PeerSharingController peer m -> m (PeerSharingClient peer m ())
peerSharingClient psc@PeerSharingController { requestQueue, resultQueue } = do
  amount <- takeMVar requestQueue
  return $
    SendMsgShareRequest amount $ \result -> do
      putMVar resultQueue result
      peerSharingClient psc


peerSharingServer :: Monad m
                  => (PeerSharingAmount -> m [peer])
                  -> PeerSharingServer peer m ()
peerSharingServer computePeersToShare =
  PeerSharingServer
    { recvMsgShareRequest = \amount -> do
        peers <- computePeersToShare amount
        return (peers, peerSharingServer computePeersToShare),
      recvMsgDone = return ()
    }
