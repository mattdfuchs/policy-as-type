import Std
import Init.Data.Nat.Basic

import Network.Protocol
import Network.ListUtils
import Network.Types

namespace Network

/-- Protocol classifications. -/
 def badProtocols    : List Protocol := [.telnet]
 def weakProtocols   : List Protocol := [.http]
 def strongProtocols : List Protocol := [.https, .ssh, .mysql, .memcache]

/-- A server has no bad protocols. -/
 def GoodProtos (s : Server) : Prop :=
   s.protocols.intersect badProtocols = []

/-- Filter ports exposed to public networks. -/
 def anyExposed (ps : List Port) : List Port :=
   ps.filter fun p => p.network.public

/-- A server has no exposed ports. -/
 def PrivateServer (s : Server) : Prop :=
   (anyExposed s.ports).length = 0

/-- Decidable test for `PrivateServer`. -/
def isPrivate (s : Server) : Decidable (PrivateServer s) :=
  Nat.decEq (anyExposed s.ports).length 0

/-- Good servers: either private or safe (no weak protocols). -/
 inductive GoodServer (s : Server) : Type where
   | goodserver (h₁ : GoodProtos s) (h₂ : PrivateServer s) : GoodServer s
   | safeserver (h₁ : GoodProtos s) (h₃ : ¬ PrivateServer s)
                (h₄ : s.protocols.intersect weakProtocols = []) : GoodServer s

/-- Attempt to build a proof of goodness for a server. -/
 def goodServerCheck (s : Server) : Option (Sigma fun t => GoodServer t) :=
   match emptyIntersection s.protocols badProtocols with
   | isTrue h₁ =>
     match isPrivate s with
     | isTrue h₂  => some (Sigma.mk s (GoodServer.goodserver h₁ h₂))
     | isFalse hn =>
       match emptyIntersection s.protocols weakProtocols with
       | isTrue h₃ => some (Sigma.mk s (GoodServer.safeserver h₁ hn h₃))
       | isFalse _ => none
   | isFalse _ => none

/-- Filter a list of servers, returning only the good ones. -/
 def goodServerList (ss : List Server) : List Server :=
   ss.filterMap fun s => (goodServerCheck s).map fun ⟨t,_⟩ => t

/-- Filter a list of servers, returning only the bad ones. -/
 def badServerList (ss : List Server) : List Server :=
   ss.filter fun s => (goodServerCheck s).isNone

end Network
