import Init.Data.List.Basic
import Std
import Network.Protocol

namespace Network

/-- A network with a name and public flag. -/
structure Network where
  name   : String
  public : Bool
deriving Repr, Inhabited

/-- A port attached to a network. -/
structure Port where
  name    : String
  network : Network
deriving Repr, Inhabited

/-- A server with protocols and ports. -/
structure Server where
  name      : String
  protocols : List Protocol
  ports     : List Port
deriving Repr, Inhabited

end Network
