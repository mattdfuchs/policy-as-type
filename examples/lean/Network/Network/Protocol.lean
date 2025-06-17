-- SPDX-License-Identifier: MIT
-- Copyright © 2025 Matthew Fuchs
namespace Network

inductive Protocol where
  | https
  | ssh
  | mysql
  | memcache
  | http
  | telnet
deriving DecidableEq, Repr, Inhabited

/-- Map a protocol to its numeric code. -/
def protoToNat : Protocol → Nat
  | .https    => 0
  | .ssh      => 1
  | .mysql    => 2
  | .memcache => 3
  | .http     => 4
  | .telnet   => 5

end Network
