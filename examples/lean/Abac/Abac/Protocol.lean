inductive Protocol
| https | ssh | mysql | memcache | http | telnet
deriving DecidableEq

open Protocol

def protoToNat : Protocol → Nat
| https    => 0
| ssh      => 1
| mysql    => 2
| memcache => 3
| http     => 4
| telnet   => 5

inductive ProtocolEq : Protocol → Protocol → Prop
| mk : ∀ {p q}, protoToNat p = protoToNat q → ProtocolEq p q

def ProtocolEq.decidable : DecidableRel ProtocolEq :=
  fun p q =>
    if h : protoToNat p = protoToNat q then
      isTrue (ProtocolEq.mk h)
    else
      isFalse (fun | ProtocolEq.mk h' => h h')

-- Boolean equality using pattern matching (alternative to ProtocolEq)
def Protocol.beq : Protocol → Protocol → Bool
| https, https => true
| ssh, ssh => true
| mysql, mysql => true
| memcache, memcache => true
| http, http => true
| telnet, telnet => true
| _, _ => false
