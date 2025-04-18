module RegoBase where

open import Data.Nat.Base using (ℕ; zero; suc; _+_; _*_; _∸_;_^_; _≤_; _>_ ; z≤n; s≤s; _≡ᵇ_)
open import Data.Nat.Properties using (_≟_ ; _<?_; ≡-decSetoid)
open import Data.List.Base
open import Data.Empty
open import Function
open import Data.Bool.Base using (if_then_else_ ; Bool; _∧_)
open import Data.Bool.Properties renaming (_≟_ to _≟B_)
open import Relation.Binary.PropositionalEquality.Core
open import Data.Product.Base
open import Data.Maybe.Base
open import Data.Maybe.Properties
open import Data.String.Base
open import Data.String.Properties renaming (_≟_ to _≟S_; _<?_ to _<S?_)
open import Relation.Nullary.Decidable.Core 
open import Relation.Nullary.Reflects
open import Relation.Nullary.Negation.Core
open import Level using (0ℓ ; suc)
open import Relation.Binary.Core using ( REL; Rel )
open import Relation.Binary.Bundles using (Setoid; DecSetoid)
open import Relation.Binary.Structures using (IsEquivalence; IsDecEquivalence)
open import Relation.Binary.PropositionalEquality using (refl; sym; trans; _≡_)
open import Level
open import Level.Literals

open import Data.List.Membership.DecSetoid using ( _∈?_ )
open import Data.List.Membership.Setoid using (_∈_)
open import Data.Unit.Polymorphic.Base
open import Relation.Unary using (Pred)

import Data.Fin.Base
import Data.Fin.Properties using (_≟_)

variable
  a ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ ℓ₆ : Level

data Protocol : Set₀ where
    https : Protocol
    ssh : Protocol
    mysql : Protocol
    memcache : Protocol
    http : Protocol
    telnet : Protocol

protoToNat : Protocol → ℕ
protoToNat https = 0
protoToNat ssh = 1
protoToNat mysql = 2
protoToNat memcache = 3
protoToNat http = 4
protoToNat telnet = 5

data _≡P2_ : Rel Protocol (# 0) where
  *≡P2* : ∀ { p q : Protocol} → (protoToNat p) ≡ (protoToNat q) → p ≡P2 q

_≟P2_ : (a : Protocol) → (b : Protocol) → Dec ( a ≡P2 b)
a ≟P2 b with (protoToNat a) Data.Nat.Properties.≟ (protoToNat b)
...       | yes y = yes (*≡P2* y)
...       | no  n = no (nent n)
  where
    nent : ∀ {s t : Protocol} → (protoToNat s) ≢ (protoToNat t) → ¬ (s ≡P2 t)
    nent neq (*≡P2* ff) = ⊥-elim (neq ff)

-- could map to string or Fin compares
_≟P_ : (p q : Protocol) → Dec (p ≡ q)
https ≟P https = yes refl
ssh ≟P ssh = yes refl
mysql ≟P mysql = yes refl
memcache ≟P memcache = yes refl
telnet ≟P telnet = yes refl
http ≟P http = yes refl
https ≟P ssh = no λ()
https ≟P mysql = no λ()
https ≟P memcache = no λ()
https ≟P http = no λ()
https ≟P telnet = no λ()
ssh ≟P https = no λ()
ssh ≟P mysql = no λ()
ssh ≟P memcache = no λ()
ssh ≟P  http = no λ()
ssh ≟P telnet = no λ()
mysql ≟P https = no λ()
mysql ≟P ssh = no λ()
mysql ≟P memcache = no λ()
mysql ≟P http = no λ()
mysql ≟P telnet = no λ()
memcache ≟P https = no λ()
memcache ≟P ssh = no λ()
memcache ≟P mysql = no λ()
memcache ≟P http = no λ()
memcache ≟P telnet = no λ()
http  ≟P https = no λ()
http ≟P  ssh = no λ()
http ≟P mysql = no λ()
http ≟P memcache = no λ()
http ≟P telnet = no λ()
telnet ≟P https = no λ()
telnet ≟P ssh = no λ()
telnet ≟P mysql = no λ()
telnet ≟P memcache = no λ()
telnet ≟P http = no λ()

isEquivalenceProt : IsEquivalence {A = Protocol} _≡_
isEquivalenceProt = record
  { refl  = refl
  ; sym   = sym
  ; trans = trans
  }

isDecEquivalenceProt : IsDecEquivalence _≡_
isDecEquivalenceProt = record
  { isEquivalence = isEquivalenceProt
  ; _≟_ = _≟P_
  }

protDecSetoid : DecSetoid 0ℓ  0ℓ
protDecSetoid = record
  { Carrier = Protocol
  ; _≈_ = _≡_
  ; isDecEquivalence = isDecEquivalenceProt
  }

-- Define the infix operator for list intersection
infixl 6 _∩_

_∩_ : List Protocol → List Protocol → List Protocol
xs ∩ ys = filter (λ x → _∈?_ protDecSetoid x ys) xs

-- Decidably prove that two lists have an empty intersection
emptyIntersection : ∀ (xs ys : List Protocol) → Dec (xs ∩ ys ≡ [])
emptyIntersection [] _ = yes refl
emptyIntersection (x ∷ xs) ys with _∈?_ protDecSetoid x ys
... | yes _ = no λ ()
... | no _  = emptyIntersection xs ys

data Network : Set where
    network : String → Bool → Network

data Port : Set where
    port : String → Network → Port

data Server : Set where
    server : String → List Protocol → List Port → Server

protocols : Server → List Protocol
protocols (server _ a _) = a

portList : Server → List Port
portList (server _ _ po) = po

-- Recreation of the Rego example

net1 = network "net1" Bool.false
net2 = network "net2" Bool.false
net3 = network "net3" Bool.true
net4 = network "net4" Bool.true

publicNetwork : Network → Bool
publicNetwork (network _ a) = a

getNetwork : Port → Network
getNetwork (port _ n) = n

p1 = port "p1" net1
p2 = port "p2" net3
p3 = port "p3" net2

app = server "app" (https ∷ ssh ∷ []) (p1 ∷ p2 ∷ p3 ∷ [])
db = server "db" (mysql ∷ []) (p3 ∷ [])
cache = server "cache" (memcache ∷ []) (p3 ∷ [])
ci = server "ci" (http ∷ []) (p1 ∷ p2 ∷ [])
busybox = server "busybox" (telnet ∷ []) (p1 ∷ [])

servers = app ∷ db ∷ cache ∷ ci ∷ busybox ∷ []
networks = net1 ∷ net2 ∷ net3 ∷ net4 ∷ []
ports = p1 ∷ p2 ∷ p3 ∷ []

badProtocols : List Protocol
badProtocols = (telnet ∷ [])

strongProtocols : List Protocol
strongProtocols = https ∷ ssh ∷ mysql ∷ memcache ∷ []

weakProtocols : List Protocol
weakProtocols = http ∷ []

data GoodProtos : Server → Set where
  *good* : (p : Server) → ((protocols p) ∩ badProtocols) ≡ [] → GoodProtos p

anyExposed : List Port → List Port
anyExposed somePorts = filterᵇ (λ {(port _ (network _ exp)) → exp}) somePorts

data PrivateServer : Server → Set where
  *private* : (s : Server) → (Data.List.Base.length (anyExposed (portList s))) ≡ 0 → PrivateServer s

negatePrivateServer : ∀ (s : Server) → { Data.List.Base.length (anyExposed (portList s)) ≢ 0 } → ¬ (PrivateServer s)
negatePrivateServer s { neq } (*private* _ p) = ⊥-elim (neq p)

isPrivate : (s : Server) → Dec (PrivateServer s)
isPrivate s with (Data.List.Base.length (anyExposed (portList s))) ≟ 0
...          | yes eq = yes (*private* s eq)
...          | no neq = no (nps neq)
   where
      nps : ∀ {s : Server} → Data.List.Base.length (anyExposed (portList s)) ≢ 0 → ¬ (PrivateServer s)
      nps neq (*private* _ p) = ⊥-elim (neq p)

data GoodServer : (s : Server) → Set where
  *goodserver* : ∀ (s : Server) → (GoodProtos s) → (PrivateServer s) → (GoodServer s)
  *safeserver* : ∀ (s : Server) → (GoodProtos s) → ¬ (PrivateServer s) → ((protocols s) ∩ weakProtocols ≡ []) → (GoodServer s)

goodServerCheck : (s : Server) → Maybe (Σ[ s ∈ (Server) ] (GoodServer s))
goodServerCheck s@(server _ protList portList) with (emptyIntersection protList badProtocols)
...           | no _ = nothing
...           | yes ei1 with isPrivate s
...                       | yes eqz = just (s , *goodserver* s (*good* s ei1) eqz)
...                       | no  gtz with (emptyIntersection protList weakProtocols)
...                                       | no _ = nothing
...                                       | yes ie2 = just (s , *safeserver* s (*good* s ei1) gtz ie2)

goof = goodServerCheck db
poof = goodServerCheck ci

boom : Σ[ s ∈ (Server) ] (GoodServer s)
boom = let foo = server "foo" (mysql ∷ []) (p3 ∷ []) in (foo , *goodserver* foo (*good* foo refl) (*private* foo refl))
bam = proj₁ boom
bust : Σ[ s ∈ (Server) ] (GoodServer s)
bust = (app , *safeserver* app (*good* app refl) (negatePrivateServer app { λ() }) refl)
pizl = proj₁ bust

goodServerList : List Server → List Server
goodServerList [] = []
goodServerList (h ∷ t) with goodServerCheck h
...                      | nothing = goodServerList t
...                      | just _  = h ∷ (goodServerList t)

badServerList : List Server → List Server
badServerList [] = []
badServerList (h ∷ t) with goodServerCheck h
...                      | just _ = badServerList t
...                      | nothing = h ∷ (badServerList t)
