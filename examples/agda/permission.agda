-- SPDX-License-Identifier: MIT
-- Copyright © 2025 Matthew Fuchs

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
open import Data.Sum using (_⊎_; inj₁; inj₂)
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
open import Data.List.Relation.Unary.Any using (Any ; here ; there)
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


{--

Here we start looking to validate a call to a service 

--}
record Pair (A B : Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B

-- Types of interest and their attribute names

record Location : Set where
  field
    name : String

record ItemRequest : Set where
  field
    name : String
    videoName : String
    ageLimit : ℕ

record Item : Set where
  field
    name : String
    ageLimit : ℕ

{-# NO_POSITIVITY_CHECK #-}
record User : Set where
  inductive
  field
    name : String
    age : ℕ
    parent : Maybe User
    grantsPermission : User → ItemRequest → Bool
    isParent : User → Bool

record Transport : Set where
  field
    name : String
    protocol : Protocol

record Context : Set where
  field
    name : String
    timeOfDay : ℕ

record Service : Set where
  field
    name : String
    isApproved : Bool    

data _≡U_ : Rel User (# 0) where
  *≡U* : ∀ ( p q : User ) → (User.name p) ≡ (User.name q) → p ≡U q

_≟U_ : (a : User) → (b : User) → Dec ( a ≡U b)
a ≟U b with (User.name a) Data.String.Properties.≟ (User.name b)
...       | yes y = yes (*≡U* a b y)
...       | no  n = no (nent n)
  where
    nent : ∀ {s t : User} → (User.name s) ≢ (User.name t) → ¬ (s ≡U t)
    nent neq (*≡U* s t ff) = ⊥-elim (neq ff)


{--

  For each of the parameters of a call, we need a property or dependent type describing correctness.  With each 
  such type, we need a function that takes an object of the type of that parameter and validates it against the proposition.
  Alternatively, it can take an arbitrary object of the type and return a potentially transformed object that is valid.

--}

data SafeContext : Context → Set where
  contextProp : (c : Context) → (Context.timeOfDay c) Data.Nat.Base.≤ 12 → SafeContext c

data HasPermission : (s : User) → (p : ItemRequest) → Set where
  *hp* : (s : User) → (p : ItemRequest) → (r : User) 
        → (User.isParent s r) ≡ Bool.true → ((User.grantsPermission r) s p) ≡ Bool.true 
        → HasPermission s p

data SafeSender : User → Set where
  senderPropOldEnough : (s : User) → (p : ItemRequest) 
                        → (ItemRequest.ageLimit p) Data.Nat.Base.≤ (User.age s) → SafeSender s
  senderPropYoung : (s : User) → (p : ItemRequest) → HasPermission s p → SafeSender s

data SafeChannel : Transport → Set where
  *isHttps* : (c : Transport) → (Transport.protocol c) ≡ https → SafeChannel c

data SafePayload : ItemRequest → Set where
  *safePayload* : (i : ItemRequest) → SafePayload i

data SafeService : Service → Set where
  *safeService* : (s : Service) → (Service.isApproved s) ≡ Bool.true → SafeService s

data SafeResponse : Item → Set where
  *safeResponse* : (r : ItemRequest) → (i : Item) → (ItemRequest.videoName r) ≡ (Item.name i) 
                   → SafeResponse i

checkContext : (c : Context) → Maybe (Σ[ c ∈ Context ] (SafeContext c))
checkContext c with (Context.timeOfDay c) Data.Nat.Properties.≤? 12
...              | no _ = nothing
...              | yes scnd = just (c , contextProp c scnd)

possiblePermission : (s : User) → (p : ItemRequest) → (r : User) → Maybe (HasPermission s p)
possiblePermission s p r = g
   where 
     g : Maybe (HasPermission s p)
     g with (((User.grantsPermission r) s p) ≟B Bool.true)
     ...             | no _ = nothing
     ...             | yes perm with (User.isParent s r) ≟B Bool.true
     ...                        | no _ = nothing
     ...                        | yes par = just (*hp* s p r par perm)

innerCheck : (s : User) → (p : ItemRequest)  → Maybe (Σ[ s ∈ User ] (SafeSender s))
innerCheck s p with (User.parent s)
...             | nothing = nothing
...             | just r with possiblePermission s p r 
...                        | nothing = nothing
...                        | just perm = just (s , senderPropYoung s p perm)

checkSender : (s : User) → ItemRequest → Maybe (Σ[ s ∈ User ] (SafeSender s))
checkSender s p with (ItemRequest.ageLimit p) Data.Nat.Properties.≤? (User.age s)
...               | no _ = innerCheck s p 
...               | yes second = just (s , senderPropOldEnough s p second)

checkChannel : (s : Transport) → Maybe (Σ[ s ∈ Transport ] (SafeChannel s))
checkChannel s with (Transport.protocol s) ≟P https
...             | yes p = just (s , *isHttps* s p)
...             | no _ = nothing

constrainPayload : (s : ItemRequest) → Maybe (Σ[ s ∈ ItemRequest ] (SafePayload s))
constrainPayload s = just (s , *safePayload* s)

checkService : (s : Service) → Maybe (Σ[ s ∈ Service ] (SafeService s))
checkService s with (Service.isApproved s) ≟B Bool.true
...            | no _ = nothing
...            | yes proof = just (s , *safeService* s proof)

constrainResponse : (s : Item) → (p : ItemRequest) → Maybe (Σ[ s ∈ Item ] (SafeResponse s))
constrainResponse s p with (ItemRequest.videoName p) ≟S (Item.name s)
...                  | no _ = nothing
...                  | yes proof = just (s , *safeResponse* p s proof)

response : Item
-- response = record { name = "I'm PG 13" ; ageLimit = 13 }

-- safeCall, because all the parameters are protected by a dependent pair
-- payload and response may not only be validated, but may also be transformed to something safer

safeCall : Σ[ c ∈ Context ] (SafeContext c) → 
           Σ[ u ∈ User ] (SafeSender u) → 
           Σ[ ch ∈ Transport ] (SafeChannel ch) → 
           Σ[ s ∈ ItemRequest ] (SafePayload s) →
           Σ[ s ∈ Service ] (SafeService s) →
           Maybe Item
safeCall context sender channel payload service = answer
 where 
    doCall : Transport → ItemRequest → Service → Maybe Item
    -- we don't really call anything here, just demo, so we return a fixed object
    doCall a b c = just response
    answer : Maybe Item
    answer with doCall (proj₁ channel) (proj₁ payload) (proj₁ service) 
    ...     | nothing = nothing
    ...     | just result with constrainResponse response (proj₁ payload)
    ...                     | nothing = nothing
    ...                     | just isGood = just (proj₁ isGood)

preCall : Context → User → Transport → ItemRequest → Service → Maybe Item
preCall   context  sender   channel  payload service with (checkContext context)
...    | nothing = nothing
...    | just safeContext with (checkSender sender payload)
...          | nothing = nothing
...          | just safeSender with (checkChannel channel)
...                 | nothing = nothing
...                 | just safeChannel with (constrainPayload payload)
...                       | nothing = nothing
...                       | just safePayload with (checkService service)
...                             | nothing = nothing
...                             | just safeService = safeCall safeContext safeSender safeChannel safePayload safeService

-- objects of the given types, instantiated with attributes, to prove things about

USAR : Location
USAR = record {name = "USA"}

payload : ItemRequest
payload = record { name = "Payload" ; videoName = "I'm PG 13"; ageLimit = 13 }

response = record { name = "I'm PG 13" ; ageLimit = 13 }

daddyPerm : User → ItemRequest → Bool
daddyPerm child item with (User.name child) ≟S "Sender"
...          | no _ = Bool.false
...          | y with (ItemRequest.videoName item) ≟S "I'm PG 13"
...                | no _ = Bool.false
...                | yes p = Bool.true
daddy : User
daddy = record { name = "Daddy" ; age = 40 ; parent = nothing ; 
                  grantsPermission = daddyPerm ; isParent = λ { _ → Bool.false }
  }

isParently : (a : User) → (b : User) → Bool
isParently a b with a ≟U b
...             | no _ = Bool.false
...             | yes _ = Bool.true

sender = record { name = "Sender" ; age = 13 ; parent = just daddy ; 
                  grantsPermission = λ { u i → Bool.false } 
                  ; isParent = λ { pq → isParently pq daddy }
  }

youngSender = record { name = "YoungSender" ; age = 10 ; parent = just daddy ;
                  grantsPermission = λ { u i → Bool.false } 
                  ; isParent = λ { pq → isParently pq daddy }
  }

channel : Transport
channel = record {name = "Channel" ; protocol = https }

context : Context
context = record { name = "Context" ; timeOfDay = 10 }

service : Service
service = record { name = "Foo" ; isApproved = Bool.true }

service2 : Service
service2 = record { name = "Foo" ; isApproved = Bool.false }

{--

    The following are the calls to the preCall function to validate whether a sender is
    authorized to call a service. In this case the service is a video, which might require the
    sender to be over a certain age, or have permission from a parent.   
    If it returns just item, then the call was safe and this is the response. If it returns nothing, 
    then the call was not safe, and so nothing is returned.

--}

tryOne = preCall context sender channel payload service
tryTwo = preCall context youngSender channel payload service
tryThree = preCall context daddy channel payload service
