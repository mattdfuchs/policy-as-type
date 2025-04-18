{-

Attribute based access control using Agda.

This is very simplified, as the first part of programming in Agda is negotiating your core concepts with the type system.

An important part of this negotiation is how much dependent information can be pushed to the types so things are visible
to the type system. 

Many infelicities may be due to my incomplete understanding of the typing system.

-}

open import Data.Nat.Base using (ℕ; zero; suc; _+_; _*_; _∸_;_^_; _≤_; z≤n; s≤s; _≡ᵇ_)
open import Data.Nat.Properties using (_≟_ ; _<?_)
open import Data.List.Base
open import Data.Empty
open import Data.Bool.Base using (if_then_else_ ; Bool; _∧_)
open import Relation.Binary.PropositionalEquality 
open import Data.Product.Base
open import Data.Maybe.Base
open import Data.Maybe.Properties
open import Data.String.Base
open import Data.String.Properties renaming (_≟_ to _≟S_; _<?_ to _<S?_)
open import Relation.Nullary.Decidable.Core 
open import Relation.Nullary.Reflects
open import Relation.Nullary.Negation.Core
open import Level using (0ℓ ; suc)
open import Relation.Binary.Core using ( REL )

-- The ubiquitous Pair type
record Pair (A B : Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B

-- We have a set of Entities. 
record Entity : Set

-- Each entity has an Attribute with some numeric value.  An Entity may need to know the value of that Attribute
data Attribute : Set where
    attr : (e : ℕ) → (v : ℕ) → Attribute

data StringAttribute : Set where
    stringAttr : (e : ℕ) → (v : String) → StringAttribute

-- An Entity may claim to know the value of that Attribute for some other Entity
data Claims : (server : ℕ) → (client : ℕ) → Set where
     claims : (server : ℕ) → (client : ℕ) → (attrib : Attribute) → Claims server client

-- function to generate a Claims from an authority about some entity.  The actual value is hidden in the list, so cannot
-- be exposed in the dependent type (at run time)
createClaim : List (Pair ℕ ℕ) → (auth : ℕ) → (client : ℕ) → Maybe (Claims auth client)
createClaim [] auth client = nothing
createClaim ((key , val) ∷ list) auth client with key ≟ client
...                           | yes _ = just (claims auth client (attr client val))
...                           | no  _ = createClaim list auth client

-- the value a Claims claims for the target Entity
claimValue : {a b : ℕ} → Claims a b → ℕ
claimValue {a} {b} (claims a b (attr _ c)) = c

-- But, if Entity A wants to know the value of the Attribute of Entity B, which it may not know, which Entity can it trust?
-- Each Entity Believes a particular set of other entities.
data Believes : ℕ → ℕ → Set where
    believes : (service : ℕ) → (auth : ℕ) → Believes service auth

-- each Entity will have a list of other Entities it believes.  We can if some service entity believes some authority entity
-- by just walking that list.
inList : (List ℕ) → (a : ℕ) → (b : ℕ) → (Maybe (Believes a b))
inList [] service auth =  nothing
inList (x ∷ accepted) service auth = if x ≡ᵇ auth then just (believes service auth) else (inList accepted service auth)

-- an Entity has the following:
record Entity  where
    inductive
    field
        -- a Nat as a name
        name : ℕ
        -- the list of other Entity names is trusts
        accepted : List ℕ
        -- as a potential authority, a list of pairs designating the attribute values it claims for some list of entities
        attributed : List (Pair ℕ ℕ)
        -- whether this entity Believes some authority.  We want the names of both believer and believed reflected in the
        -- type, so svc should be the same as name (but we don't seem to be able to state that here.
        acceptable : (svc : ℕ) → (auth : ℕ) → Maybe (Believes svc auth)
        -- at the request of another, a claim by this Entity as an authority about the value of the Attribute of some other Entity
        grantAttrib : (auth : ℕ) → (client : ℕ) → Maybe (Claims auth client)



-- helper function to create an Entity record.  User the inList and createClaim helper functions.
-- Note it only inlines the lists, although one would want to inline the name as well - but then 
-- it wouldn't be available to the compiler during type checking.
mkEntity : ℕ → List ℕ → List (Pair ℕ ℕ) → Entity
mkEntity a b c = record { 
    name = a ; 
    accepted = b ; 
    attributed = c ;
    acceptable = inList b ;
    -- needs to be rewritten to ensure the "auth" given matches name
    grantAttrib = createClaim c
  }

{-
  Entities : 1 2 3 4
  1 trusts 2 3
  2 trusts 3 4
  3 trusts no one
  4 trusts 1 2
-}
-- we make some Entities
e1 = mkEntity 1 (2 ∷ 3 ∷ []) ((1 , 4) ∷ (2 , 9) ∷ [])
e2 = mkEntity 2 (3 ∷ 4 ∷ []) ((1 , 50) ∷ (3 , 9) ∷ [])
e3 = mkEntity 3 [] []
e4 = mkEntity 4 (1 ∷ 2 ∷ []) ((1 , 0) ∷ (4 , 9) ∷ [])

-- We collect them in a list with their names
entityList : List (Pair ℕ Entity)
entityList = (1 , e1) ∷ (2 , e2) ∷ (3 , e3) ∷ (4 , e4) ∷ []

-- helper function to find an Entity given its name
findEntity : List (Pair ℕ Entity) → ℕ → Maybe Entity
findEntity [] index = nothing
findEntity ((key , value) ∷ l) index with key ≟ index 
...                                    | yes _ = just value
...                                    | no  _ = findEntity l index

-- an invocation of a service by a client is only valid if an authority trusted by the service claims that
-- the attribute value of the client validates some proposition
data Invocation : Set where 
    invoke : (client service : ℕ) → -- want to keep track of them in the Invocation object
             {authority : ℕ} → -- an authority trusted by the service
             {claim : Claims authority client} → -- a claim by that service about the client
             {trusts : Believes service authority} → -- evidence the service trusts the authority
             {claimValue claim Data.Nat.Base.< 40} → -- the proposition
             Invocation -- and the result

maybeCheck : {A : Set} → Maybe A → Bool
maybeCheck nothing = Bool.false
maybeCheck (just _) = Bool.true

-- an attempt to create an Invocation object, given all the above
-- returns nothing if there's a failure
validInvoke : ℕ → ℕ → ℕ → Maybe Invocation
validInvoke client service authority = 
    solution
   where
      cEnt = findEntity entityList client
      sEnt = findEntity entityList service
      aEnt = findEntity entityList authority
      -- get a claim about the attribute from the authority
      aClaim : Maybe (Claims authority client)
      aClaim with aEnt 
      ...         | nothing = nothing
      ...         | (just entity) with Entity.grantAttrib entity authority client
      ...                           | nothing = nothing
      ...                           | just aClaim = just aClaim
      -- see if the service believe the authority
      aBelief : Maybe (Believes service authority)
      aBelief with sEnt 
      ...         | nothing = nothing
      ...         | (just servEnt) with aEnt
      ...                          | nothing = nothing
      ...                          | (just authEnt) = Entity.acceptable servEnt service authority
      solution : Maybe Invocation
      solution with aClaim
      ...      | nothing = nothing
                 -- if we have an actual claim
      ...      | just theClaim with aBelief
      ...                       | nothing = nothing
                                  -- and the service believe the claim
                                  -- and the attribute passes the (Decidable) test
      ...                       | just theBelief with (claimValue theClaim) <? 40
      ...                                          | no _ = nothing
                                                     -- then there's proof and we can create an invocation
      ...                                          | yes P = just (invoke client service {authority} {theClaim} {theBelief} {P})

-- this fails because Entity 2 says the attribute value for Entity 1 is 50
failure = validInvoke 1 4 2 

-- the passes because Entity 1 says the attribute value for Entity 2 is 9
success = validInvoke 2 4 1