import Abac.Protocol
import Abac.Model

open Protocol
open User

-- Define permission logic here for simplicity
def grantsPermission (r : User) (s : User) (p : ItemRequest) : Bool :=
  if r.name = "Daddy" ∧ s.name = "Sender" ∧ p.videoName = "I'm PG 13" then true else false

def isParent (s r : User) : Bool :=
  s.name = r.name

-- HasPermission as a Prop
inductive HasPermission (s : User) (p : ItemRequest) : Prop where
| mk (r : User) :
    isParent s r = true →
    grantsPermission r s p = true →
    HasPermission s p

structure HasPermissionWitness (s : User) (p : ItemRequest) where
  r : User
  isPar : isParent s r = true
  granted : grantsPermission r s p = true

def HasPermissionWitness.toProp {s p} (w : HasPermissionWitness s p) : HasPermission s p :=
  HasPermission.mk w.r w.isPar w.granted

-- Decidable HasPermission
def possiblePermission (s : User) (p : ItemRequest) (r : User) : Option (HasPermissionWitness s p) :=
  if h₁ : isParent s r = true then
    if h₂ : grantsPermission r s p = true then
      some ⟨r, h₁, h₂⟩
    else none
  else none

-- Sender safety
inductive SafeSender : User → Prop where
| oldEnough (s : User) (p : ItemRequest) (h : p.ageLimit ≤ s.age) : SafeSender s
| withPerm (s : User) (p : ItemRequest) (hp : HasPermission s p) : SafeSender s

-- Subtype-friendly definitions

def checkContext (c : Context) : Option {c : Context // SafeContext c} :=
  if h : c.timeOfDay ≤ 12 then some ⟨c, SafeContext.mk c h⟩ else none

def innerCheck (s : User) (p : ItemRequest) : Option { u : User // SafeSender u } :=
  match s.parent with
  | none => none
  | some r =>
    match possiblePermission s p r with
    | some w => some ⟨s, SafeSender.withPerm s p (w.toProp)⟩
    | none => none

def checkSender (s : User) (p : ItemRequest) : Option {s : User // SafeSender s} :=
  if h : p.ageLimit ≤ s.age then
    some ⟨s, SafeSender.oldEnough s p h⟩
  else innerCheck s p

def checkChannel (c : Transport) : Option {t : Transport // SafeChannel t} :=
  if h : c.protocol = Protocol.https then some ⟨c, SafeChannel.httpsOnly h⟩ else none

def constrainPayload (p : ItemRequest) : Option {p : ItemRequest // SafePayload p} :=
  some ⟨p, SafePayload.mk⟩

def checkService (s : Service) : Option {s : Service // SafeService s} :=
  if h : s.isApproved = true then some ⟨s, SafeService.mk s h⟩ else none

def constrainResponse (i : Item) (r : ItemRequest) : Option {i : Item // SafeResponse r i} :=
  if h : i.name = r.videoName then some ⟨i, SafeResponse.mk i h⟩ else none

def doCall (_ : Transport) (_ : ItemRequest) (_ : Service) : Option Item :=
  some { name := "I'm PG 13", ageLimit := 13 }

def safeCall (ctx : {c : Context // SafeContext c})
             (snd : {u : User // SafeSender u})
             (chl : {c : Transport // SafeChannel c})
             (pld : {p : ItemRequest // SafePayload p})
             (srv : {s : Service // SafeService s}) : Option Item :=
  match doCall chl.1 pld.1 srv.1 with
  | none => none
  | some result =>
    match constrainResponse result pld.1 with
    | some ⟨item, _⟩ => some item
    | none => none

def preCall (c : Context) (u : User) (ch : Transport) (p : ItemRequest) (s : Service) : Option Item :=
  match checkContext c, checkSender u p, checkChannel ch, constrainPayload p, checkService s with
  | some ctx, some snd, some chl, some pld, some srv =>
    safeCall ctx snd chl pld srv
  | _, _, _, _, _ => none
