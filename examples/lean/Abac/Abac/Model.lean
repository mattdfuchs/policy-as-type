-- SPDX-License-Identifier: MIT
-- Copyright © 2025 Matthew Fuchs

import Abac.Protocol

open Protocol

open Classical

structure ItemRequest where
  name : String
  videoName : String
  ageLimit : Nat

structure Item where
  name : String
  ageLimit : Nat

structure Transport where
  name : String
  protocol : Protocol

structure Context where
  name : String
  timeOfDay : Nat

structure Service where
  name : String
  isApproved : Bool

structure User where
  name : String
  age : Nat
  parent : Option User

-- Optional: name-based equality
inductive UserEq : User → User → Prop
| mk : ∀ a b, a.name = b.name → UserEq a b

-- Safe dependent properties

inductive SafeContext : Context → Prop
| mk (c : Context) (h : c.timeOfDay ≤ 12) : SafeContext c

inductive SafeChannel : Transport → Prop
| httpsOnly {c} : c.protocol = https → SafeChannel c

inductive SafePayload (p : ItemRequest) : Prop
| mk : SafePayload p

inductive SafeService : Service → Prop
| mk (s : Service) : s.isApproved = true → SafeService s

inductive SafeResponse (r : ItemRequest) : Item → Prop
| mk (i : Item) : i.name = r.videoName → SafeResponse r i
