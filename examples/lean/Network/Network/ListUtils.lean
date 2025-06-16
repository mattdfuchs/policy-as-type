import Network.Protocol
import Init.Data.List.Basic

namespace List

/-- Intersection of two lists with decidable membership. -/
def intersect {α : Type} [DecidableEq α] (xs ys : List α) : List α :=
  xs.filter fun x => x ∈ ys

end List

namespace Network

/-- Decidably check that two lists have empty intersection. -/
def emptyIntersection (xs ys : List Protocol) : Decidable (List.intersect xs ys = []) :=
by infer_instance

end Network
