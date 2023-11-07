import Mathlib.Data.Set.Lattice
import Mathlib.Tactic
import Mathlib.Data.Nat.Prime
import Mathlib.Data.Nat.Parity

variable {α : Type*}
open Set

#check 1
variable (s t u : Set α)
example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u :=
  by
  rw [subset_def]
