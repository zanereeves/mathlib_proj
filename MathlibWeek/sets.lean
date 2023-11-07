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
  rw [subset_def, inter_def, inter_def]
  rw [subset_def] at h
  rintro x ⟨xs, xu⟩ -- deconstruct our goal
  exact ⟨h _ xs, xu⟩ -- the brackets tell lean to use whatever constructor is nec to acc goal

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  intro x xsu
  exact ⟨h xsu.1, xsu.2⟩

example : s ∩ (t ∪ u) ⊆ s ∩ t ∪ s ∩ u := by
  intro x hx
  have xs : x ∈ s := hx.1 -- have proves a sub-hyp
  have xtu : x ∈ t ∪ u := hx.2
  rcases xtu with xt | xu -- with means we will prove our cases using only the given hyp
  · left
    exact ⟨xs, xt⟩
  · right
    exact ⟨xs, xu⟩


-- book exercise
example : s ∩ t ∪ s ∩ u ⊆ s ∩ (t ∪ u) := by
  intro x hx
  rcases hx with (⟨xs, xt⟩ | ⟨xs, xu⟩)
  constructor
  exact xs
  constructor
  exact xt
  constructor
  exact xs
  case inr.intro.right => simp
                          simp only [xu]
                          simp




example : (s \ t) \ u ⊆ s \ (t ∪ u) := by -- x ∈ s ∧ x ∉ t
  intro x xstu
  have xs : x ∈ s := xstu.left.1
  have xnt : x ∉ t := xstu.1.2
  have xnu : x ∉ u := xstu.2
  constructor
  · exact xs
  intro xtu
  -- x ∈ t ∨ x ∈ u
  rcases xtu with xt | xu
  · show False; exact xnt xt
  . show False; exact xnu xu
