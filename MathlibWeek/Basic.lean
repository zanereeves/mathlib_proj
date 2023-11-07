import Mathlib.Algebra.Algebra.Hom
import Mathlib.Algebra.Divisibility.Basic
import Mathlib.Algebra.Algebra.Subalgebra.Basic

variable {R : Type u} {A : Type v} {B : Type w} {C : Type u₁} {D : Type v₁}


variable [CommSemiring R] [Semiring A] [Semiring B] [Semiring C] [Semiring D]

variable [Algebra R A] [Algebra R B] [Algebra R C] [Algebra R D]
#check AlgHom R A B -- I believe this is saying there exists a mapping from A to B within the commsemiring R
#check AlgHom R B C -- Same goes from B to C

-- We wish to show g(f(a)) = c, that is g ∘ f : A → C, h in effect (i believe) is saying there exists
theorem comp3 (h : A →ₐ[R] B) (h2 : B →ₐ[R] C) : A →ₐ[R] C :=
  {h2.toRingHom.comp ↑h with commutes' := fun r : R => by rw [← h2.commutes, ← h.commutes]; simp}

variable [CommSemiring X] [Semiring Y] [Semiring Z]
variable [Algebra X Y] [Algebra X Z]

#check algebraMap X Y

example (h : X →+* Y) : X →+* Y :=
  by assumption


theorem comp2 (h : X →+* Y) (h2 : Y →+* Z) : X →+* Z := by
  constructor
  case map_zero'  => simp -- Okay so for this step we would use the property of Semirings that they map to zero
                     simp only []

#check exists_eq_mul_right_of_dvd

-- theorem dvd_iff_exists_eq_mul_righty {α : Type u_1} [Semigroup α] {a : α} {b : α} :  a ∣ b ↔ ∃c, b = a*c := by
--   constructor
--   case mp h h1 h2 h3 h4 =>
