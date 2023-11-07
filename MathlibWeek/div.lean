import Mathlib.Algebra.Divisibility.Basic
theorem dvd_iff_exists_eq_mul_righty {α : Type u_1} [Semigroup α] {a : α} {b : α} :  a ∣ b ↔ ∃c, b = a*c := by
  constructor
  case mp s => intros adivb
               simp only [exists_eq_mul_left_of_dvd] at adivb
               apply adivb
  case mpr s => intros ec
                apply ec -- H must be a hypothesis or theorem with type P1 -> P2 -> ... -> PN -> Q, where the goal has type Q. This tactic (apply) will replace the goal with N separate goals, P1, through PN


theorem div_if_eq {α : Type u_1} [Monoid α] {a : α} {b : α} (h : a = b) : a ∣ b := by
  rw [h]