import Mathlib.Data.Set.Lattice
import Mathlib.Data.Nat.Prime
import Mathlib.Tactic
import Mathlib.Data.Real.Basic

example (a b c : ℝ) : a * b * c = b * (a * c) :=
  by rw [mul_comm a b]
     rw [mul_assoc b a c]


example (a b c : ℝ) : c * b * a = b * (a * c) := by
   rw [mul_comm c b, mul_comm a c]
   rw [mul_assoc]

-- ring proves identitites in a commutative ring as long as they follow purely from ring axioms
example (a b c : ℝ) : c * b * a = b * (a * c) := by
  ring

-- nth_rw replaces the nth expression given a specific def.
example (a b c : ℕ) (h : a + b = c) : (a + b) * (a + b) = a * c + b * c := by
  nth_rw 2 [h]
  rw [add_mul]

-- Proving Identities in Algebraic Structures
-- The collection of ring objects is represented by a type R
variable (R : Type*) [Ring R]

#check (add_assoc : ∀ a b c : R, a + b + c = a + (b + c))
#check (add_comm : ∀ a b : R, a + b = b + a)
#check (zero_add : ∀ a : R, 0 + a = a)
#check (add_left_neg : ∀ a : R, -a + a = 0)
#check (mul_assoc : ∀ a b c : R, a * b * c = a * (b * c))
#check (mul_one : ∀ a : R, a * 1 = a)
#check (one_mul : ∀ a : R, 1 * a = a)
#check (mul_add : ∀ a b c : R, a * (b + c) = a * b + a * c)
#check (add_mul : ∀ a b c : R, (a + b) * c = a * c + b * c)


-- exercise
theorem add_neg_cancel_righty (a b : ℝ) : a + b + -b = a := by
 rw [add_assoc a b]
 rw [add_comm b (-b)]
 rw [add_left_neg, add_comm, zero_add]


variable (a b c : ℝ)

variable (h : a ≤ b) (h' : b ≤ c)

#check (le_refl : ∀ a : Real, a ≤ a)
#check (le_refl a : a ≤ a)
#check (le_trans : a ≤ b → b ≤ c → a ≤ c)
#check (le_trans h : b ≤ c → a ≤ c)
#check (le_trans h h' : a ≤ c)


example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z := by
  apply le_trans
  · apply h₀
  . apply h₁


#check (le_refl : ∀ a, a ≤ a)
#check (le_trans : a ≤ b → b ≤ c → a ≤ c)
#check (lt_of_le_of_lt : a ≤ b → b < c → a < c)
#check (lt_of_lt_of_le : a < b → b ≤ c → a < c)
#check (lt_trans : a < b → b < c → a < c)


-- Logic

#check ∀ x : ℝ , 0 ≤ x → |x| = x

-- exercise
theorem my_lemma : ∀ x y ε : ℝ, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε := by
  intro x y ε epos ele1 xlt ylt
  calc
    |x * y| = |x| * |y| := by rw [abs_mul]
    _ ≤ |x| * ε := by apply mul_le_mul
                      apply le_refl
                      apply le_of_lt
                      apply ylt
                      apply abs_nonneg
                      apply abs_nonneg
    |x| * ε < 1 * ε := (mul_lt_mul_right (c:= 1) epos).mpr (lt_of_le_of_lt' ele1 xlt)
    _ = ε := one_mul ε

-- Universal quantifiers

def FnUb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, f x ≤ a

def FnLb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀x, a ≤ f x

example (hfa : FnUb f a) (hgb : FnUb g b) : FnUb (fun x ↦ f x + g x) (a + b) := by
  intro x
  dsimp
  apply add_le_add
  apply hfa
  apply hgb

-- exercises
example (hfa : FnLb f a) (hgb : FnLb g b) : FnLb (fun x ↦ f x + g x) (a + b) := by
  intro x
  dsimp
  apply add_le_add
  apply hfa
  apply hgb

example (hfa : FnUb f a) (hgb : FnUb g b) (nng : FnLb g 0) (nna : 0 ≤ a) :
    FnUb (fun x ↦ f x * g x) (a*b) := by
  intro x
  dsimp
  apply mul_le_mul
  apply hfa
  apply hgb
  apply nng
  apply nna

example (f : ℝ → ℝ) (h : Monotone f) : ∀ {a b}, a ≤ b → f a ≤ f b :=
  @h

-- monotonicity
example (x : ℝ) (f g : ℝ → ℝ) (mf : Monotone f) (mg : Monotone g) : Monotone fun x ↦ f x + g x := by
  intro a b aleb
  apply add_le_add
  apply mf aleb
  apply mg aleb

def FnEven (f : ℝ → ℝ) : Prop :=
  ∀ x, f x = f (-x)

def FnOdd (f : ℝ → ℝ) : Prop :=
  ∀ x, f x = -f (-x)

example (ef : FnEven f) (eg : FnEven g) : FnEven fun x ↦ f x + g x := by
  intro x
  calc
    (fun x ↦ f x + g x) x = f x + g x := rfl
    _ = f (-x) + g (-x) := by rw [eg, ef]

-- exercises
example (of : FnOdd f) (og : FnOdd g) : FnEven fun x ↦ f x * g x := by
  intro x
  calc
    (fun x ↦ f x * g x) x = f x * g x := rfl
    _ = f (-x) * g (-x) := by rw [of, og]
                              simp

example (ef : FnEven f) (og : FnOdd g) : FnEven fun x ↦ f (g x) := by
  intro x
  calc
    (fun x ↦ f (g x)) x = f (g x) := rfl
    _ = f ( (g (-x))) := by rw [og, <-ef]


-- Set Theory
variable {α : Type*} (r s t : Set α)

example : s ⊆ s := by
  intro x xs
  exact xs

-- exercise
theorem Subset.trans : r ⊆ s → s ⊆ t → r ⊆ t := by
  intros r s a b
  exact s (r b)

variable {α : Type*} {β : Type*} {γ : Type*}

variable [PartialOrder α]
variable {s : Set α} (a b : α)

def SetUb (s : Set α) (a : α) :=
  ∀ x, x ∈ s → x ≤ a

-- exercise
example (h : SetUb s a) (h' : a ≤ b) : SetUb s b := by
  intros x s
  simp only [SetUb] at h
  have xys : x ≤ a := (h x) s
  exact le_trans xys h'


open Function

example (c : ℝ) : Injective fun x ↦ x + c := by
  intro x1 x2 h'
  exact (add_left_inj c).mp h'

-- exercise
example {c : ℝ} (h : c ≠ 0) : Injective fun x ↦ c * x := by
  intro x1 x2 h'
  simp at h'
  simp only [h] at h'
  simp at h'
  exact h'

variable {α : Type*} {R : Type*} [OrderedCancelAddCommMonoid R]

def FnUb' (f : α → R) (a : R) : Prop :=
  ∀x, f x ≤ a

def FnLb' (f : α → R) (a : R) : Prop :=
  ∀x, f x ≥ a

theorem fnUb_add {f g : α → R} {a b : R} (hfa : FnUb' f a) (hgb : FnUb' g b) :
  FnUb' (fun x ↦ f x + g x) (a + b) := fun x ↦ add_le_add (hfa x) (hgb x)

def FnHasUb (f : ℝ → ℝ) :=
  ∃a, FnUb f a


variable {f g : ℝ → ℝ}

example (ubf : FnHasUb f) (ubg : FnHasUb g) : FnHasUb fun x ↦ f x + g x := by
  rcases ubf with ⟨a, ubfa⟩
  rcases ubg with ⟨b,ubgb⟩
  use a + b
  apply fnUb_add ubfa ubgb

-- exercise

theorem fnLb_add {f g : α → R} {a b : R} (hfa : FnLb' f a) (hgb : FnLb' g b) :
  FnLb' (fun x ↦ f x + g x) (a + b) := fun x ↦ add_le_add (hfa x) (hgb x)

def FnHasLb (f : ℝ → ℝ) :=
  ∃a, FnLb f a

example (lbf : FnHasLb f) (lbg : FnHasLb g) : FnHasLb fun x ↦ f x + g x := by
  rcases lbf with ⟨a, lbfa⟩
  rcases lbg with ⟨b, lbgb⟩
  use a + b
  apply fnLb_add lbfa lbgb
