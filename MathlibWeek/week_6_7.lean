import Mathlib.Data.Set.Lattice
import Mathlib.Data.Nat.Prime
import Mathlib.Data.Nat.Parity
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mathlib.Algebra.Category.GroupCat.Basic

#check ∀ x : ℝ, 0 ≤ x → |x| = x

#check ∀ x y ε : ℝ, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x*y| < ε

variable {a : Type*}
variable { s t u : Set α }
open Set

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  rw [subset_def, inter_def, inter_def]
  rw [subset_def] at h
  simp only [mem_setOf]
  rintro x ⟨xs, xu⟩
  exact ⟨h x xs, xu⟩

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  intro x xsu
  exact ⟨h xsu.1, xsu.2⟩


example : (s \ t) \ u ⊆ s \ (t ∪ u) := by
  intro x xstu
  have xs : x ∈ s := xstu.1.1
  have xnt : x ∉ t := xstu.1.2
  have xnu : x ∉ u := xstu.2
  constructor
  · exact xs
  intro xtu
  -- x ∈ t ∨ x ∈ u
  rcases xtu with xt | xu
  · show False; exact xnt xt
  . show False; exact xnu xu


variable {α I : Type*}
variable (A B : I → Set α)
variable (s : Set α)


example : (s ∩ ⋃ i, A i) = ⋃ i, A i ∩ s := by
  ext x
  simp only [mem_inter_iff, mem_iUnion]
  constructor
  rintro ⟨xs, ⟨i, xAi⟩⟩
  exact ⟨i, xAi, xs⟩
  rintro ⟨i, xAi, xs⟩
  exact ⟨xs, ⟨i, xAi⟩⟩



example : (⋂ i, A i ∩ B i) = (⋂ i, A i) ∩ ⋂ i, B i := by
  ext x
  simp only [mem_inter_iff, mem_iInter]
  constructor
  · intro h
    constructor
    · intro i
      exact (h i).1
    intro i
    exact (h i).2
  rintro ⟨h1, h2⟩ i
  constructor
  · exact h1 i
  exact h2 i


example : (s ∪ ⋂ i, A i) = ⋂ i, A i ∪ s := by
  ext x
  simp only [mem_iInter, mem_inter_iff]
  by_cases xs : x ∈ s
  constructor
  · intro h s
    simp [mem_inter_iff]
    simp [xs]
  · intro h2
    constructor
    exact xs
  · simp
    constructor
    · intro xs2 I
      simp [xs] at xs2
      simp [xs]
      exact (xs2 I)
    · intro xs2
      simp [xs] at xs2
      simp [xs2]

def primes : Set ℕ :=
  {x | Nat.Prime x}

variable {α β : Type*}
variable (f : α → β)
variable (s t : Set α)
variable (u v : Set β)

open Function


-- if f : α → β, the library function defines preimage f p as f⁻¹' to be {x | f x ∈ p}
-- The expression x ∈ f⁻¹' p reduces f x ∈ p.

example : f⁻¹' (u ∩ v) = f⁻¹' u ∩ f⁻¹' v := by
  ext
  rfl

-- If s is a set of ele of type α the library defs.
-- image f s as f'' s, to be {y | ∃ x, x ∈ s ∧ (f x = y)}
-- y ∈ f''s can decompose to a triplet: ⟨x,xs,xeq⟩

example : f '' (s ∪ t) = f '' s ∪ f '' t := by
  ext y
  constructor
  · rintro ⟨x, xs | xt, rfl⟩
    · left
      use x, xs
    right
    use x, xt
  rintro (⟨x, xs, rfl⟩ | ⟨x,xt,rfl⟩)
  · use x, Or.inl xs
  use x, Or.inr xt

example : s ⊆ f⁻¹' (f '' s) := by
  intro x xs
  show f x ∈ f '' s
  use x, xs

-- easy exercise
example : f '' s ⊆ v ↔ s ⊆ f⁻¹' v := by
  exact image_subset_iff

variable {I : Type*} (A : I → Set α) (B : I → Set β)

-- images and preimages with index unions and intersections
-- Note, the i: I is needed to setup a non-empty set
example : (f '' ⋃ i, A i) = ⋃ i, f '' A i := by
  ext y; simp
  constructor
  · rintro ⟨x, ⟨i, xAi⟩, fxeq⟩
    use i, x
  rintro ⟨i, x, xAi, fxeq⟩
  exact ⟨x, ⟨i, xAi⟩, fxeq⟩


example : (f '' ⋂ i, A i) ⊆ ⋂ i, f '' A i := by
  intro y; simp
  intro x h fxeq i
  use x
  exact ⟨h i, fxeq⟩

#print Nat.Coprime

-- To claim that the fraction a/b where a, b ∈ ℤ is in lowest terms means that a and
-- b do not have any common factos, meaning they are coprime. Mathlib defines
-- Nat.Coprime m n to be Nat.gcd m n = 1.
-- if s and t are exp of type Nat we can write s.Coprime t, same for Nat.gcd
-- norm_num tactic can calc values

example (m n : Nat) (h : m.Coprime n) : m.gcd n = 1 := by
  rw [Nat.Coprime] at h
  exact h

example : Nat.Coprime 12 7 := by norm_num

#check Nat.prime_def_lt

example (p : ℕ) (prime_p : Nat.Prime p) : 2 ≤ p ∧ ∀ m : ℕ, m < p → m ∣ p → m = 1 := by
  rw [Nat.prime_def_lt] at prime_p
  assumption

-- If the square of a number is even, then the number is even

theorem even_of_even_sqr {m : ℕ} (h : 2 ∣ m^2) : 2 ∣ m := by
  rw [pow_two, Nat.prime_two.dvd_mul] at h
  cases h <;> assumption

-- the @[ext] annotation tells lean to auto-gen theorems that can be used to prove
-- the two instances of a structure are equal when comp. are equal aka extensionality
@[ext]
structure Point where
  x : ℝ
  y : ℝ
  z : ℝ

#check Point.ext
example (a b : Point) (hx : a.x = b.x) (hy : a.y = b.y) (hz : a.z = b.z) : a = b := by
  ext
  repeat' assumption

-- instance of point structure
def myPoint1 : Point where
  x := 2
  y := -1
  z := 4

-- We use protected keyword so that the name of the theorem is Point.add_comm
namespace Point

def add (a b : Point) : Point :=
  ⟨a.x + b.x, a.y + b.y, a.z + b.z⟩

protected theorem add_comm (a b : Point) : add a b = add b a := by
  rw [add, add]
  ext <;> dsimp
  repeat' apply add_comm

example (a b : Point) : add a b = add b a := by simp [add, add_comm]

protected theorem add_assoc (a b c : Point) : (a.add b).add c = a.add (b.add c) := by
  simp [add, add_assoc]

def smul (r : ℝ) (a : Point) : Point :=
  ⟨r * a.x, r * a.y, r * a.z⟩

theorem smul_distrib (r : ℝ) (a b : Point) : (smul r a).add (smul r b) = smul r (a.add b) := by
  simp [add, smul]
  simp [mul_add]

end Point

theorem add_x (a b : Point) : (a.add b).x = a.x + b.x :=
  rfl

-- algebraic structures are akin to the structure Point, the structure cmd is designed spec. to
-- generate algebraic structures.

structure Group₁ (α : Type*) where
  mul : α → α → α
  one : α
  inv : α → α
  mul_assoc : ∀ x y z : α, mul (mul x y) z = mul x (mul y z)
  mul_one : ∀ x : α, mul x one = x
  one_mul : ∀ x : α, mul one x = x
  mul_left_inv : ∀ x : α, mul (inv x) x = one

#check Group₁
#check Group --Mathlib defined group

-- Group concatenation ↓
structure Group₁Cat where
  α : Type*
  str : Group₁ α


section
variable (α β γ : Type*)
variable (f : α ≃ β) (g : β ≃ γ)

-- f : α ≃ β is a bijection between α and β
#check Equiv α β
#check (f.toFun : α → β)
#check (f.invFun : β → α)
#check (f.right_inv : ∀ x : β, f (f.invFun x) = x)
#check (f.left_inv : ∀ x : α, f.invFun (f x) = x)
#check (Equiv.refl α : α ≃ α)
#check (f.symm : β ≃ α)
#check (f.trans g : α ≃ γ)

example (x : α) : (f.trans g).toFun x = g.toFun (f.toFun x) := by
  rfl


-- exercise
-- AddGroup data type built to spec
structure AddGroup₁ (α : Type*) where
  add : α → α → α
  zero : α
  neg : α → α
  add_assoc : ∀ x y z : α, add (add x y) z = add x (add y z)
  add_zero : ∀ x : α, add x zero = x
  zero_add : ∀ x : α, add x zero = x
  add_left_neg : ∀ x : α, add (neg x) x = zero

@[ext]
structure Point2 where
  x : ℝ
  y : ℝ
  z : ℝ


namespace Point2

def add (a b : Point2) : Point2 :=
  ⟨a.x + b.x, a.y + b.y, a.z + b.z⟩

def negate (a : Point2) : Point2 :=
  ⟨-a.x, -a.y, -a.z⟩

def zero : Point2 := ⟨0, 0, 0⟩

-- A point under the AddGroup scheme
def addGroupPoint : AddGroup₁ Point2 where
  add := Point2.add
  zero := Point2.zero
  neg := Point2.negate
  add_assoc := by simp [Point2.add, add_assoc]
  add_zero := by simp [Point2.add, Point2.zero]
  zero_add := by simp [Point2.add, Point2.zero]
  add_left_neg := by simp [Point2.add, Point2.negate, Point2.zero]

end Point2

-- Mathlib is setup to use generic group notation, for Equiv.Perm α
variable {α : Type*} (f g : Equiv.Perm α) (n : ℕ)
#check f * g
#check f * g * g⁻¹
#check g ^ n

example : f * g * g⁻¹ = f := by rw [mul_assoc, mul_right_inv, mul_one]


-- Building the Guassian Inteers


-- The gaussians are the set of complex numbers s.t. {a + bi | a, b ∈ ℤ}
@[ext]
structure gaussInt where
  re : ℤ
  im : ℤ

instance : Zero gaussInt :=
  ⟨⟨0, 0⟩⟩

instance : One gaussInt :=
  ⟨⟨1, 0⟩⟩

instance : Add gaussInt :=
  ⟨fun x y ↦ ⟨x.re + y.re, x.im + y.im⟩⟩

instance : Neg gaussInt :=
  ⟨fun x ↦ ⟨-x.re, -x.im⟩⟩

instance : Mul gaussInt :=
  ⟨fun x y ↦ ⟨x.re * y.re - x.im * y.im, x.re * y.im + x.im * y.re⟩⟩

-- The above we are defining particular instances of Guassian ints use the aptly named "instance" key-word
-- Additionally doing the above allows lean's default tactics to do their thing.
 theorem zero_def : (0 : gaussInt) = ⟨0, 0⟩ :=
  rfl

theorem one_def : (1 : gaussInt) = ⟨1, 0⟩ :=
  rfl

theorem add_def (x y : gaussInt) : x + y = ⟨x.re + y.re, x.im + y.im⟩ :=
  rfl

theorem neg_def (x : gaussInt) : -x = ⟨-x.re, -x.im⟩ :=
  rfl

theorem mul_def (x y : gaussInt) :
    x * y = ⟨x.re * y.re - x.im * y.im, x.re * y.im + x.im * y.re⟩ :=
  rfl

@[simp]
theorem zero_re : (0 : gaussInt).re = 0 :=
  rfl


class One₁ (α : Type) where
  one : α

#check One₁.one

@[class] structure One₂ (α : Type) where
  one : α

#check One₂.one -- writing @[class] keeps the second arg explicit

-- We will assign notation to One₁.one
@[inherit_doc]
notation "𝟙" => One₁.one

-- Data carrying class
class Dia₁ (α : Type) where
  dia : α → α → α

infixl:70 "◇" => Dia₁.dia

class Semigroup₁ (α : Type) where
  toDia₁ : Dia₁ α
  dia_assoc : ∀ a b c : α, a ◇ b ◇ c = a ◇ (b ◇ c)

-- We additionally need to state toDia is in attribute of Semigroup₁ as it is not in type class's
-- database
attribute [instance] Semigroup₁.toDia₁

-- without needing attribute
class Semigroup₂ (α : Type) extends Dia₁ α where
  dia_assoc : ∀ a b c : α, a ◇ b ◇ c = a ◇ (b ◇ c)

example {α : Type} [Semigroup₂ α] (a b : α) : α := a ◇ b

class DiaOneClass₁ (α : Type) extends One₁ α, Dia₁ α where
  one_dia : ∀ a : α, 𝟙 ◇ a = a
  dia_one : ∀ a : α , a ◇ 𝟙 = a
-- A monoid has an associativty operation and an identity operation
class Monoid₁ (α : Type) extends Semigroup₁ α, DiaOneClass₁ α
#check Monoid₁

class Inv₁ (α : Type) where
  inv : α → α

@[inherit_doc]
postfix:max "⁻¹" => Inv₁.inv

class Group₃ (G : Type) extends Monoid₁ G, Inv G where
  inv_dia : ∀ a : G, a⁻¹ ◇ a = 𝟙

lemma left_inv_eq_right_inv₃ {M : Type} [Monoid₁ M] {a b c : M} (hba : b ◇ a = 𝟙) (hac : a ◇ c = 𝟙) : b = c :=
  by rw [<- DiaOneClass₁.one_dia c, <- hba, Semigroup₁.dia_assoc, hac, DiaOneClass₁.dia_one b]

export DiaOneClass₁ (one_dia dia_one)
export Semigroup₁ (dia_assoc)
export Group₃ (inv_dia)
-- copies the aboce lemmas into root name space

example {M : Type} [Monoid₁ M] {a b c : M} (hba : b ◇ a = 𝟙) (hac : a ◇ c = 𝟙) : b = c :=
  by
  rw [<- one_dia c, <- hba, dia_assoc, hac, dia_one]

-- exercises :)

lemma inv_eq_of_dia [Group₃ G] {a b : G} (h : a ◇ b = 𝟙) : a⁻¹ = b :=
  left_inv_eq_right_inv₃ (inv_dia a) h

lemma dia_inv [Group₃ G] (a : G) : a ◇ a⁻¹ = 𝟙 := by
  rw [<- inv_dia a⁻¹, inv_eq_of_dia (inv_dia a)]


-- Classes and Structures are defined in both additive and multiplicative notation
-- with an attr. to_additive
class AddSemigroup₃ (α : Type) extends Add α where
  add_assoc₃ : ∀ a b c : α, a + b + c = a + (b + c)

@[to_additive AddSemigroup₃]
class Semigroup₃ (α : Type) extends Mul α where
  mul_assoc₃ : ∀ a b c : α, a * b * c = a * (b * c)

class AddMonoid₃ (α : Type) extends AddSemigroup₃ α, AddZeroClass α

@[to_additive AddMonoid₃]
class Monoid₃ (α : Type) extends Semigroup₃ α, MulOneClass α

attribute [to_additive existing] Monoid₃.toMulOneClass

export Semigroup₃ (mul_assoc₃)
export AddSemigroup₃ (add_assoc₃)

@[to_additive]
lemma left_inv_eq_right_inv' {M : Type} [Monoid₃ M] {a b c : M} (hba : b * a = 1) (hac : a * c = 1) : b = c := by
  rw [← one_mul c, ← hba, mul_assoc₃, hac, mul_one b]

#check left_neg_eq_right_neg'


class AddCommSemigroup₃ (α : Type) extends AddSemigroup₃ α where
  add_comm : ∀ a b : α, a + b = b + a

@[to_additive AddCommSemigroup₃]
class CommSemigroup₃ (α : Type) extends Semigroup₃ α where
  mul_comm : ∀ a b : α, a * b = b * a

class AddCommMonoid₃ (α : Type) extends AddMonoid₃ α, AddCommSemigroup₃ α

@[to_additive AddCommMonoid₃]
class CommMonoid₃ (α : Type) extends Monoid₃ α, CommSemigroup₃ α

class AddGroup₄ (G : Type) extends AddMonoid₃ G, Neg G where
  neg_add : ∀ a : G, -a + a = 0

@[to_additive AddGroup₄]
class Group₄ (G : Type) extends Monoid₃ G, Inv G where
  inv_mul : ∀ a : G, a⁻¹ * a = 1

attribute [simp] Group₄.inv_mul AddGroup₄.neg_add

-- exercises
-- Note, Groups are Monoids with inverse elements
-- Semigroups are groups with associativity

@[to_additive]
lemma inv_eq_of_mul [Group₄ G] {a b : G} (h : a * b = 1) : a⁻¹ = b :=
  left_inv_eq_right_inv' (Group₄.inv_mul a) h


@[to_additive (attr := simp)]
lemma Group₄.mul_inv {G : Type} [Group₄ G] {a : G} : a * a⁻¹ = 1 := by
  rw [← inv_mul a⁻¹, inv_eq_of_mul (inv_mul a)]

@[to_additive]
lemma mul_left_cancel₃ {G : Type} [Group₄ G] {a b c : G} (h : a * b = a * c) : b = c := by
  simpa [← mul_assoc₃] using congr_arg (a⁻¹ * ·) h

-- apply associativity of our group then try to simplify after apply a congr_argument where
-- we substitute h in for ·

@[to_additive]
lemma mul_right_cancel₃ {G : Type} [Group₄ G] {a b c : G} (h : b*a = c*a) : b = c := by
  simpa [mul_assoc₃] using congr_arg (· * a⁻¹) h
