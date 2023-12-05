import Mathlib.Tactic
import Mathlib.Data.Set.Lattice
import Mathlib.Topology.Instances.Real
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.Perm.Cycle.Concrete
import Mathlib.GroupTheory.Perm.Subgroup
import Mathlib.GroupTheory.PresentedGroup

-- There are a few ways to generate morphisms. The most obvious of which is to
-- define a predicate on functions.
def isMonoidHom₁ [Monoid G] [Monoid H] (f : G → H) : Prop :=
  f 1 = 1 ∧ ∀ g g', f (g * g') = f g * f g'

-- The above definition isn't optimal as the user must remember the
-- ordering used in conjunction, therefore we can use a structure
-- to simplify

structure isMonoidHom₂ [Monoid G] [Monoid H] (f : G → H) : Prop where
  map_one : f 1 = 1
  map_mul : ∀ g g', f (g * g') = f g * f g'

-- We can generate a morphism between monoids
@[ext]
structure MonoidHom₁ (G H : Type) [Monoid G] [Monoid H] where
  toFun : G → H
  map_one : toFun 1 = 1
  map_mul : ∀ g g', toFun (g * g') = toFun g * toFun g'


-- Registers a coercion, that is to say a type can be used as a function
instance [Monoid G] [Monoid H] : CoeFun (MonoidHom₁ G H) (fun _ ↦ G → H) where
  coe := MonoidHom₁.toFun

example [Monoid G] [Monoid H] (f : MonoidHom₁ G H) : f 1 = 1 := f.map_one

@[ext]
structure AddMonoidHom₁ (G H : Type) [AddMonoid G] [AddMonoid H] where
  toFun : G → H
  map_zero : toFun 0 = 0
  map_add : ∀ g g', toFun (g + g') = toFun g + toFun g'

instance [AddMonoid G] [AddMonoid H] : CoeFun (AddMonoidHom₁ G H) (fun _ ↦ G → H) where
  coe := AddMonoidHom₁.toFun

attribute [coe] AddMonoidHom₁.toFun


@[ext]
structure RingHom₁ (R S : Type) [Ring R] [Ring S] extends MonoidHom₁ R S, AddMonoidHom₁ R S
-- Note, we can't use the prior approach of applying the coercion (coe) attribute
-- to our Ring morphism as RingHom₁.toFun doesn't exist. Furthermore, the relevant
-- function is MonoidHom₁.toFun ∘ RingHom₁.toMonoidHom₁ which is not a declaration that
-- is taggable by coe.

class MonoidHomClass₁ (F : Type) (M N : outParam Type) [Monoid M] [Monoid N] where
  toFun : F → M → N
  map_one : ∀ f : F, toFun f 1 = 1
  map_mul : ∀ f g g', toFun f (g * g') = toFun f g * toFun f g'

instance [Monoid M] [Monoid N] [MonoidHomClass₁ F M N] : CoeFun F (fun _ ↦ M → N) where
  coe := MonoidHomClass₁.toFun

attribute [coe] MonoidHomClass₁.toFun

instance (M N : Type) [Monoid M] [Monoid N] : MonoidHomClass₁ (MonoidHom₁ M N) M N where
  toFun := MonoidHom₁.toFun
  map_one := fun f ↦ f.map_one
  map_mul := fun f ↦ f.map_mul

instance (R S : Type) [Ring R] [Ring S] : MonoidHomClass₁ (RingHom₁ R S) R S where
  toFun := fun f ↦ f.toMonoidHom₁.toFun
  map_one := fun f ↦ f.toMonoidHom₁.map_one
  map_mul := fun f ↦ f.toMonoidHom₁.map_mul


@[ext]
structure OrderPresHom (α β : Type) [LE α] [LE β] where
  toFun : α → β
  le_of_le : ∀ a a', a ≤ a' → toFun a ≤ toFun a'

class MonoidHomClass₃ (F : Type) (M N : outParam Type) [Monoid M] [Monoid N] extends
    FunLike F M (fun _ ↦ N) where
  map_one : ∀ f : F, f 1 = 1
  map_mul : ∀ (f : F) g g', f (g * g') = f g * f g'

instance (M N : Type) [Monoid M] [Monoid N] : MonoidHomClass₃ (MonoidHom₁ M N) M N where
  coe := MonoidHom₁.toFun
  coe_injective' := MonoidHom₁.ext
  map_one := MonoidHom₁.map_one
  map_mul := MonoidHom₁.map_mul

-- exercise

@[ext]
structure OrderPresMonoidHom (M N : Type) [Monoid M] [LE M] [Monoid N] [LE N] extends
MonoidHom₁ M N, OrderPresHom M N

class OrderPresHomClass (F : Type) (α β : outParam Type) [LE α] [LE β] extends FunLike F α (fun _ ↦ β) where
  le_of_le : ∀ (f : F) a a', a ≤ a' → f a ≤ f a'

instance (α β : Type) [LE α] [LE β] : OrderPresHomClass (OrderPresHom α β) α β where
  coe := OrderPresHom.toFun
  coe_injective' := OrderPresHom.ext
  le_of_le := OrderPresHom.le_of_le

instance (α β : Type) [LE α] [Monoid α] [LE β] [Monoid β] :
    OrderPresHomClass (OrderPresMonoidHom α β) α β where
      coe := fun f ↦ f.toOrderPresHom.toFun
      coe_injective' := OrderPresMonoidHom.ext
      le_of_le := fun f ↦ f.toOrderPresHom.le_of_le

instance (α β : Type) [LE α] [Monoid α] [LE β] [Monoid β] : MonoidHomClass₃ (OrderPresMonoidHom α β) α β where
  coe := fun f ↦ f.toOrderPresHom.toFun
  coe_injective' := OrderPresMonoidHom.ext
  map_one := fun f ↦ f.toMonoidHom₁.map_one
  map_mul := fun f ↦ f.toMonoidHom₁.map_mul

-- Sub-objects, we will start exploring sets that inherit algebraic structure
@[ext]
structure Submonoid₁ (M : Type) [Monoid M] where
  -- Carrier of submonoid
  carrier : Set M
  -- The prod of two eles of a submonoid belong to the same submonoid
  mul_mem {a b} : a ∈ carrier → b ∈ carrier -> a * b ∈ carrier
  -- The unit ele belongs to the submonoid
  one_mem : 1 ∈ carrier

-- Submonoids in M can be seen as sets in M
instance [Monoid M] : SetLike (Submonoid₁ M) M where
  coe := Submonoid₁.carrier
  coe_injective' := Submonoid₁.ext

example [Monoid M] (N : Submonoid₁ M) : 1 ∈ N := N.one_mem

-- N is a set in M as shown by direct image
example [Monoid M] (N : Submonoid₁ M) (α : Type) (f : M → α) := f '' N

--
instance SubMonoid₁Monoid [Monoid M] (N : Submonoid₁ M) : Monoid N where
  mul := fun x y ↦ ⟨x*y, N.mul_mem x.property y.property⟩
  mul_assoc := fun x y z ↦ SetCoe.ext (mul_assoc (x : M) y z)
  one := ⟨1, N.one_mem⟩
  one_mul := fun x ↦ SetCoe.ext (one_mul (x : M))
  mul_one := fun x ↦ SetCoe.ext (mul_one (x : M))

class SubmonoidClass₁ (S : Type) (M : Type) [Monoid M] [SetLike S M] : Prop where
  mul_mem : ∀ (s : S) {a b : M}, a ∈ s → b ∈ s → a * b ∈ s
  one_mem : ∀ s : S, 1 ∈ s


instance [Monoid M] : SubmonoidClass₁ (Submonoid₁ M) M where
  mul_mem := Submonoid₁.mul_mem
  one_mem := Submonoid₁.one_mem


instance [Monoid M] : Inf (Submonoid₁ M) :=
  ⟨fun S₁ S₂ ↦
    { carrier := S₁ ∩ S₂
      one_mem := ⟨S₁.one_mem, S₂.one_mem⟩
      mul_mem := fun ⟨hx, hx'⟩ ⟨hy, hy'⟩ ↦ ⟨S₁.mul_mem hx hy, S₂.mul_mem hx' hy'⟩}⟩

-- If the elements of N and P meet in a lattice, the greatest lower
-- bound is given by N ⊓ P
example [Monoid M] (N P : Submonoid₁ M) : Submonoid₁ M := N ⊓ P

example {M : Type*} [Monoid M] (x : M) : x * 1 = x := mul_one x
example {M : Type*} [AddCommMonoid M] (x y : M) : x + y = y + x := add_comm x y

-- Type morphisms are labeled M →* N, lean will automatically see such a morphism
-- from M to N when we apply it to elements of M
example {M N : Type*} [Monoid M] [Monoid N] (x y : M) (f : M →* N) : f (x * y) = f x * f y :=
  f.map_mul x y

example {M N : Type*} [AddMonoid M] [AddMonoid N] (f : M →+ N) : f 0 = 0 :=
  f.map_zero

-- Use MonoidHom.comp to compose maps
example {M N P : Type*} [AddMonoid M] [AddMonoid N] [AddMonoid P] (f : M →+ N) (g : N →+ P) : M →+ P :=
  g.comp f

-- Mentioned in previous weeks groups are monoids with the extra property that every element has
-- an inverse
example {G : Type*} [Group G] (x : G) : x * x⁻¹ = 1 := mul_inv_self x
-- group tactic proves identities that hold in a group
example {G : Type*} [Group G] (x y z : G) : x * (y * z) * (x * z)⁻¹* ( x * y * x⁻¹)⁻¹ = 1 := by group
-- abel proves identities in commutative additive groups
example {G : Type*} [AddCommGroup G] (x y z : G) : z + x + (y - z - x) = y := by
  abel

example {G H : Type*} [Group G] [Group H] (x : G) (f : G →* H) : f (x⁻¹) = (f x)⁻¹ :=
  f.map_inv x

example {G H : Type*} [Group G] [Group H] (f : G ≃* H) : f.trans f.symm = MulEquiv.refl G :=
  f.self_trans_symm

example {G : Type*} [Group G] (H : Subgroup G) {x y : G} (hx : x ∈ H) (hy : y ∈ H) :
  x * y ∈ H := H.mul_mem hx hy

-- Checking to see that the infimum of two subgroups is their intersection
example {G : Type*} [Group G] (H H' : Subgroup G) :
  ((H ⊓ H' : Subgroup G) : Set G) = (H : Set G) ∩ (H' : Set G) := rfl


-- exercise

def conjugate {G : Type*} [Group G] (x : G) (H : Subgroup G) : Subgroup G where
  carrier := {a : G | ∃ h, h ∈ H ∧ a = x * h * x⁻¹}
  one_mem' := by
    dsimp
    use 1
    constructor
    exact H.one_mem
    group
  inv_mem' := by
    dsimp
    rintro - ⟨h, h_in, rfl⟩
    use h⁻¹, H.inv_mem h_in
    group
  mul_mem' := by
    dsimp
    rintro - - ⟨h, h_in, rfl⟩ ⟨k, k_in, rfl⟩
    use h*k, H.mul_mem h_in k_in
    group
