import Wikipedia.HopfProblem.Lattice
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Coprod.Basic
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

/-!
# The abstract (3,4,∞) triangle group and its integral representation

The group of Sections 2.11 and 2.15 is constructed as the actual free
product of cyclic groups of orders three and four.  Its generators have
exactly those orders, generate the group, and satisfy the universal
mapping property.  Applying that property to the explicit integral
matrices constructs the source representation, rather than assuming one.

This algebraic construction does not assert that a geometric action on
the upper half-plane is faithful or has the required fundamental domain.
-/

noncomputable section

open Function Set
open scoped MatrixGroups

namespace Wikipedia.HopfProblem.SpecialPeriods

/-- A homomorphism out of a finite cyclic group, induced by an element
whose order divides its modulus. -/
def cyclicPowerHom {G : Type*} [Group G] (n : ℕ) (a : G) (ha : a ^ n = 1) :
    Multiplicative (ZMod n) →* G :=
  (ZMod.lift n ⟨zmultiplesHom (Additive G) (Additive.ofMul a), by
    change a ^ (n : ℤ) = 1
    simpa only [zpow_natCast] using ha⟩).toMultiplicativeLeft

@[simp] theorem cyclicPowerHom_intCast {G : Type*} [Group G] (n : ℕ)
    (a : G) (ha : a ^ n = 1) (k : ℤ) :
    cyclicPowerHom n a ha (Multiplicative.ofAdd (k : ZMod n)) = a ^ k := by
  simp [cyclicPowerHom]

@[simp] theorem cyclicPowerHom_one {G : Type*} [Group G] (n : ℕ)
    (a : G) (ha : a ^ n = 1) :
    cyclicPowerHom n a ha (Multiplicative.ofAdd (1 : ZMod n)) = a := by
  simpa using cyclicPowerHom_intCast n a ha 1

private theorem cyclic_eq_generator_zpow {n : ℕ} (x : Multiplicative (ZMod n)) :
    ∃ k : ℤ, x = Multiplicative.ofAdd (1 : ZMod n) ^ k := by
  obtain ⟨k, hk⟩ := ZMod.intCast_surjective x.toAdd
  refine ⟨k, ?_⟩
  change x.toAdd = k • (1 : ZMod n)
  simpa using hk.symm

private theorem cyclic_hom_ext {G : Type*} [Group G] {n : ℕ}
    {f g : Multiplicative (ZMod n) →* G}
    (h : f (Multiplicative.ofAdd 1) = g (Multiplicative.ofAdd 1)) : f = g := by
  apply MonoidHom.ext
  intro x
  obtain ⟨k, rfl⟩ := cyclic_eq_generator_zpow x
  rw [map_zpow, map_zpow, h]

/-- The actual free product `ℤ/3 * ℤ/4`. -/
abbrev TriangleGroup :=
  Monoid.Coprod (Multiplicative (ZMod 3)) (Multiplicative (ZMod 4))

def triangleGenerator₁ : TriangleGroup :=
  Monoid.Coprod.inl (Multiplicative.ofAdd (1 : ZMod 3))

def triangleGenerator₂ : TriangleGroup :=
  Monoid.Coprod.inr (Multiplicative.ofAdd (1 : ZMod 4))

def triangleCuspGenerator : TriangleGroup := (triangleGenerator₁ * triangleGenerator₂)⁻¹

theorem triangleGenerator₁_order : orderOf triangleGenerator₁ = 3 := by
  rw [triangleGenerator₁, orderOf_injective _ Monoid.Coprod.inl_injective,
    orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one]

theorem triangleGenerator₂_order : orderOf triangleGenerator₂ = 4 := by
  rw [triangleGenerator₂, orderOf_injective _ Monoid.Coprod.inr_injective,
    orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one]

@[simp] theorem triangleGenerator₁_cube : triangleGenerator₁ ^ 3 = 1 := by
  simpa only [triangleGenerator₁_order] using pow_orderOf_eq_one triangleGenerator₁

@[simp] theorem triangleGenerator₂_fourth : triangleGenerator₂ ^ 4 = 1 := by
  simpa only [triangleGenerator₂_order] using pow_orderOf_eq_one triangleGenerator₂

@[simp] theorem triangle_generators_cusp_relation :
    triangleGenerator₁ * triangleGenerator₂ * triangleCuspGenerator = 1 := by
  exact mul_inv_cancel _

/-- The two distinguished cyclic generators generate the whole free
product as a subgroup. -/
theorem triangle_generators_generate :
    Subgroup.closure ({triangleGenerator₁, triangleGenerator₂} : Set TriangleGroup) = ⊤ := by
  apply top_unique
  intro x hx
  clear hx
  induction x using Monoid.Coprod.induction_on with
  | inl x =>
      obtain ⟨k, rfl⟩ := cyclic_eq_generator_zpow x
      rw [map_zpow]
      exact Subgroup.zpow_mem _ (Subgroup.subset_closure (by simp [triangleGenerator₁])) k
  | inr x =>
      obtain ⟨k, rfl⟩ := cyclic_eq_generator_zpow x
      rw [map_zpow]
      exact Subgroup.zpow_mem _ (Subgroup.subset_closure (by simp [triangleGenerator₂])) k
  | mul x y hx hy => exact Subgroup.mul_mem _ hx hy

/-- The universal homomorphism determined by two elements satisfying the
order-three and order-four relations. -/
def triangleLift {G : Type*} [Group G] (a b : G) (ha : a ^ 3 = 1) (hb : b ^ 4 = 1) :
    TriangleGroup →* G :=
  Monoid.Coprod.lift (cyclicPowerHom 3 a ha) (cyclicPowerHom 4 b hb)

@[simp] theorem triangleLift_generator₁ {G : Type*} [Group G]
    (a b : G) (ha : a ^ 3 = 1) (hb : b ^ 4 = 1) :
    triangleLift a b ha hb triangleGenerator₁ = a := by
  simp [triangleLift, triangleGenerator₁]

@[simp] theorem triangleLift_generator₂ {G : Type*} [Group G]
    (a b : G) (ha : a ^ 3 = 1) (hb : b ^ 4 = 1) :
    triangleLift a b ha hb triangleGenerator₂ = b := by
  simp [triangleLift, triangleGenerator₂]

@[simp] theorem triangleLift_cusp {G : Type*} [Group G]
    (a b : G) (ha : a ^ 3 = 1) (hb : b ^ 4 = 1) :
    triangleLift a b ha hb triangleCuspGenerator = (a * b)⁻¹ := by
  simp [triangleCuspGenerator]

/-- Agreement on the two actual generators determines a homomorphism. -/
theorem triangle_hom_ext {G : Type*} [Group G] {f g : TriangleGroup →* G}
    (h₁ : f triangleGenerator₁ = g triangleGenerator₁)
    (h₂ : f triangleGenerator₂ = g triangleGenerator₂) : f = g := by
  apply Monoid.Coprod.hom_ext
  · exact cyclic_hom_ext h₁
  · exact cyclic_hom_ext h₂

theorem triangleLift_unique {G : Type*} [Group G]
    (a b : G) (ha : a ^ 3 = 1) (hb : b ^ 4 = 1) (f : TriangleGroup →* G)
    (h₁ : f triangleGenerator₁ = a) (h₂ : f triangleGenerator₂ = b) :
    f = triangleLift a b ha hb := by
  apply triangle_hom_ext <;> simp [h₁, h₂]

/-- The image of any representation is exactly the subgroup generated by
the two generator images. -/
theorem triangle_range {G : Type*} [Group G] (f : TriangleGroup →* G) :
    f.range = Subgroup.closure ({f triangleGenerator₁, f triangleGenerator₂} : Set G) := by
  rw [MonoidHom.range_eq_map, ← triangle_generators_generate, MonoidHom.map_closure,
    Set.image_pair]

/-- The order-three lattice monodromy, as a genuine special-linear matrix. -/
def triangleLatticeT₁ : SL(4, ℤ) := ⟨T₁, det_T₁⟩

/-- The order-four lattice monodromy, as a genuine special-linear matrix. -/
def triangleLatticeT₂ : SL(4, ℤ) := ⟨T₂, det_T₂⟩

theorem triangleLatticeT₁_cube : triangleLatticeT₁ ^ 3 = 1 :=
  Subtype.ext T₁_cube

theorem triangleLatticeT₂_fourth : triangleLatticeT₂ ^ 4 = 1 :=
  Subtype.ext T₂_fourth

/-- Definition 2.15: the integral representation obtained by the proved
universal property, without a supplied representation hypothesis. -/
def triangleLatticeRepresentation : TriangleGroup →* SL(4, ℤ) :=
  triangleLift triangleLatticeT₁ triangleLatticeT₂
    triangleLatticeT₁_cube triangleLatticeT₂_fourth

@[simp] theorem triangleLatticeRepresentation_generator₁ :
    triangleLatticeRepresentation triangleGenerator₁ = triangleLatticeT₁ :=
  triangleLift_generator₁ ..

@[simp] theorem triangleLatticeRepresentation_generator₂ :
    triangleLatticeRepresentation triangleGenerator₂ = triangleLatticeT₂ :=
  triangleLift_generator₂ ..

@[simp] theorem triangleLatticeRepresentation_generator₁_matrix :
    (triangleLatticeRepresentation triangleGenerator₁ : LatticeMatrix) = T₁ := by
  simp [triangleLatticeT₁]

@[simp] theorem triangleLatticeRepresentation_generator₂_matrix :
    (triangleLatticeRepresentation triangleGenerator₂ : LatticeMatrix) = T₂ := by
  simp [triangleLatticeT₂]

theorem triangleLatticeRepresentation_cusp_matrix :
    (triangleLatticeRepresentation triangleCuspGenerator : LatticeMatrix) = T₀ := by
  rw [triangleLatticeRepresentation, triangleLift_cusp]
  decide

theorem triangleLatticeRepresentation_range :
    triangleLatticeRepresentation.range =
      Subgroup.closure ({triangleLatticeT₁, triangleLatticeT₂} : Set (SL(4, ℤ))) := by
  simpa using triangle_range triangleLatticeRepresentation

theorem triangleLatticeRepresentation_unique (f : TriangleGroup →* SL(4, ℤ))
    (h₁ : (f triangleGenerator₁ : LatticeMatrix) = T₁)
    (h₂ : (f triangleGenerator₂ : LatticeMatrix) = T₂) :
    f = triangleLatticeRepresentation := by
  apply triangle_hom_ext
  · rw [triangleLatticeRepresentation_generator₁]
    exact Subtype.ext h₁
  · rw [triangleLatticeRepresentation_generator₂]
    exact Subtype.ext h₂

/-- The actual inverse-transpose homomorphism on the integral special
linear group. -/
def latticeContragredient : SL(4, ℤ) →* SL(4, ℤ) where
  toFun A := Matrix.SpecialLinearGroup.transpose A⁻¹
  map_one' := Subtype.ext (by simp [Matrix.SpecialLinearGroup.transpose])
  map_mul' A B := Subtype.ext (by
    change (((A * B)⁻¹ : SL(4, ℤ)) : LatticeMatrix).transpose =
      ((A⁻¹ : SL(4, ℤ)) : LatticeMatrix).transpose *
        ((B⁻¹ : SL(4, ℤ)) : LatticeMatrix).transpose
    simp only [mul_inv_rev, Matrix.SpecialLinearGroup.coe_mul, Matrix.transpose_mul])

/-- Definition 2.15: the dual integral lattice representation is the
contragredient of the constructed representation. -/
def triangleDualRepresentation : TriangleGroup →* SL(4, ℤ) :=
  latticeContragredient.comp triangleLatticeRepresentation

theorem triangleDualRepresentation_generator₁_matrix :
    (triangleDualRepresentation triangleGenerator₁ : LatticeMatrix) = A₁ := by
  rw [triangleDualRepresentation, MonoidHom.comp_apply,
    triangleLatticeRepresentation_generator₁]
  decide

theorem triangleDualRepresentation_generator₂_matrix :
    (triangleDualRepresentation triangleGenerator₂ : LatticeMatrix) = A₂ := by
  rw [triangleDualRepresentation, MonoidHom.comp_apply,
    triangleLatticeRepresentation_generator₂]
  decide

theorem triangleDualRepresentation_cusp_matrix :
    (triangleDualRepresentation triangleCuspGenerator : LatticeMatrix) = M₀ := by
  change (Matrix.adjugate (triangleLatticeRepresentation triangleCuspGenerator :
    LatticeMatrix)).transpose = M₀
  rw [triangleLatticeRepresentation_cusp_matrix]
  decide

/-- The transposed coordinate matrices used in Section 3. -/
def triangleCoordinateMatrix (g : TriangleGroup) : LatticeMatrix :=
  (triangleLatticeRepresentation g : LatticeMatrix).transpose

/-- The coordinate matrices form an anti-homomorphism, as required by the
column-coordinate convention in the source. -/
theorem triangleCoordinateMatrix_mul (g h : TriangleGroup) :
    triangleCoordinateMatrix (g * h) = triangleCoordinateMatrix h * triangleCoordinateMatrix g := by
  simp [triangleCoordinateMatrix, Matrix.transpose_mul]

/-- The matrix at the inverse element is exactly the dual representation. -/
theorem triangleCoordinateMatrix_inv (g : TriangleGroup) :
    triangleCoordinateMatrix g⁻¹ = (triangleDualRepresentation g : LatticeMatrix) := by
  change (triangleLatticeRepresentation g⁻¹ : LatticeMatrix).transpose =
    (((triangleLatticeRepresentation g)⁻¹ : SL(4, ℤ)) : LatticeMatrix).transpose
  rw [map_inv]

end Wikipedia.HopfProblem.SpecialPeriods
