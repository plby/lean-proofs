import Wikipedia.HopfProblem.SpecialPeriodsTrianglePresentation
import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices
import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction

/-!
# The modular image of the triangle group

The homomorphism in Section 2.15 has the actual projective modular group
`PSL(2, ℤ)` as its target.  We construct it from the free-product universal
property and prove that it is surjective.  The order-four source generator
has order two in this quotient; in particular, this modular representation
is not the faithful geometric action of the triangle group.
-/

noncomputable section

open Function Set Matrix
open scoped MatrixGroups UpperHalfPlane

namespace Wikipedia.HopfProblem.SpecialPeriods

/-- The canonical quotient map from the integral special-linear group to
Mathlib's projective special-linear group. -/
def modularProjectivization : SL(2, ℤ) →* PSL(2, ℤ) :=
  QuotientGroup.mk' (Subgroup.center (SL(2, ℤ)))

theorem modularProjectivization_surjective :
    Function.Surjective modularProjectivization :=
  QuotientGroup.mk'_surjective _

private theorem modular_neg_one_mem_center :
    (-1 : SL(2, ℤ)) ∈ Subgroup.center (SL(2, ℤ)) := by
  apply Subgroup.mem_center_iff.mpr
  intro A
  apply Subtype.ext
  change (A : Matrix (Fin 2) (Fin 2) ℤ) * (-1) = (-1) * A
  simp

@[simp] theorem modularProjectivization_neg_one :
    modularProjectivization (-1) = 1 :=
  (QuotientGroup.eq_one_iff _).mpr modular_neg_one_mem_center

@[simp] theorem modularProjectivization_neg (A : SL(2, ℤ)) :
    modularProjectivization (-A) = modularProjectivization A := by
  have hn : (-1 : SL(2, ℤ)) * A = -A := by
    apply Subtype.ext
    change (-1 : Matrix (Fin 2) (Fin 2) ℤ) * A = -(A : Matrix (Fin 2) (Fin 2) ℤ)
    simp
  rw [← hn, map_mul, modularProjectivization_neg_one, one_mul]

/-- The lift of the first modular generator, acting by `z ↦ (z - 1) / z`. -/
def triangleModularA : SL(2, ℤ) :=
  ⟨!![1, -1; 1, 0], by decide⟩

@[simp] theorem triangleModularA_matrix :
    (triangleModularA : Matrix (Fin 2) (Fin 2) ℤ) = !![1, -1; 1, 0] := rfl

theorem triangleModularA_eq_T_mul_S :
    triangleModularA = ModularGroup.T * ModularGroup.S := by decide

theorem triangleModularA_cube : triangleModularA ^ 3 = -1 := by decide

theorem modularS_square : ModularGroup.S ^ 2 = -1 := by decide

theorem triangleModularA_mul_S : triangleModularA * ModularGroup.S = -ModularGroup.T :=
  by decide

/-- The first modular image of the abstract triangle generators. -/
def triangleModularGenerator₁ : PSL(2, ℤ) := modularProjectivization triangleModularA

/-- The second modular image of the abstract triangle generators. -/
def triangleModularGenerator₂ : PSL(2, ℤ) := modularProjectivization ModularGroup.S

@[simp] theorem triangleModularGenerator₁_cube : triangleModularGenerator₁ ^ 3 = 1 := by
  rw [triangleModularGenerator₁, ← map_pow, triangleModularA_cube,
    modularProjectivization_neg_one]

@[simp] theorem triangleModularGenerator₂_square : triangleModularGenerator₂ ^ 2 = 1 := by
  rw [triangleModularGenerator₂, ← map_pow, modularS_square,
    modularProjectivization_neg_one]

theorem triangleModularGenerator₂_fourth : triangleModularGenerator₂ ^ 4 = 1 := by
  rw [show 4 = 2 * 2 from rfl, pow_mul, triangleModularGenerator₂_square, one_pow]

theorem triangleModularGenerator₁_mul_generator₂ :
    triangleModularGenerator₁ * triangleModularGenerator₂ =
      modularProjectivization ModularGroup.T := by
  rw [triangleModularGenerator₁, triangleModularGenerator₂, ← map_mul,
    triangleModularA_mul_S, modularProjectivization_neg]

/-- The source's homomorphism `Δ → PSL₂(ℤ)`, constructed without an
assumed representation or any faithfulness hypothesis. -/
def triangleModularRepresentation : TriangleGroup →* PSL(2, ℤ) :=
  triangleLift triangleModularGenerator₁ triangleModularGenerator₂
    triangleModularGenerator₁_cube triangleModularGenerator₂_fourth

@[simp] theorem triangleModularRepresentation_generator₁ :
    triangleModularRepresentation triangleGenerator₁ = triangleModularGenerator₁ :=
  triangleLift_generator₁ ..

@[simp] theorem triangleModularRepresentation_generator₂ :
    triangleModularRepresentation triangleGenerator₂ = triangleModularGenerator₂ :=
  triangleLift_generator₂ ..

/-- With the source convention `δ₀ = (δ₁ δ₂)⁻¹`, the modular cusp
generator is the translation by `-1`, not by `+1`. -/
@[simp] theorem triangleModularRepresentation_cusp :
    triangleModularRepresentation triangleCuspGenerator =
      modularProjectivization ModularGroup.T⁻¹ := by
  rw [triangleModularRepresentation, triangleLift_cusp,
    triangleModularGenerator₁_mul_generator₂, map_inv]

theorem triangleModularRepresentation_surjective :
    Function.Surjective triangleModularRepresentation := by
  let H : Subgroup (SL(2, ℤ)) :=
    triangleModularRepresentation.range.comap modularProjectivization
  have hS : ModularGroup.S ∈ H :=
    ⟨triangleGenerator₂, triangleModularRepresentation_generator₂⟩
  have hT : ModularGroup.T ∈ H := by
    refine ⟨triangleGenerator₁ * triangleGenerator₂, ?_⟩
    rw [map_mul, triangleModularRepresentation_generator₁,
      triangleModularRepresentation_generator₂, triangleModularGenerator₁_mul_generator₂]
  have hH : H = ⊤ := by
    apply top_unique
    rw [← _root_.SpecialLinearGroup.SL2Z_generators]
    exact (Subgroup.closure_le _).mpr (Set.pair_subset hS hT)
  intro q
  obtain ⟨A, rfl⟩ := modularProjectivization_surjective q
  have hA : A ∈ H := hH ▸ Subgroup.mem_top A
  exact hA

theorem triangleModularRepresentation_unique (f : TriangleGroup →* PSL(2, ℤ))
    (h₁ : f triangleGenerator₁ = triangleModularGenerator₁)
    (h₂ : f triangleGenerator₂ = triangleModularGenerator₂) :
    f = triangleModularRepresentation := by
  apply triangle_hom_ext <;> simp [h₁, h₂]

/-- The modular representation kills the square of the order-four
generator, and hence is not faithful. -/
theorem triangleModularRepresentation_not_injective :
    ¬ Function.Injective triangleModularRepresentation := by
  intro hi
  have he : triangleModularRepresentation (triangleGenerator₂ ^ 2) =
      triangleModularRepresentation 1 := by
    simp
  have hd := orderOf_dvd_of_pow_eq_one (hi he)
  rw [triangleGenerator₂_order] at hd
  norm_num at hd

private theorem modular_center_eq_one_or_neg_one (A : SL(2, ℤ))
    (hA : A ∈ Subgroup.center (SL(2, ℤ))) : A = 1 ∨ A = -1 := by
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  have hr₂ : r ^ 2 = 1 := by simpa using hr
  rcases sq_eq_one_iff.mp hr₂ with rfl | rfl
  · left
    apply Subtype.ext
    simpa using hrA.symm
  · right
    apply Subtype.ext
    simpa using hrA.symm

private theorem modular_center_le_permutation_kernel :
    Subgroup.center (SL(2, ℤ)) ≤ (MulAction.toPermHom (SL(2, ℤ)) ℍ).ker := by
  intro A hA
  rcases modular_center_eq_one_or_neg_one A hA with rfl | rfl
  · exact map_one _
  · apply Equiv.ext
    intro z
    change (-1 : SL(2, ℤ)) • z = z
    simp

/-- The actual Möbius action descends from `SL₂(ℤ)` to Mathlib's quotient
`PSL₂(ℤ)`, bundled as a homomorphism to permutations. -/
def modularPSLPermutation : PSL(2, ℤ) →* Equiv.Perm ℍ :=
  QuotientGroup.lift (Subgroup.center (SL(2, ℤ)))
    (MulAction.toPermHom (SL(2, ℤ)) ℍ) modular_center_le_permutation_kernel

@[simp] theorem modularPSLPermutation_projectivization (A : SL(2, ℤ)) (z : ℍ) :
    modularPSLPermutation (modularProjectivization A) z = A • z := rfl

/-- The modular action of the triangle group, factoring through its
constructed projective integral representation. -/
def triangleModularAction : TriangleGroup →* Equiv.Perm ℍ :=
  modularPSLPermutation.comp triangleModularRepresentation

@[simp] theorem triangleModularAction_generator₁_apply (z : ℍ) :
    triangleModularAction triangleGenerator₁ z = triangleModularA • z := by
  simp [triangleModularAction, triangleModularGenerator₁]

@[simp] theorem triangleModularAction_generator₂_apply (z : ℍ) :
    triangleModularAction triangleGenerator₂ z = ModularGroup.S • z := by
  simp [triangleModularAction, triangleModularGenerator₂]

/-- The first generator has exactly the source's fractional-linear
formula in complex coordinates. -/
theorem triangleModularAction_generator₁_coe (z : ℍ) :
    (triangleModularAction triangleGenerator₁ z : ℂ) = (z - 1) / z := by
  rw [triangleModularAction_generator₁_apply, UpperHalfPlane.coe_specialLinearGroup_apply]
  simp [triangleModularA, sub_eq_add_neg]

theorem triangleModularAction_generator₂_coe (z : ℍ) :
    (triangleModularAction triangleGenerator₂ z : ℂ) = -1 / z := by
  rw [triangleModularAction_generator₂_apply, UpperHalfPlane.coe_specialLinearGroup_apply]
  simp [ModularGroup.S]

@[simp] theorem triangleModularAction_cusp_apply (z : ℍ) :
    triangleModularAction triangleCuspGenerator z = (-1 : ℝ) +ᵥ z := by
  change modularPSLPermutation (triangleModularRepresentation triangleCuspGenerator) z = _
  rw [triangleModularRepresentation_cusp, modularPSLPermutation_projectivization]
  simpa using UpperHalfPlane.modular_T_zpow_smul z (-1)

theorem triangleModularAction_cusp_coe (z : ℍ) :
    (triangleModularAction triangleCuspGenerator z : ℂ) = z - 1 := by
  simp [sub_eq_add_neg, add_comm]

theorem triangleModularAction_cusp_zpow_apply (n : ℤ) (z : ℍ) :
    triangleModularAction (triangleCuspGenerator ^ n) z = (-(n : ℝ)) +ᵥ z := by
  change modularPSLPermutation (triangleModularRepresentation (triangleCuspGenerator ^ n)) z = _
  rw [map_zpow, triangleModularRepresentation_cusp, ← map_zpow,
    modularPSLPermutation_projectivization, inv_zpow, ← zpow_neg,
    UpperHalfPlane.modular_T_zpow_smul]
  simp

theorem triangleModularAction_cusp_zpow_coe (n : ℤ) (z : ℍ) :
    (triangleModularAction (triangleCuspGenerator ^ n) z : ℂ) = z - (n : ℂ) := by
  rw [triangleModularAction_cusp_zpow_apply]
  simp [sub_eq_add_neg, add_comm]

/-- Choosing the negative lift of the first projective generator makes
its cube the identity in `SL₂(ℤ)` itself. -/
theorem neg_triangleModularA_cube : (-triangleModularA) ^ 3 = 1 := by decide

theorem modularS_fourth : ModularGroup.S ^ 4 = 1 := by decide

theorem neg_triangleModularA_mul_S :
    (-triangleModularA) * ModularGroup.S = ModularGroup.T := by decide

/-- The integral special-linear lift with the sign convention of Lemma
9.14: the generators map to `-A` and `S`.  Its projectivization is the
modular representation; no canonical choice of signs for arbitrary
projective representations is asserted. -/
def triangleModularLinearRepresentation : TriangleGroup →* SL(2, ℤ) :=
  triangleLift (-triangleModularA) ModularGroup.S
    neg_triangleModularA_cube modularS_fourth

@[simp] theorem triangleModularLinearRepresentation_generator₁ :
    triangleModularLinearRepresentation triangleGenerator₁ = -triangleModularA :=
  triangleLift_generator₁ ..

@[simp] theorem triangleModularLinearRepresentation_generator₂ :
    triangleModularLinearRepresentation triangleGenerator₂ = ModularGroup.S :=
  triangleLift_generator₂ ..

theorem triangleModularLinearRepresentation_generator₁_matrix :
    (triangleModularLinearRepresentation triangleGenerator₁ : Matrix (Fin 2) (Fin 2) ℤ) =
      !![-1, 1; -1, 0] := by
  rw [triangleModularLinearRepresentation_generator₁]
  decide

theorem triangleModularLinearRepresentation_generator₂_matrix :
    (triangleModularLinearRepresentation triangleGenerator₂ : Matrix (Fin 2) (Fin 2) ℤ) =
      !![0, -1; 1, 0] := by
  rw [triangleModularLinearRepresentation_generator₂]
  rfl

@[simp] theorem triangleModularLinearRepresentation_cusp :
    triangleModularLinearRepresentation triangleCuspGenerator = ModularGroup.T⁻¹ := by
  rw [triangleModularLinearRepresentation, triangleLift_cusp, neg_triangleModularA_mul_S]

theorem triangleModularLinearRepresentation_cusp_matrix :
    (triangleModularLinearRepresentation triangleCuspGenerator : Matrix (Fin 2) (Fin 2) ℤ) =
      !![1, -1; 0, 1] := by
  rw [triangleModularLinearRepresentation_cusp, ModularGroup.coe_T_inv]

/-- Projectivization of the chosen integral lift is exactly the already
constructed modular representation. -/
theorem triangleModularLinearRepresentation_projectivization :
    modularProjectivization.comp triangleModularLinearRepresentation =
      triangleModularRepresentation := by
  apply triangle_hom_ext
  · simp [triangleModularGenerator₁]
  · simp [triangleModularGenerator₂]

@[simp] theorem modularProjectivization_triangleModularLinearRepresentation (g : TriangleGroup) :
    modularProjectivization (triangleModularLinearRepresentation g) =
      triangleModularRepresentation g :=
  DFunLike.congr_fun triangleModularLinearRepresentation_projectivization g

end Wikipedia.HopfProblem.SpecialPeriods
