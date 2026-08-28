import Wikipedia.HopfProblem.SpecialPeriodsTrianglePresentation
import Wikipedia.HopfProblem.SpecialPeriodsTriangleMatrices
import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
import Mathlib.Algebra.Group.Action.End

/-!
# The actual Möbius action of the abstract triangle group

The explicit real matrices satisfy the triangle relations modulo the
central sign, which acts trivially on the actual upper half-plane.  Their
permutations therefore define a homomorphism from the constructed free
product.  The cusp element translates by `-(1 + sqrt 2)`, and its integer
powers have an explicit translation formula.  This proves that the cusp
has infinite order without assuming that the whole action is faithful.
-/

noncomputable section

open Function Set UpperHalfPlane
open scoped MatrixGroups

namespace Wikipedia.HopfProblem.SpecialPeriods

namespace Triangle

/-- The actual Möbius action of determinant-one real matrices, bundled
as a homomorphism into permutations of the upper half-plane. -/
def realSLPermutation : SL(2, ℝ) →* Equiv.Perm ℍ :=
  MulAction.toPermHom (SL(2, ℝ)) ℍ

@[simp] theorem realSLPermutation_apply (A : SL(2, ℝ)) (z : ℍ) :
    realSLPermutation A z = A • z := rfl

/-- The central sign disappears in the actual Möbius action. -/
@[simp] theorem realSLPermutation_neg_one : realSLPermutation (-1) = 1 := by
  apply Equiv.ext
  intro z
  apply UpperHalfPlane.ext
  change (((-1 : SL(2, ℝ)) • z : ℍ) : ℂ) = z
  norm_num [UpperHalfPlane.coe_specialLinearGroup_apply,
    Matrix.SpecialLinearGroup.coe_neg,
    Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply]

def generatorOnePerm : Equiv.Perm ℍ := realSLPermutation generatorOneSL

def generatorTwoPerm : Equiv.Perm ℍ := realSLPermutation generatorTwoSL

theorem generatorOnePerm_cube : generatorOnePerm ^ 3 = 1 := by
  rw [generatorOnePerm, ← map_pow, generatorOneSL_cube, realSLPermutation_neg_one]

theorem generatorTwoPerm_fourth : generatorTwoPerm ^ 4 = 1 := by
  rw [generatorTwoPerm, ← map_pow, generatorTwoSL_fourth, realSLPermutation_neg_one]

/-- Real horizontal translations as an actual homomorphism of groups. -/
def horizontalTranslation : Multiplicative ℝ →* Equiv.Perm ℍ :=
  (AddAction.toPermHom ℝ ℍ).toMultiplicativeLeft

@[simp] theorem horizontalTranslation_apply (t : ℝ) (z : ℍ) :
    horizontalTranslation (Multiplicative.ofAdd t) z = t +ᵥ z := rfl

theorem cuspSL_apply (z : ℍ) : cuspSL • z = (-width) +ᵥ z := by
  apply UpperHalfPlane.ext
  simp [UpperHalfPlane.coe_specialLinearGroup_apply,
    coe_cuspSL, add_comm]

theorem cuspSL_permutation_eq_translation :
    realSLPermutation cuspSL = horizontalTranslation (Multiplicative.ofAdd (-width)) := by
  apply Equiv.ext
  exact cuspSL_apply

end Triangle

/-- The geometric representation of the genuine abstract free product,
obtained from the actual Möbius permutations. -/
def triangleGeometricRepresentation : TriangleGroup →* Equiv.Perm ℍ :=
  triangleLift Triangle.generatorOnePerm Triangle.generatorTwoPerm
    Triangle.generatorOnePerm_cube Triangle.generatorTwoPerm_fourth

/-- The corresponding group action, available as a named instance for
geometric statements about the abstract triangle group. -/
@[instance_reducible] def triangleGeometricAction : MulAction TriangleGroup ℍ :=
  MulAction.compHom ℍ triangleGeometricRepresentation

theorem triangleGeometricAction_smul (g : TriangleGroup) (z : ℍ) :
    letI := triangleGeometricAction
    g • z = triangleGeometricRepresentation g z := rfl

@[simp] theorem triangleGeometricRepresentation_generator₁ :
    triangleGeometricRepresentation triangleGenerator₁ = Triangle.generatorOnePerm :=
  triangleLift_generator₁ ..

@[simp] theorem triangleGeometricRepresentation_generator₂ :
    triangleGeometricRepresentation triangleGenerator₂ = Triangle.generatorTwoPerm :=
  triangleLift_generator₂ ..

@[simp] theorem triangleGeometricRepresentation_generator₁_apply (z : ℍ) :
    triangleGeometricRepresentation triangleGenerator₁ z = Triangle.generatorOneSL • z := by
  rw [triangleGeometricRepresentation_generator₁]
  rfl

@[simp] theorem triangleGeometricRepresentation_generator₂_apply (z : ℍ) :
    triangleGeometricRepresentation triangleGenerator₂ z = Triangle.generatorTwoSL • z := by
  rw [triangleGeometricRepresentation_generator₂]
  rfl

/-- Every element of the constructed action is represented by an actual
determinant-one real matrix.  The representative need not be unique. -/
theorem triangleGeometricRepresentation_has_SL_lift (g : TriangleGroup) :
    ∃ A : SL(2, ℝ), Triangle.realSLPermutation A = triangleGeometricRepresentation g := by
  have hr : triangleGeometricRepresentation.range ≤ Triangle.realSLPermutation.range := by
    rw [triangle_range]
    apply (Subgroup.closure_le _).mpr
    intro p hp
    rcases hp with rfl | rfl
    · exact ⟨Triangle.generatorOneSL, triangleGeometricRepresentation_generator₁.symm⟩
    · exact ⟨Triangle.generatorTwoSL, triangleGeometricRepresentation_generator₂.symm⟩
  exact hr ⟨g, rfl⟩

theorem triangleGeometricRepresentation_cusp :
    triangleGeometricRepresentation triangleCuspGenerator =
      Triangle.realSLPermutation Triangle.cuspSL := by
  rw [triangleGeometricRepresentation, triangleLift_cusp,
    Triangle.generatorOnePerm, Triangle.generatorTwoPerm, ← map_mul,
    Triangle.generatorOneSL_mul_generatorTwoSL, ← map_inv]
  rfl

theorem triangleGeometricRepresentation_cusp_eq_translation :
    triangleGeometricRepresentation triangleCuspGenerator =
      Triangle.horizontalTranslation (Multiplicative.ofAdd (-Triangle.width)) :=
  triangleGeometricRepresentation_cusp.trans Triangle.cuspSL_permutation_eq_translation

@[simp] theorem triangleGeometricRepresentation_cusp_apply (z : ℍ) :
    triangleGeometricRepresentation triangleCuspGenerator z = (-Triangle.width) +ᵥ z := by
  rw [triangleGeometricRepresentation_cusp_eq_translation]
  rfl

/-- The exact source-normalized cusp translation in complex coordinates. -/
theorem triangleGeometricRepresentation_cusp_coe (z : ℍ) :
    (triangleGeometricRepresentation triangleCuspGenerator z : ℂ) = z - Triangle.width := by
  simp [sub_eq_add_neg, add_comm]

/-- Every integral cusp iterate is the corresponding horizontal
translation, including negative iterates. -/
theorem triangleGeometricRepresentation_cusp_zpow_apply (n : ℤ) (z : ℍ) :
    triangleGeometricRepresentation (triangleCuspGenerator ^ n) z =
      (-(n : ℝ) * Triangle.width) +ᵥ z := by
  rw [map_zpow, triangleGeometricRepresentation_cusp_eq_translation,
    ← map_zpow, ← ofAdd_zsmul, Triangle.horizontalTranslation_apply]
  congr 1
  simp only [zsmul_eq_mul, mul_neg, neg_mul]

theorem triangleGeometricRepresentation_cusp_zpow_coe (n : ℤ) (z : ℍ) :
    (triangleGeometricRepresentation (triangleCuspGenerator ^ n) z : ℂ) =
      z - (n : ℂ) * Triangle.width := by
  rw [triangleGeometricRepresentation_cusp_zpow_apply, UpperHalfPlane.coe_vadd]
  push_cast
  ring

theorem triangleGeometricRepresentation_cusp_pow_apply (n : ℕ) (z : ℍ) :
    triangleGeometricRepresentation (triangleCuspGenerator ^ n) z =
      (-(n : ℝ) * Triangle.width) +ᵥ z := by
  simpa only [zpow_natCast, Int.cast_natCast] using
    triangleGeometricRepresentation_cusp_zpow_apply (n : ℤ) z

theorem triangleGeometricRepresentation_cusp_zpow_eq_one_iff (n : ℤ) :
    triangleGeometricRepresentation (triangleCuspGenerator ^ n) = 1 ↔ n = 0 := by
  constructor
  · intro h
    have he := congrArg (fun f : Equiv.Perm ℍ => (f UpperHalfPlane.I).re) h
    rw [triangleGeometricRepresentation_cusp_zpow_apply] at he
    have hn : -(n : ℝ) * Triangle.width = 0 := by simpa using he
    have hn₀ : (n : ℝ) = 0 :=
      neg_eq_zero.mp ((mul_eq_zero.mp hn).resolve_right Triangle.width_ne_zero)
    exact_mod_cast hn₀
  · rintro rfl
    simp

theorem triangleCuspGenerator_zpow_eq_one_iff (n : ℤ) :
    triangleCuspGenerator ^ n = 1 ↔ n = 0 := by
  constructor
  · intro h
    apply (triangleGeometricRepresentation_cusp_zpow_eq_one_iff n).mp
    rw [h, map_one]
  · rintro rfl
    simp

theorem triangleCuspGenerator_pow_eq_one_iff (n : ℕ) :
    triangleCuspGenerator ^ n = 1 ↔ n = 0 := by
  simpa using triangleCuspGenerator_zpow_eq_one_iff (n : ℤ)

/-- The cusp element has infinite order in the actual abstract free
product, as witnessed by its nontrivial translations. -/
theorem triangleCuspGenerator_order : orderOf triangleCuspGenerator = 0 := by
  apply orderOf_eq_zero_iff'.mpr
  intro n hn h
  exact hn.ne' ((triangleCuspGenerator_pow_eq_one_iff n).mp h)

theorem triangleGeometricRepresentation_cusp_order :
    orderOf (triangleGeometricRepresentation triangleCuspGenerator) = 0 := by
  apply orderOf_eq_zero_iff'.mpr
  intro n hn h
  have he : triangleGeometricRepresentation (triangleCuspGenerator ^ (n : ℤ)) = 1 := by
    simpa only [zpow_natCast, map_pow] using h
  have hn₀ := (triangleGeometricRepresentation_cusp_zpow_eq_one_iff (n : ℤ)).mp he
  exact hn.ne' (by exact_mod_cast hn₀)

/-- Every cusp orbit contains distinct points for distinct integer
iterates.  This only uses the explicit translation, not faithfulness of
the whole triangle action. -/
theorem triangleGeometricRepresentation_cusp_orbit_injective (z : ℍ) :
    Function.Injective (fun n : ℤ =>
      triangleGeometricRepresentation (triangleCuspGenerator ^ n) z) := by
  intro m n h
  simp only [triangleGeometricRepresentation_cusp_zpow_apply] at h
  have he := (UpperHalfPlane.vadd_right_cancel_iff z).mp h
  have hmn := neg_injective (mul_right_cancel₀ Triangle.width_ne_zero he)
  exact_mod_cast hmn

end Wikipedia.HopfProblem.SpecialPeriods
