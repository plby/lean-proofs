import Wikipedia.HopfProblem.SpecialPeriodsTriangleDiscrete
import Wikipedia.HopfProblem.SpecialPeriodsTriangleShimizuMatrices
import Wikipedia.HopfProblem.SpecialPeriodsTriangleCuspPrimitive
import Wikipedia.HopfProblem.SpecialPeriodsTriangleTranslations
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine

/-!
# The stabilizer of the actual triangle cusp

This file identifies the subgroup fixing the ideal cusp of the explicit
triangle action.  It uses the inherited discreteness of the generated
matrix subgroup and the proved primitivity of the abstract cusp element.
No precise-invariance or cusp-stabilizer assertion is assumed.
-/

noncomputable section

open Function Set Matrix UpperHalfPlane OnePoint
open scoped MatrixGroups Topology

namespace Wikipedia.HopfProblem.SpecialPeriods.Triangle

theorem upperTriangular_det (A : SL(2, ℝ)) (hc : A 1 0 = 0) :
    A 0 0 * A 1 1 = 1 := by
  have hdet : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 :=
    (Matrix.det_fin_two A.val).symm.trans A.property
  simpa only [hc, mul_zero, sub_zero] using hdet

theorem upperTriangular_zero_zero_ne_zero (A : SL(2, ℝ)) (hc : A 1 0 = 0) :
    A 0 0 ≠ 0 := by
  intro ha
  have h := upperTriangular_det A hc
  simp [ha] at h

theorem upperTriangular_one_one_ne_zero (A : SL(2, ℝ)) (hc : A 1 0 = 0) :
    A 1 1 ≠ 0 := by
  intro hd
  have h := upperTriangular_det A hc
  simp [hd] at h

/-- Conjugation by an upper-triangular determinant-one matrix scales
translation lengths by the square of its first diagonal entry. -/
theorem upperTriangular_conjugate_translation (A : SL(2, ℝ))
    (hc : A 1 0 = 0) (t : ℝ) :
    A * shimizuTranslation t * A⁻¹ = shimizuTranslation (t * (A 0 0) ^ 2) := by
  apply Subtype.ext
  rw [shimizu_conjugate_matrix, coe_shimizuTranslation]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hc]

theorem upperTriangular_inverse_lower_left (A : SL(2, ℝ)) (hc : A 1 0 = 0) :
    (A⁻¹ : SL(2, ℝ)) 1 0 = 0 := by
  change (Matrix.adjugate (A : Matrix (Fin 2) (Fin 2) ℝ)) 1 0 = 0
  simp [Matrix.adjugate_fin_two, hc]

theorem inverse_upper_left (A : SL(2, ℝ)) : (A⁻¹ : SL(2, ℝ)) 0 0 = A 1 1 := by
  change (Matrix.adjugate (A : Matrix (Fin 2) (Fin 2) ℝ)) 0 0 = A 1 1
  simp [Matrix.adjugate_fin_two]

private theorem neg_one_mul_realSL (A : SL(2, ℝ)) : (-1 : SL(2, ℝ)) * A = -A := by
  apply Subtype.ext
  change (-1 : Matrix (Fin 2) (Fin 2) ℝ) * A = -(A : Matrix (Fin 2) (Fin 2) ℝ)
  simp

theorem realSLPermutation_neg (A : SL(2, ℝ)) : realSLPermutation (-A) = realSLPermutation A := by
  rw [← neg_one_mul_realSL, map_mul, realSLPermutation_neg_one, one_mul]

/-- Two determinant-one real matrices induce the same actual Möbius
transformation precisely when they differ by their central sign. -/
theorem realSLPermutation_eq_iff (A B : SL(2, ℝ)) :
    realSLPermutation A = realSLPermutation B ↔ A = B ∨ A = -B := by
  constructor
  · intro h
    have hk : realSLPermutation (A * B⁻¹) = 1 := by
      rw [map_mul, map_inv, h, mul_inv_cancel]
    rcases (realSLPermutation_eq_one_iff _).mp hk with hk | hk
    · exact Or.inl (mul_inv_eq_one.mp hk)
    · right
      have he := congrArg (fun C : SL(2, ℝ) => C * B) hk
      simpa only [mul_assoc, inv_mul_cancel, mul_one, neg_one_mul_realSL] using he
  · rintro (rfl | rfl)
    · rfl
    · exact realSLPermutation_neg B

/-- Every matrix lift of a generated Möbius transformation belongs to
the actual generated matrix group, since both central signs belong. -/
theorem matrixGroup_of_permutation_mem_range (A : SL(2, ℝ))
    (h : realSLPermutation A ∈ triangleGeometricRepresentation.range) : A ∈ matrixGroup := by
  obtain ⟨g, hg⟩ := h
  obtain ⟨B, hB⟩ := triangleGeometricRepresentation_matrixGroup_lift g
  rcases (realSLPermutation_eq_iff A B).mp (hg.symm.trans hB.symm) with he | he
  · rw [he]
    exact B.property
  · rw [he, ← neg_one_mul_realSL]
    exact matrixGroup.mul_mem neg_one_mem_matrixGroup B.property

theorem same_permutation_lower_left_zero_iff (A B : SL(2, ℝ))
    (h : realSLPermutation A = realSLPermutation B) : A 1 0 = 0 ↔ B 1 0 = 0 := by
  rcases (realSLPermutation_eq_iff A B).mp h with rfl | rfl
  · rfl
  · change -(B 1 0) = 0 ↔ B 1 0 = 0
    exact neg_eq_zero

/-- The proved cusp width is the primitive generator of the actual
translation subgroup.  A smaller generator would give a proper root of
the abstract cusp element, contradicting the integral representation. -/
theorem matrixGroup_translationSubgroup_eq :
    translationSubgroup matrixGroup = AddSubgroup.zmultiples width := by
  obtain ⟨t, ht⟩ := translationSubgroup_cyclic matrixGroup
  have ht_mem : shimizuTranslation t ∈ matrixGroup := by
    change t ∈ translationSubgroup matrixGroup
    rw [ht]
    exact AddSubgroup.mem_zmultiples t
  have hw := neg_width_mem_translationSubgroup_matrixGroup
  rw [ht, AddSubgroup.mem_zmultiples_iff] at hw
  obtain ⟨k, hk⟩ := hw
  obtain ⟨g, hg⟩ := matrixGroup_permutation_lift (shimizuTranslation t) ht_mem
  have hroot : g ^ k = triangleCuspGenerator := by
    apply triangleGeometricRepresentation_injective
    rw [map_zpow, hg, ← map_zpow, shimizuTranslation_zpow]
    have hk' : (k : ℝ) * t = -width := by simpa only [zsmul_eq_mul] using hk
    rw [hk', shimizuTranslation_neg_width]
    exact triangleGeometricRepresentation_cusp.symm
  have hk_abs := triangleCuspGenerator_zpow_root_exponent g k hroot
  have hk_cases : k = 1 ∨ k = -1 := by omega
  rcases hk_cases with rfl | rfl
  · have ht' : t = -width := by simpa using hk
    rw [ht, ht', AddSubgroup.zmultiples_neg]
  · have ht' : t = width := by simpa using congrArg Neg.neg hk
    rw [ht, ht']

/-- Every pure translation in the generated real matrix group has an
integer multiple of the original cusp width. -/
theorem shimizuTranslation_mem_matrixGroup_iff (t : ℝ) :
    shimizuTranslation t ∈ matrixGroup ↔ ∃ n : ℤ, t = (n : ℝ) * width := by
  change t ∈ translationSubgroup matrixGroup ↔ _
  rw [matrixGroup_translationSubgroup_eq, AddSubgroup.mem_zmultiples_iff]
  simp only [zsmul_eq_mul, eq_comm]

private theorem upperTriangular_square_is_integer (A : SL(2, ℝ))
    (hA : A ∈ matrixGroup) (hc : A 1 0 = 0) : ∃ n : ℤ, (A 0 0) ^ 2 = (n : ℝ) := by
  have hT : shimizuTranslation width ∈ matrixGroup :=
    width_mem_translationSubgroup_matrixGroup
  have hconj := matrixGroup.mul_mem (matrixGroup.mul_mem hA hT) (matrixGroup.inv_mem hA)
  rw [upperTriangular_conjugate_translation A hc width] at hconj
  obtain ⟨n, hn⟩ := (shimizuTranslation_mem_matrixGroup_iff _).mp hconj
  refine ⟨n, mul_left_cancel₀ width_ne_zero ?_⟩
  simpa only [mul_comm] using hn

/-- An upper-triangular element of the actual discrete matrix group
cannot dilate the cusp: its first diagonal entry has square one. -/
theorem matrixGroup_upperTriangular_square_eq_one (A : SL(2, ℝ))
    (hA : A ∈ matrixGroup) (hc : A 1 0 = 0) : (A 0 0) ^ 2 = 1 := by
  obtain ⟨m, hm⟩ := upperTriangular_square_is_integer A hA hc
  obtain ⟨n, hn⟩ := upperTriangular_square_is_integer A⁻¹ (matrixGroup.inv_mem hA)
    (upperTriangular_inverse_lower_left A hc)
  rw [inverse_upper_left] at hn
  have hmpos : (0 : ℤ) < m := by
    have hp : (0 : ℝ) < (m : ℝ) := by
      rw [← hm]
      exact sq_pos_of_ne_zero (upperTriangular_zero_zero_ne_zero A hc)
    exact_mod_cast hp
  have hnpos : (0 : ℤ) < n := by
    have hp : (0 : ℝ) < (n : ℝ) := by
      rw [← hn]
      exact sq_pos_of_ne_zero (upperTriangular_one_one_ne_zero A hc)
    exact_mod_cast hp
  have hmn : m * n = 1 := by
    have he : (m : ℝ) * (n : ℝ) = 1 := by
      rw [← hm, ← hn, ← mul_pow, upperTriangular_det A hc, one_pow]
    exact_mod_cast he
  have hm1 : (1 : ℤ) ≤ m := by omega
  have hn1 : (1 : ℤ) ≤ n := by omega
  have hprod : 0 ≤ m * (n - 1) := mul_nonneg hmpos.le (sub_nonneg.mpr hn1)
  have hm_eq : m = 1 := by nlinarith [hmn]
  rw [hm, hm_eq, Int.cast_one]

private theorem upperTriangular_eq_signed_translation (A : SL(2, ℝ))
    (hc : A 1 0 = 0) (ha : (A 0 0) ^ 2 = 1) :
    A = shimizuTranslation (A 0 0 * A 0 1) ∨
      A = -shimizuTranslation (A 0 0 * A 0 1) := by
  have hdet := upperTriangular_det A hc
  rcases sq_eq_one_iff.mp ha with ha | ha
  · have hd : A 1 1 = 1 := by simpa [ha] using hdet
    left
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [coe_shimizuTranslation, ha, hd, hc]
  · have hd : A 1 1 = -1 := by rw [ha] at hdet; linarith
    right
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [coe_shimizuTranslation, ha, hd, hc]

private theorem translation_int_width_eq_cusp_zpow (n : ℤ) :
    shimizuTranslation ((n : ℝ) * width) = cuspSL ^ (-n) := by
  rw [← shimizuTranslation_neg_width, shimizuTranslation_zpow]
  simp

/-- The upper-triangular part of the generated real matrix group consists
exactly of cusp powers and their central negatives. -/
theorem matrixGroup_upperTriangular_iff (A : SL(2, ℝ)) (hA : A ∈ matrixGroup) :
    A 1 0 = 0 ↔ ∃ n : ℤ, A = cuspSL ^ n ∨ A = -(cuspSL ^ n) := by
  constructor
  · intro hc
    have hs := upperTriangular_eq_signed_translation A hc
      (matrixGroup_upperTriangular_square_eq_one A hA hc)
    have ht : shimizuTranslation (A 0 0 * A 0 1) ∈ matrixGroup := by
      rcases hs with he | he
      · exact he ▸ hA
      · have hneg : -A ∈ matrixGroup := by
          rw [← neg_one_mul_realSL]
          exact matrixGroup.mul_mem neg_one_mem_matrixGroup hA
        have he' := congrArg (fun B : SL(2, ℝ) => -B) he
        rw [neg_neg] at he'
        exact he' ▸ hneg
    obtain ⟨n, hn⟩ := (shimizuTranslation_mem_matrixGroup_iff _).mp ht
    refine ⟨-n, ?_⟩
    simpa only [hn, translation_int_width_eq_cusp_zpow] using hs
  · rintro ⟨n, rfl | rfl⟩
    · rw [← shimizuTranslation_neg_width, shimizuTranslation_zpow]
      rfl
    · change -((cuspSL ^ n) 1 0) = 0
      rw [← shimizuTranslation_neg_width, shimizuTranslation_zpow]
      simp [shimizuTranslation]

theorem matrixGroup_upperTriangular_permutation (A : SL(2, ℝ))
    (hA : A ∈ matrixGroup) (hc : A 1 0 = 0) :
    ∃ n : ℤ, realSLPermutation A =
      triangleGeometricRepresentation (triangleCuspGenerator ^ n) := by
  obtain ⟨n, he | he⟩ := (matrixGroup_upperTriangular_iff A hA).mp hc
  · refine ⟨n, ?_⟩
    rw [he, map_zpow, map_zpow, triangleGeometricRepresentation_cusp]
  · refine ⟨n, ?_⟩
    rw [he, realSLPermutation_neg, map_zpow, map_zpow, triangleGeometricRepresentation_cusp]

/-- Thus every upper-triangular matrix in the actual group acts by an
integer translation of exactly the original cusp width. -/
theorem matrixGroup_upperTriangular_smul (A : SL(2, ℝ))
    (hA : A ∈ matrixGroup) (hc : A 1 0 = 0) :
    ∃ n : ℤ, ∀ z : ℍ, A • z = (-(n : ℝ) * width) +ᵥ z := by
  obtain ⟨n, hn⟩ := matrixGroup_upperTriangular_permutation A hA hc
  refine ⟨n, fun z => ?_⟩
  change realSLPermutation A z = _
  rw [hn, triangleGeometricRepresentation_cusp_zpow_apply]

/-- An abstract triangle element with an upper-triangular real lift is
exactly an integer power of the original cusp element. -/
theorem triangleGeometric_upperTriangular_lift_iff (g : TriangleGroup) (A : SL(2, ℝ))
    (hA : realSLPermutation A = triangleGeometricRepresentation g) :
    A 1 0 = 0 ↔ g ∈ Subgroup.zpowers triangleCuspGenerator := by
  constructor
  · intro hc
    have hmem : A ∈ matrixGroup := matrixGroup_of_permutation_mem_range A ⟨g, hA.symm⟩
    obtain ⟨n, hn⟩ := matrixGroup_upperTriangular_permutation A hmem hc
    exact Subgroup.mem_zpowers_iff.mpr
      ⟨n, triangleGeometricRepresentation_injective (hn.symm.trans hA)⟩
  · intro hg
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    have he : realSLPermutation A = realSLPermutation (cuspSL ^ n) := by
      rw [hA, map_zpow, map_zpow, triangleGeometricRepresentation_cusp]
    apply (same_permutation_lower_left_zero_iff _ _ he).mpr
    rw [← shimizuTranslation_neg_width, shimizuTranslation_zpow]
    rfl

/-- The actual ideal-point stabilizer is precisely the cusp subgroup,
expressed independently of the sign of the chosen special-linear lift. -/
theorem triangle_stabilizer_infty_iff (g : TriangleGroup) (A : SL(2, ℝ))
    (hA : realSLPermutation A = triangleGeometricRepresentation g) :
    Matrix.SpecialLinearGroup.mapGL ℝ A • (∞ : OnePoint ℝ) = ∞ ↔
      g ∈ Subgroup.zpowers triangleCuspGenerator := by
  rw [OnePoint.smul_infty_eq_self_iff]
  change A 1 0 = 0 ↔ _
  exact triangleGeometric_upperTriangular_lift_iff g A hA

theorem triangle_lower_left_ne_zero_of_not_mem_cusp (g : TriangleGroup) (A : SL(2, ℝ))
    (hA : realSLPermutation A = triangleGeometricRepresentation g)
    (hg : g ∉ Subgroup.zpowers triangleCuspGenerator) : A 1 0 ≠ 0 :=
  fun hc => hg ((triangleGeometric_upperTriangular_lift_iff g A hA).mp hc)

end Wikipedia.HopfProblem.SpecialPeriods.Triangle
