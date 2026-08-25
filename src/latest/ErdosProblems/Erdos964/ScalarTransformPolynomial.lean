import ErdosProblems.Erdos964.ScalarTransformAsymptotic

/-!
# A polynomial model for the scalar transform, including its zero region
-/

namespace Erdos964

open BoundedGaps.Maynard

noncomputable def scalarTransformPolynomial (R r : ℕ) : ℝ :=
  if 1 ≤ r ∧ r < R then Real.log R *
    ggpyPolynomialPrimitive (1 - Real.log r / Real.log R) else 0

theorem scalarTransformPolynomial_eq_zero (R r : ℕ) (hr : R ≤ r) :
    scalarTransformPolynomial R r = 0 := if_neg (fun h => hr.not_gt h.2)

theorem scalarTransformPolynomial_eq_primitive (R r : ℕ) (hr : 0 < r) (hrR : r < R) :
    scalarTransformPolynomial R r =
      Real.log R * ggpyPolynomialPrimitive (Real.log ((R : ℝ) / r) / Real.log R) := by
  have hR : (1 : ℝ) < R := by exact_mod_cast (show 1 < R by omega)
  have hL := Real.log_pos hR
  have hrpos : (0 : ℝ) < r := by exact_mod_cast hr
  rw [scalarTransformPolynomial, if_pos (show 1 ≤ r ∧ r < R from ⟨hr, hrR⟩),
    Real.log_div (by linarith : (R : ℝ) ≠ 0) hrpos.ne']
  congr 2
  field_simp

theorem scalarTransformPolynomial_bounds (R r : ℕ) (hL : 0 < Real.log R) :
    0 ≤ scalarTransformPolynomial R r ∧ scalarTransformPolynomial R r ≤ 4 * Real.log R := by
  rw [scalarTransformPolynomial]
  split_ifs with hr
  · have hrpos : (0 : ℝ) < r := by exact_mod_cast hr.1
    have hlogr := Real.log_natCast_nonneg r
    have hlogrL : Real.log r ≤ Real.log R :=
      Real.log_le_log hrpos (by exact_mod_cast hr.2.le)
    have hratio0 : 0 ≤ Real.log r / Real.log R := div_nonneg hlogr hL.le
    have hratio1 : Real.log r / Real.log R ≤ 1 := (div_le_one hL).mpr hlogrL
    have hx0 : 0 ≤ 1 - Real.log r / Real.log R := by linarith
    have hx1 : 1 - Real.log r / Real.log R ≤ 1 := by linarith
    have hx2 : (1 - Real.log r / Real.log R) ^ 2 ≤ 1 := pow_le_one₀ hx0 hx1
    have hprim0 : 0 ≤ ggpyPolynomialPrimitive (1 - Real.log r / Real.log R) := by
      unfold ggpyPolynomialPrimitive
      positivity
    have hprim4 : ggpyPolynomialPrimitive (1 - Real.log r / Real.log R) ≤ 4 := by
      unfold ggpyPolynomialPrimitive
      linarith
    refine ⟨mul_nonneg hL.le hprim0, ?_⟩
    nlinarith [mul_le_mul_of_nonneg_left hprim4 hL.le]
  · exact ⟨le_rfl, by positivity⟩

noncomputable def scalarTransformErrorEnvelope (M R : ℕ) (K C : ℝ) : ℝ :=
  81 * coprimeHarmonicDensity M *
    (K + primeLogDivisorMass M + (Real.log (Real.log R) + C + 2) + Real.log 2)

theorem scalarTransformErrorEnvelope_nonneg (M R : ℕ) (K C : ℝ)
    (hK : 0 ≤ K) (hC : 0 ≤ C) (hR : 2 ≤ Real.log R) :
    0 ≤ scalarTransformErrorEnvelope M R K C := by
  have hmass : 0 ≤ primeLogDivisorMass M := by unfold primeLogDivisorMass; positivity
  have hloglog : 0 ≤ Real.log (Real.log R) := Real.log_nonneg (by linarith)
  unfold scalarTransformErrorEnvelope coprimeHarmonicDensity
  positivity

theorem exists_uniform_scalar_transform_polynomial_error :
    ∃ K C : ℝ, 0 < K ∧ 0 ≤ C ∧ ∀ M R r : ℕ,
      0 < M → 2 ≤ Real.log R → Squarefree r → r.Coprime M →
      |scalarSemiprimeTransform (scalarSievePrimeProduct M R) (scalarLinearY R) r -
        coprimeHarmonicDensity M * scalarTransformPolynomial R r| ≤
        scalarTransformErrorEnvelope M R K C := by
  obtain ⟨K, C, hK, hC, hbound⟩ := exists_uniform_scalar_transform_primitive_error
  refine ⟨K, C, hK, hC, ?_⟩
  intro M R r hM hR hrsq hrM
  by_cases hrR : r < R
  · have hrP := (dvd_scalarSievePrimeProduct_iff M R r hrR.le).mpr ⟨hrsq, hrM⟩
    have h := hbound M R r hM hrP hrR hR
    rw [scalarTransformPolynomial_eq_primitive R r (Nat.pos_of_ne_zero hrsq.ne_zero) hrR]
    simpa only [scalarTransformErrorEnvelope, mul_assoc] using h
  · have hRr : R ≤ r := Nat.le_of_not_gt hrR
    rw [scalarTransformPolynomial_eq_zero R r hRr,
      scalarSemiprimeTransform_eq_zero_of_radius (scalarSievePrimeProduct M R) R
        (scalarLinearY R) (scalarLinearY_eq_zero_of_radius R) r hRr,
      mul_zero, sub_self, abs_zero]
    exact scalarTransformErrorEnvelope_nonneg M R K C hK.le hC hR

end Erdos964
