import ErdosProblems.Erdos67b.MRTypicalCofactorPerron

/-!
# Exact finite-prefix Perron error for the typical cofactor

The actual tailored coefficient is summable on the moving line. Its
inclusive prefix therefore differs from the Perron transform by the
explicit near mass, total mass, and half-endpoint terms.
-/

open scoped BigOperators LSeries.notation

namespace Erdos67b

open MRHalaszBands MRHalaszEuler EulerResidue BoundedGaps.Maynard

noncomputable section

theorem mrTypicalCofactorTailored_LSeriesSummable {ι : Type*}
    (A : Finset ℕ) (J : Finset ι) (B : ι → Finset ℕ)
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (y X : ℕ) (alpha beta : ℝ) {s : ℂ}
    (hlow : 0 < s.re) (hhigh : 1 < (s + ((alpha + 2 * beta : ℝ) : ℂ)).re) :
    LSeriesSummable (mrTypicalCofactorTailoredCoefficient A J B f hmul y X alpha beta) s := by
  exact gsA10TailoredCoefficient_LSeriesSummable _ _ _ y X alpha beta s
    (mrTypicalCofactorLowArithmetic_LSeriesSummable_of_pos_re A J B hbound y hlow)
    (gsA9HighArithmetic_LSeriesSummable hbound y hhigh)

theorem mrNorm_positivePrefix_typicalCofactorTailored_sub_perron_le {ι : Type*}
    (A : Finset ℕ) (J : Finset ι) (B : ι → Finset ℕ)
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {X y : ℕ} (hX : 1 < X) {alpha beta T : ℝ}
    (hsigma : 0 < taoExponent X - alpha - 2 * beta)
    (hupper : taoExponent X - alpha - 2 * beta ≤ 2) (hT : 0 < T) :
    let a := mrTypicalCofactorTailoredCoefficient A J B f hmul y X alpha beta
    let sigma := taoExponent X - alpha - 2 * beta
    ‖positivePrefixSum a X - mrTypicalCofactorMovingPerronIntegral A J B f hmul y X alpha beta T‖ ≤
      dirichletPerronNearMass a X T +
        (32 * (X : ℝ) ^ sigma / T) * dirichletPerronCoefficientMass a sigma +
        (1 / 2 : ℝ) * ‖a X‖ := by
  dsimp only
  have hsum := mrTypicalCofactorTailored_LSeriesSummable A J B hmul hbound y X alpha beta
    (s := ((taoExponent X - alpha - 2 * beta : ℝ) : ℂ)) (by simpa using hsigma) (by
      simp only [Complex.add_re, Complex.ofReal_re]
      have hc := one_lt_taoExponent hX
      linarith)
  apply norm_positivePrefixSum_sub_le_of_starred_sub_le (by omega)
  exact norm_dirichletPerronStarredSum_sub_integral_le hsum (by omega) hsigma hupper hT

/-- The source rectangle discharges the line conditions. The exact moving
power remains adjacent to the absolute coefficient mass. -/
theorem mrNorm_positivePrefix_typicalCofactorTailored_sub_perron_le_source {ι : Type*}
    (A : Finset ℕ) (J : Finset ι) (B : ι → Finset ℕ)
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {X y : ℕ} (hX : 1 < X) (hlogX : 1 ≤ Real.log (X : ℝ))
    (hlogy : 6 ≤ Real.log (y : ℝ)) {alpha beta T : ℝ}
    (ha0 : 0 ≤ alpha) (ha : alpha ≤ (Real.log (y : ℝ))⁻¹)
    (hb0 : 0 ≤ beta) (hb : beta ≤ (Real.log (y : ℝ))⁻¹) (hT : 0 < T) :
    let a := mrTypicalCofactorTailoredCoefficient A J B f hmul y X alpha beta
    let sigma := taoExponent X - alpha - 2 * beta
    ‖positivePrefixSum a X - mrTypicalCofactorMovingPerronIntegral A J B f hmul y X alpha beta T‖ ≤
      dirichletPerronNearMass a X T +
        (32 * (X : ℝ) ^ sigma / T) * dirichletPerronCoefficientMass a sigma +
        (1 / 2 : ℝ) * ‖a X‖ := by
  have hc := one_lt_taoExponent hX
  have hiy : (Real.log (y : ℝ))⁻¹ ≤ 1 / 6 := by
    simpa only [one_div] using inv_anti₀ (by norm_num : (0 : ℝ) < 6) hlogy
  have hc2 : taoExponent X ≤ 2 := by
    unfold taoExponent
    have hh := (inv_le_one₀ (zero_lt_one.trans_le hlogX)).mpr hlogX
    linarith
  exact mrNorm_positivePrefix_typicalCofactorTailored_sub_perron_le A J B hmul hbound hX
    (by linarith) (by linarith) hT

end

end Erdos67b
