import ErdosProblems.Erdos67b.MRTypicalCofactorWeightedAverage

/-!
# Transfer from an actual cofactor envelope to its Perron contour

The two transfers isolate the linear use of a proved low/high bound and
of a proved pointwise contour bound. Source instances discharge those
hypotheses with the actual cofactor estimates.
-/

open scoped BigOperators Classical LSeries.notation
open Complex Set MeasureTheory

namespace Erdos67b

open MRHalaszBands MRHalaszEuler EulerResidue

noncomputable section

theorem mrExists_norm_typicalCofactorPerron_le_of_lowHigh :
    ∃ C : ℝ, ∃ Y : ℕ, 1 ≤ C ∧
      ∀ {ι : Type*} (A : Finset ℕ) (J : Finset ι) (B : ι → Finset ℕ)
        {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
        (_hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1) {y X : ℕ}
        (_hY : Y ≤ y) (_hX : 2 ≤ X) {alpha beta T M : ℝ} (K : ℕ)
        (_hlogy : 6 ≤ Real.log (y : ℝ))
        (_ha : alpha ≤ (Real.log (y : ℝ))⁻¹)
        (_hb0 : 0 ≤ beta) (_hb : beta ≤ (Real.log (y : ℝ))⁻¹)
        (_hT : 0 ≤ T) (_hTK : T ≤ (((2 : ℕ) ^ K : ℕ) : ℝ)) (_hM : 0 ≤ M)
        (_hlow : ∀ t, |t| ≤ T →
          ‖LSeries (mrTypicalCofactorLowArithmetic A J B f y)
              (((taoExponent X - alpha - 2 * beta : ℝ) : ℂ) + I * (t : ℂ)) *
            LSeries (gsA9HighArithmetic f y) (halaszPoint X t)‖ ≤ M),
        ‖mrTypicalCofactorMovingPerronIntegral A J B f hmul y X alpha beta T‖ ≤
          (2 * Real.pi)⁻¹ * (M * (X : ℝ) ^ (taoExponent X - alpha - 2 * beta)) *
            (gsA10PrimeSourceWeightedRowFactor C y X K *
                (((X / y : ℕ) : ℝ) ^ (2 * beta) * gsA10PrimeLambdaHarmonicBudget X) +
              4 * T * gsA10LambdaVerticalSplitError y X
                (taoExponent X - 2 * beta) (taoExponent X)) := by
  obtain ⟨C, Y, hC, hvertical⟩ := mrExists_weightedLambda_fixedHigh_pair_le
  refine ⟨C, Y, hC, ?_⟩
  intro ι A J B f hmul hbound y X hY hX alpha beta T M K hlogy ha hb0 hb hT hTK hM hlow
  let sigma := taoExponent X - alpha - 2 * beta
  let s : ℝ → ℂ := fun t ↦ (sigma : ℂ) + I * (t : ℂ)
  let lowHigh : ℝ → ℂ := fun t ↦
    LSeries (mrTypicalCofactorLowArithmetic A J B f y) (s t) *
      LSeries (gsA9HighArithmetic f y) (halaszPoint X t)
  let F : ℝ → ℂ := fun t ↦ lowHigh t * (X : ℂ) ^ s t
  have hc := one_lt_taoExponent (show 1 < X by omega)
  have hinv : (Real.log (y : ℝ))⁻¹ ≤ 1 / 6 := by
    simpa only [one_div] using inv_anti₀ (by norm_num : (0 : ℝ) < 6) hlogy
  have hhalf : 1 / 2 ≤ sigma := by dsimp only [sigma]; linarith
  have hsigma : 0 < sigma := by linarith
  have hXR : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hs : Continuous s := by dsimp only [s]; fun_prop
  have hcont : Continuous F :=
    ((mrContinuous_LSeries_typicalCofactorLow_vertical A J B hbound y hsigma).mul
      (continuous_LSeries_gsA9HighArithmetic_vertical hbound y hc)).mul
        (continuous_const.cpow hs (fun _ ↦ Or.inl (by exact_mod_cast (show 0 < X by omega))))
  have hlowBound : ∀ t, |t| ≤ T → ‖lowHigh t‖ ≤ M := hlow
  have hFbound : ∀ t, |t| ≤ T → ‖F t‖ ≤ M * (X : ℝ) ^ sigma := by
    intro t ht
    have hpow : ‖(X : ℂ) ^ s t‖ = (X : ℝ) ^ sigma := by
      simpa [s] using Complex.norm_cpow_eq_rpow_re_of_pos hXR (s t)
    dsimp only [F]
    rw [norm_mul, hpow]
    exact mul_le_mul_of_nonneg_right (hlowBound t ht) (Real.rpow_nonneg hXR.le _)
  have hraw := hvertical hmul hbound y X beta sigma T (M * (X : ℝ) ^ sigma) K F
    hY hX hb0 hhalf hT hTK (mul_nonneg hM (Real.rpow_nonneg hXR.le _)) hcont hFbound
  have hcontour : mrTypicalCofactorMovingPerronIntegral A J B f hmul y X alpha beta T =
      (((2 * Real.pi : ℝ) : ℂ)⁻¹) * ∫ t in -T..T,
        F t * LSeries (gsA10LambdaWindow (gsA9HighGeneralizedMangoldt hmul y) y X)
            (((taoExponent X - 2 * beta : ℝ) : ℂ) + I * (t : ℂ)) *
          LSeries (gsA10LambdaWindow (gsA9HighGeneralizedMangoldt hmul y) y X)
            ((taoExponent X : ℂ) + I * (t : ℂ)) / s t := by
    rw [mrTypicalCofactorMovingPerronIntegral_eq_fourFactors A J B hmul hbound
      (by omega) hlogy ha hb]
    congr 1
    apply intervalIntegral.integral_congr
    intro t _
    dsimp only [F, lowHigh, s, sigma, halaszPoint]
    ring
  rw [hcontour, norm_mul]
  have hscalar : ‖(((2 * Real.pi : ℝ) : ℂ)⁻¹)‖ = (2 * Real.pi)⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  rw [hscalar]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hraw (inv_nonneg.mpr (by positivity))

/-- Integrate a proved pointwise weighted contour estimate on its actual
source square. No continuity premise is left for the Perron transform. -/
theorem mrNorm_typicalCofactorIntegratedPerron_div_le_of_pointBudget
    {ι : Type*} (A : Finset ℕ) (J : Finset ι) (B : ι → Finset ℕ)
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1) {y X K : ℕ}
    (hX : 2 ≤ X) (hy : 23 ≤ y) (hyX : y ≤ X)
    {C M eta T : ℝ} (hC : 1 ≤ C) (hM : 0 ≤ M)
    (hlogy : 6 ≤ Real.log (y : ℝ))
    (heta0 : 0 ≤ eta) (heta : eta ≤ (Real.log (y : ℝ))⁻¹) (hT : 0 ≤ T)
    (hpoint : ∀ alpha ∈ Icc (0 : ℝ) eta, ∀ beta ∈ Icc (0 : ℝ) eta,
      ‖mrTypicalCofactorMovingPerronIntegral A J B f hmul y X alpha beta T‖ ≤
        (2 * Real.pi)⁻¹ * (M * (X : ℝ) ^ (taoExponent X - alpha - 2 * beta)) *
          (gsA10PrimeSourceWeightedRowFactor C y X K *
              (((X / y : ℕ) : ℝ) ^ (2 * beta) * gsA10PrimeLambdaHarmonicBudget X) +
            4 * T * gsA10LambdaVerticalSplitError y X
              (taoExponent X - 2 * beta) (taoExponent X))) :
    ‖mrTypicalCofactorIntegratedPerron A J B f hmul y X eta T‖ / (X : ℝ) ≤
      mrWeightedCofactorContourBudget C M y X K eta T := by
  let D := mrWeightedCofactorContourCoefficient C M y X K T
  let scale := (2 * Real.pi)⁻¹ * D
  let P : ℝ → ℝ → ℂ := fun alpha beta ↦
    mrTypicalCofactorMovingPerronIntegral A J B f hmul y X alpha beta T
  let Q : ℝ → ℝ → ℂ := fun _ _ ↦ 0
  let G : ℝ → ℝ → ℝ := fun alpha beta ↦ scale * gsA10MovingRpowPrimeFactor y X alpha beta
  have hD : 0 ≤ D := mrWeightedCofactorContourCoefficient_nonneg hC hM (by omega) (by omega) hT
  have hscale : 0 ≤ scale := mul_nonneg (inv_nonneg.mpr (by positivity)) hD
  have hG : Continuous (Function.uncurry G) :=
    continuous_const.mul (continuous_gsA10MovingRpowPrimeFactor (by omega) hyX)
  have hP : ContinuousOn (Function.uncurry P) (Icc (0 : ℝ) eta ×ˢ Icc (0 : ℝ) eta) := by
    apply (mrContinuousOn_typicalCofactorMovingPerron_sourceRectangle A J B hmul hbound
      (by omega : 1 < X) hlogy T).mono
    intro z hz
    exact ⟨⟨hz.1.1, hz.1.2.trans heta⟩, ⟨hz.2.1, hz.2.2.trans heta⟩⟩
  have hQ : ContinuousOn (Function.uncurry Q) (Icc (0 : ℝ) eta ×ˢ Icc (0 : ℝ) eta) := by
    dsimp only [Q]
    fun_prop
  have hmajor : ∀ alpha ∈ Icc (0 : ℝ) eta, ∀ beta ∈ Icc (0 : ℝ) eta,
      ‖P alpha beta - Q alpha beta‖ ≤ G alpha beta := by
    intro alpha ha beta hb
    have hraw := hpoint alpha ha beta hb
    have hscalar := mrWeightedCofactorPointBudget_le_primeFactor
      (C := C) (M := M) (T := T) (alpha := alpha) (beta := beta) (K := K)
      (y := y) (X := X)
      hM (by omega) hyX hT (by linarith) hb.1 (hb.2.trans heta)
    simpa only [P, Q, G, scale, D, sub_zero] using hraw.trans hscalar
  have havg := norm_two_mul_doubleIntervalIntegral_sub_le_of_pointwise_continuousOn
    (P := P) (Q := Q) (G := G) heta0 hP hQ hG.continuousOn hmajor
  have havg' : ‖mrTypicalCofactorIntegratedPerron A J B f hmul y X eta T‖ ≤
      2 * (scale * (∫ alpha : ℝ in 0..eta, ∫ beta : ℝ in 0..eta,
        gsA10MovingRpowPrimeFactor y X alpha beta)) := by
    simpa only [P, Q, G, mrTypicalCofactorIntegratedPerron,
      intervalIntegral.integral_zero, mul_zero, sub_zero,
      intervalIntegral.integral_const_mul] using havg
  have hpow := doubleIntervalIntegral_gsA10MovingRpowPrimeFactor_le
    (show 0 < y by omega) hyX (show 1 < X by omega) heta0
  have hnorm := havg'.trans (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hpow hscale) (by norm_num))
  have hdiv := div_le_div_of_nonneg_right hnorm (Nat.cast_nonneg X)
  apply hdiv.trans_eq
  have hXne : (X : ℝ) ≠ 0 := by exact_mod_cast (show X ≠ 0 by omega)
  unfold mrWeightedCofactorContourBudget
  dsimp only [scale, D]
  field_simp
  ring


end

end Erdos67b
