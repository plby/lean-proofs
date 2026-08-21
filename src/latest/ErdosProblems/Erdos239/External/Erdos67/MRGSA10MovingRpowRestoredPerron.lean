import ErdosProblems.Erdos239.External.Erdos67.MRGSA10MovingKernelRpow
import ErdosProblems.Erdos239.External.Erdos67.MRGSA10FixedHighRestoredPerron

/-!
# Restored fixed-high Perron contour with the moving power retained

This is the source-correct moving-power variant of the restored fixed-high
Perron theorem.  The norm of the Perron kernel is kept as
`2 * X^(c₀-alpha-2 beta)`; it is not replaced by a rectangle-uniform
multiple of `X` before the auxiliary average.
-/

open scoped BigOperators LSeries.notation
open Complex

namespace Erdos67.MRHalaszBands

noncomputable section

/-- Pointwise restored fixed-high Perron control with the exact moving
real power retained in both the prime-window and HPP terms. -/
theorem exists_norm_gsA10MovingPerronIntegral_fixedHigh_restored_le_movingRpow :
    ∃ Cβ : ℝ, 1 ≤ Cβ ∧
      ∀ {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
        (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
        (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
        (hsmallOutside : ∀ p ∈ gsA9SmallPrimeFinset, P₁ p)
        {y A X Q S : ℕ} (hy : 23 ≤ y) (hX : 2 ≤ X)
        (hQ : 3 ≤ Q) (hQy : Q ≤ y) (hS : 101 ≤ S)
        (hlogCβ : Real.log Cβ ≤ 2 * (S - 100 : ℕ) / 99)
        {alpha beta T : ℝ} (hlogy : 6 ≤ Real.log (y : ℝ))
        (halpha0 : 0 ≤ alpha)
        (halpha : alpha ≤ (Real.log (y : ℝ))⁻¹)
        (hbeta0 : 0 ≤ beta)
        (hbeta : beta ≤ (Real.log (y : ℝ))⁻¹)
        (hT : 0 < T) (hTX : T ≤ X)
        (hdist : ∀ t : ℝ, |t| ≤ T →
          (A : ℝ) ≤ pretentiousDistSq f (archimedeanTwist t) X),
        ‖gsA10TwoBlockMovingPerronIntegral
            f hmul P₁ P₂ y X alpha beta T‖ ≤
          (2 * Real.pi)⁻¹ *
            ((gsA10RestoredFixedHighHalaszEnvelope A X *
                gsA10MovingPerronKernelScale X alpha beta) *
                  (gsA10PrimeLambdaLeftEnergyBound Cβ Q S X y
                    (2 * beta) T) ^ ((1 : ℝ) / 2) *
                (gsA10PrimeLambdaRightEnergyBound Cβ Q S y X T) ^
                  ((1 : ℝ) / 2) +
              2 * T *
                (gsA10RestoredFixedHighHalaszEnvelope A X *
                  gsA10MovingPerronKernelScale X alpha beta) *
                ((X : ℝ) ^ (2 * (Real.log (y : ℝ))⁻¹) *
                  (2 * gsA10PrimeLambdaHarmonicBudget X *
                      gsA10HigherPrimePowerGeometricMass y X +
                    (gsA10HigherPrimePowerGeometricMass y X) ^ 2))) := by
  obtain ⟨Cβ, hCβ, hvertical⟩ :=
    exists_norm_intervalIntegral_mul_gsA10LambdaWindow_fixedHigh_pair_le
  refine ⟨Cβ, hCβ, ?_⟩
  intro f hmul hbound P₁ P₂ _ _ hsmallOutside y A X Q S hy hX
    hQ hQy hS hlogCβ alpha beta T hlogy halpha0 halpha hbeta0 hbeta hT hTX
    hdist
  let c₀ : ℝ := Erdos67.EulerResidue.taoExponent X
  let sigma : ℝ := c₀ - alpha - 2 * beta
  let M : ℝ := gsA10RestoredFixedHighHalaszEnvelope A X
  let K : ℝ := gsA10MovingPerronKernelScale X alpha beta
  let lowHigh : ℝ → ℂ := fun t ↦
    LSeries (gsA10TwoBlockAlternatingLow f P₁ P₂ y)
        ((sigma : ℂ) + I * (t : ℂ)) *
      LSeries (gsA9HighArithmetic f y)
        ((c₀ : ℂ) + I * (t : ℂ))
  let kernel : ℝ → ℂ := fun t ↦
    (X : ℂ) ^ ((sigma : ℂ) + I * (t : ℂ)) /
      ((sigma : ℂ) + I * (t : ℂ))
  let F : ℝ → ℂ := fun t ↦ lowHigh t * kernel t
  have hlogX : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hlogyPos : 0 < Real.log (y : ℝ) := by linarith
  have hetaSixth : (Real.log (y : ℝ))⁻¹ ≤ 1 / 6 := by
    simpa only [one_div] using
      inv_anti₀ (by norm_num : (0 : ℝ) < 6) hlogy
  have hcOne : 1 ≤ c₀ := by
    dsimp only [c₀, Erdos67.EulerResidue.taoExponent]
    exact le_add_of_nonneg_right (inv_pos.mpr hlogX).le
  have hcStrict : 1 < c₀ := by
    dsimp only [c₀]
    exact Erdos67.EulerResidue.one_lt_taoExponent (by omega)
  have hsigmaHalf : 1 / 2 ≤ sigma := by
    dsimp only [sigma]
    have hab : alpha + 2 * beta ≤
        3 * (Real.log (y : ℝ))⁻¹ := by linarith
    linarith
  have hsigma : 0 < sigma :=
    (by norm_num : (0 : ℝ) < 1 / 2).trans_le hsigmaHalf
  have hK : 0 ≤ K := by
    dsimp only [K]
    exact gsA10MovingPerronKernelScale_nonneg X alpha beta
  have hlowHighCont : Continuous lowHigh :=
    (continuous_LSeries_twoBlockAlternatingLow_vertical
      hmul hbound P₁ P₂ y hsigma).mul
      (continuous_LSeries_gsA9HighArithmetic_vertical hbound y hcStrict)
  have hsne : ∀ t : ℝ, (sigma : ℂ) + I * (t : ℂ) ≠ 0 := by
    intro t htzero
    have hre := congrArg Complex.re htzero
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.ofReal_im, zero_mul, one_mul,
      sub_zero, Complex.zero_re] at hre
    linarith
  have hkernelCont : Continuous kernel := by
    dsimp only [kernel]
    apply Continuous.div
    · have hline : Continuous (fun t : ℝ ↦
          (sigma : ℂ) + I * (t : ℂ)) := by fun_prop
      exact hline.const_cpow (Or.inl (by norm_cast; omega))
    · fun_prop
    · exact hsne
  have hFcont : Continuous F := hlowHighCont.mul hkernelCont
  have hlowHighBound : ∀ t, |t| ≤ T → ‖lowHigh t‖ ≤ M := by
    intro t ht
    have hab : alpha + 2 * beta ≤
        3 * (Real.log (y : ℝ))⁻¹ := by linarith
    have hsigmaWide : 1 - 3 / Real.log (y : ℝ) ≤ sigma := by
      dsimp only [sigma]
      rw [show 3 / Real.log (y : ℝ) =
        3 * (Real.log (y : ℝ))⁻¹ by field_simp]
      linarith
    have hle : sigma ≤ c₀ := by dsimp only [sigma]; linarith
    have hgap : c₀ - sigma ≤ 3 / Real.log (y : ℝ) := by
      dsimp only [sigma]
      rw [show 3 / Real.log (y : ℝ) =
        3 * (Real.log (y : ℝ))⁻¹ by field_simp]
      linarith
    have hpoint :=
      norm_twoBlock_alternatingLow_mul_high_le_wideHalaszPoint_of_distance
        hmul hbound P₁ P₂ hy hsmallOutside (by omega) (hdist t ht)
        hsigmaHalf hle hsigmaWide hgap
    dsimp only [lowHigh, M, gsA10RestoredFixedHighHalaszEnvelope]
    rw [LSeries_gsA9HighArithmetic]
    simpa only [c₀, sigma, Erdos67.MRHalaszEuler.halaszPoint,
      gsA10FixedHighHalaszEnvelope] using hpoint
  have hM : 0 ≤ M := by
    have hzero := hlowHighBound 0 (by simpa using hT.le)
    exact (norm_nonneg _).trans hzero
  have hMK : 0 ≤ M * K := mul_nonneg hM hK
  have hkernelBound : ∀ t : ℝ, ‖kernel t‖ ≤ K := by
    intro t
    dsimp only [kernel, K, sigma, c₀]
    exact norm_gsA10MovingPerronKernel_le_scale
      hX hlogy halpha0 halpha hbeta0 hbeta
  have hFbound : ∀ t, |t| ≤ T → ‖F t‖ ≤ M * K := by
    intro t ht
    dsimp only [F]
    rw [norm_mul]
    exact mul_le_mul (hlowHighBound t ht) (hkernelBound t)
      (norm_nonneg _) hM
  have hraw := hvertical hmul hbound y X Q S beta T (M * K) F
    hX hQ hQy hS hlogCβ hbeta0 hT hMK hFcont hFbound
  have hsplit := gsA10LambdaVerticalSplitError_fixedHigh_le
    (y := y) (X := X) (show 1 ≤ X by omega) hlogyPos hbeta0 hbeta
  have hcorr :
      2 * T * (M * K) *
          gsA10LambdaVerticalSplitError y X (c₀ - 2 * beta) c₀ ≤
        2 * T * (M * K) *
          ((X : ℝ) ^ (2 * (Real.log (y : ℝ))⁻¹) *
            (2 * gsA10PrimeLambdaHarmonicBudget X *
                gsA10HigherPrimePowerGeometricMass y X +
              (gsA10HigherPrimePowerGeometricMass y X) ^ 2)) := by
    exact mul_le_mul_of_nonneg_left (by
      simpa only [c₀] using hsplit)
      (mul_nonneg (mul_nonneg (by norm_num) hT.le) hMK)
  have hverticalScalar := hraw.trans (add_le_add_right hcorr _)
  have hhigh : 1 < (c₀ - beta) + beta := by
    simpa only [sub_add_cancel] using hcStrict
  have hlow : 0 < c₀ - beta - alpha - beta := by
    dsimp only [sigma] at hsigma
    linarith
  have hfour := gsA10TwoBlockTailoredPerronIntegral_eq_fourFactors
    hmul hbound P₁ P₂ y X (c₀ - beta) alpha beta T hT.le hlow hhigh
  have hLowPoint (t : ℝ) :
      (((c₀ - beta - alpha - beta : ℝ) : ℂ) + (t : ℂ) * I) =
        (sigma : ℂ) + I * (t : ℂ) := by
    apply Complex.ext
    · simp [sigma]
      ring
    · simp
  have hHighPoint (t : ℝ) :
      (((c₀ - beta - alpha - beta : ℝ) : ℂ) + (t : ℂ) * I) +
          ((alpha + 2 * beta : ℝ) : ℂ) =
        (c₀ : ℂ) + I * (t : ℂ) := by
    apply Complex.ext <;>
      simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
        Complex.I_im, zero_mul, mul_zero, one_mul, add_zero, zero_add,
        sub_zero] <;> ring
  have hWindowLowPoint (t : ℝ) :
      (((c₀ - beta - alpha - beta : ℝ) : ℂ) + (t : ℂ) * I) +
          (alpha : ℂ) =
        ((c₀ - 2 * beta : ℝ) : ℂ) + I * (t : ℂ) := by
    apply Complex.ext <;>
      simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
        Complex.I_im, zero_mul, mul_zero, one_mul, add_zero, zero_add,
        sub_zero] <;> ring
  have hcontour :
      gsA10TwoBlockMovingPerronIntegral f hmul P₁ P₂ y X alpha beta T =
        (((2 * Real.pi : ℝ) : ℂ)⁻¹) *
          ∫ t in -T..T,
            F t *
              LSeries
                (gsA10LambdaWindow
                  (gsA9HighGeneralizedMangoldt hmul y) y X)
                (((c₀ - 2 * beta : ℝ) : ℂ) + I * (t : ℂ)) *
              LSeries
                (gsA10LambdaWindow
                  (gsA9HighGeneralizedMangoldt hmul y) y X)
                ((c₀ : ℂ) + I * (t : ℂ)) := by
    unfold gsA10TwoBlockMovingPerronIntegral
    rw [hfour]
    congr 1
    apply intervalIntegral.integral_congr
    intro t _ht
    dsimp only
    rw [hHighPoint t, hWindowLowPoint t, hLowPoint t]
    dsimp only [F, lowHigh, kernel]
    ring
  rw [hcontour, norm_mul]
  have hscalar :
      ‖(((2 * Real.pi : ℝ) : ℂ)⁻¹)‖ = (2 * Real.pi)⁻¹ := by
    have hpi : 0 ≤ 2 * Real.pi := by positivity
    rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg hpi]
  rw [hscalar]
  exact mul_le_mul_of_nonneg_left (by
    simpa only [M, K, c₀] using hverticalScalar)
    (inv_nonneg.mpr (by positivity))

end

end Erdos67.MRHalaszBands

#print axioms
  Erdos67.MRHalaszBands.exists_norm_gsA10MovingPerronIntegral_fixedHigh_restored_le_movingRpow
