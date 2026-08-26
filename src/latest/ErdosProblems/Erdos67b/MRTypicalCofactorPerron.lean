import ErdosProblems.Erdos67b.MRTypicalCofactorVertical
import ErdosProblems.Erdos67b.MRGSA10FixedHighTailoredPerron

/-!
# Moving Perron transform of the actual typical cofactor

The genuine variable Perron kernel is inserted before the common-window
energy estimate. The resulting transform concerns the exact tailored
coefficient, with no assertion yet about its finite-prefix error.
-/

open scoped BigOperators Classical LSeries.notation
open Complex

namespace Erdos67b

open MRHalaszBands MRHalaszEuler EulerResidue EulerQuantitative BoundedGaps.Maynard

noncomputable section

theorem mrContinuous_perronKernel {X : ℕ} (hX : 0 < X) {sigma : ℝ} (hsigma : 0 < sigma) :
    Continuous (fun t : ℝ ↦ (X : ℂ) ^ ((sigma : ℂ) + I * (t : ℂ)) /
      ((sigma : ℂ) + I * (t : ℂ))) := by
  apply Continuous.div
  · have hline : Continuous (fun t : ℝ ↦ (sigma : ℂ) + I * (t : ℂ)) := by fun_prop
    exact hline.const_cpow (Or.inl (by exact_mod_cast hX.ne'))
  · fun_prop
  · intro t hzero
    have hre := congrArg Complex.re hzero
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.I_im, Complex.ofReal_im, zero_mul, one_mul, sub_zero, add_zero,
      Complex.zero_re] at hre
    linarith

theorem mrNorm_sourcePerronKernel_le {X : ℕ} (hX : 2 ≤ X)
    {alpha beta : ℝ} (ha0 : 0 ≤ alpha) (hb0 : 0 ≤ beta)
    (hhalf : 1 / 2 ≤ taoExponent X - alpha - 2 * beta) (t : ℝ) :
    ‖(X : ℂ) ^ (((taoExponent X - alpha - 2 * beta : ℝ) : ℂ) + I * (t : ℂ)) /
      (((taoExponent X - alpha - 2 * beta : ℝ) : ℂ) + I * (t : ℂ))‖ ≤
      gsA10FixedHighPerronKernelScale X := by
  let sigma := taoExponent X - alpha - 2 * beta
  let s : ℂ := (sigma : ℂ) + I * (t : ℂ)
  have hsigma : 0 < sigma := by dsimp only [sigma]; linarith
  have hsRe : s.re = sigma := by simp [s]
  have hsNorm : sigma ≤ ‖s‖ := by
    simpa only [hsRe, abs_of_pos hsigma] using Complex.abs_re_le_norm s
  have hpow : (X : ℝ) ^ sigma ≤ Real.exp 2 * X := by
    dsimp only [sigma]
    simpa only [sub_sub] using rpow_sourcePerronLine_le_exp_two_mul hX ha0
      (mul_nonneg (by norm_num) hb0 : 0 ≤ 2 * beta)
  have hpowNorm : ‖(X : ℂ) ^ s‖ = (X : ℝ) ^ sigma := by
    have hXp : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
    simpa only [Complex.ofReal_natCast, hsRe] using Complex.norm_cpow_eq_rpow_re_of_pos hXp s
  change ‖(X : ℂ) ^ s / s‖ ≤ _
  rw [norm_div, hpowNorm]
  calc
    _ ≤ (Real.exp 2 * X) / ‖s‖ := div_le_div_of_nonneg_right hpow (norm_nonneg _)
    _ ≤ (Real.exp 2 * X) / (1 / 2 : ℝ) :=
      div_le_div_of_nonneg_left (by positivity) (by norm_num) (hhalf.trans hsNorm)
    _ = _ := by unfold gsA10FixedHighPerronKernelScale; ring

def mrTypicalCofactorMovingPerronIntegral {ι : Type*}
    (A : Finset ℕ) (J : Finset ι) (B : ι → Finset ℕ)
    (f : ℕ → ℂ) (hmul : IsMultiplicativeOnPositiveNat f)
    (y X : ℕ) (alpha beta T : ℝ) : ℂ :=
  dirichletPerronIntegral (mrTypicalCofactorTailoredCoefficient A J B f hmul y X alpha beta)
    X (taoExponent X - alpha - 2 * beta) T

theorem mrTypicalCofactorMovingPerronIntegral_eq_fourFactors {ι : Type*}
    (A : Finset ℕ) (J : Finset ι) (B : ι → Finset ℕ)
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {X y : ℕ} (hX : 1 < X) {alpha beta T : ℝ}
    (hlogy : 6 ≤ Real.log (y : ℝ))
    (ha : alpha ≤ (Real.log (y : ℝ))⁻¹) (hb : beta ≤ (Real.log (y : ℝ))⁻¹) :
    let sigma := taoExponent X - alpha - 2 * beta
    let W := gsA10LambdaWindow (gsA9HighGeneralizedMangoldt hmul y) y X
    mrTypicalCofactorMovingPerronIntegral A J B f hmul y X alpha beta T =
      (((2 * Real.pi : ℝ) : ℂ)⁻¹) * ∫ t in -T..T,
        ((LSeries (mrTypicalCofactorLowArithmetic A J B f y) ((sigma : ℂ) + I * (t : ℂ)) *
          LSeries (gsA9HighArithmetic f y) (halaszPoint X t)) *
          ((X : ℂ) ^ ((sigma : ℂ) + I * (t : ℂ)) / ((sigma : ℂ) + I * (t : ℂ)))) *
          LSeries W (((taoExponent X - 2 * beta : ℝ) : ℂ) + I * (t : ℂ)) *
          LSeries W (halaszPoint X t) := by
  dsimp only
  unfold mrTypicalCofactorMovingPerronIntegral dirichletPerronIntegral
  congr 1
  apply intervalIntegral.integral_congr
  intro t _
  dsimp only
  rw [mul_comm (t : ℂ) I,
    mrLSeries_typicalCofactorTailored_eq_fourFactors A J B hmul hbound hX hlogy ha hb]
  simp only [Complex.ofReal_natCast]
  ring

/-- The actual cofactor Perron transform, with the variable kernel included
before applying the common Mangoldt-window energies. -/
theorem mrExists_norm_typicalCofactorMovingPerronIntegral_le :
    ∃ Cβ : ℝ, 1 ≤ Cβ ∧
      ∀ (A : Finset ℕ) (_hA : ∀ p ∈ A, p.Prime)
        (J : Finset ℕ) (B : ℕ → Finset ℕ) {N X y Q S : ℕ}
        (_hX : 2 ≤ X) (_hy : 23 ≤ y)
        (_hJ : ∀ j ∈ J, 1 ≤ j) (_hB : ∀ j ∈ J, B j ⊆ primesUpTo X)
        (_hdisj : Set.PairwiseDisjoint (↑J : Set ℕ) B)
        (_hsmall : ∀ j ∈ J, ∀ p ∈ B j, Real.log (p : ℝ) ≤ Real.log (X : ℝ) / 16)
        (_hmass : ∀ j ∈ J, 2 * Real.log (j : ℝ) ≤ ∑ p ∈ B j, 1 / (p : ℝ))
        (_hAy : ∀ p ∈ A, p ≤ y) (_hBy : ∀ j ∈ J, ∀ p ∈ B j, p ≤ y)
        {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
        (_hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1) (_hnonpret : MRArchimedeanNonpretentious f N X)
        (_hQ : 3 ≤ Q) (_hQy : Q ≤ y) (_hS : 101 ≤ S)
        (_hlogCβ : Real.log Cβ ≤ 2 * (S - 100 : ℕ) / 99)
        {alpha beta T : ℝ} (_hlogy : 6 ≤ Real.log (y : ℝ))
        (_ha0 : 0 ≤ alpha) (_ha : alpha ≤ (Real.log (y : ℝ))⁻¹)
        (_hb0 : 0 ≤ beta) (_hb : beta ≤ (Real.log (y : ℝ))⁻¹)
        (_hT : 0 < T) (_hTX : T ≤ X),
        let M := mrTypicalCofactorFixedHighEnvelope A N X * gsA10FixedHighPerronKernelScale X
        ‖mrTypicalCofactorMovingPerronIntegral A J B (gsDeletePrimeBand f gsA9SmallPrime)
          (gsDeletePrimeBand_isMultiplicativeOnPositiveNat hmul gsA9SmallPrime)
          y X alpha beta T‖ ≤
          (2 * Real.pi)⁻¹ * (M *
              (gsA10PrimeLambdaLeftEnergyBound Cβ Q S X y (2 * beta) T) ^ ((1 : ℝ) / 2) *
              (gsA10PrimeLambdaRightEnergyBound Cβ Q S y X T) ^ ((1 : ℝ) / 2) +
            2 * T * M *
              gsA10LambdaVerticalSplitError y X (taoExponent X - 2 * beta) (taoExponent X)) := by
  obtain ⟨Cβ, hCβ, hvertical⟩ := exists_norm_intervalIntegral_mul_gsA10LambdaWindow_fixedHigh_pair_le
  refine ⟨Cβ, hCβ, ?_⟩
  intro A hA J B N X y Q S hX hy hJ hB hdisj hsmall hmass hAy hBy f hmul hbound hnonpret
    hQ hQy hS hlogCβ alpha beta T hlogy ha0 ha hb0 hb hT hTX
  dsimp only
  let g := gsDeletePrimeBand f gsA9SmallPrime
  let hgmul := gsDeletePrimeBand_isMultiplicativeOnPositiveNat hmul gsA9SmallPrime
  have hgbound : ∀ n, 0 < n → ‖g n‖ ≤ 1 :=
    fun n hn ↦ norm_gsDeletePrimeBand_le_one hbound gsA9SmallPrime hn
  let sigma := taoExponent X - alpha - 2 * beta
  let M := mrTypicalCofactorFixedHighEnvelope A N X
  let K := gsA10FixedHighPerronKernelScale X
  let lowHigh : ℝ → ℂ := fun t ↦
    LSeries (mrTypicalCofactorLowArithmetic A J B g y) ((sigma : ℂ) + I * (t : ℂ)) *
      LSeries (gsA9HighArithmetic g y) (halaszPoint X t)
  let kernel : ℝ → ℂ := fun t ↦ (X : ℂ) ^ ((sigma : ℂ) + I * (t : ℂ)) /
      ((sigma : ℂ) + I * (t : ℂ))
  let F : ℝ → ℂ := fun t ↦ lowHigh t * kernel t
  have hc := one_lt_taoExponent (show 1 < X by omega)
  have hinv : (Real.log (y : ℝ))⁻¹ ≤ 1 / 6 := by
    simpa only [one_div] using inv_anti₀ (by norm_num : (0 : ℝ) < 6) hlogy
  have hhalf : 1 / 2 ≤ sigma := by dsimp only [sigma]; linarith
  have hsigma : 0 < sigma := by linarith
  have hM : 0 ≤ M := (Real.exp_pos _).le
  have hK : 0 ≤ K := gsA10FixedHighPerronKernelScale_nonneg X
  have hcont : Continuous F :=
    ((mrContinuous_LSeries_typicalCofactorLow_vertical A J B hgbound y hsigma).mul
      (continuous_LSeries_gsA9HighArithmetic_vertical hgbound y hc)).mul
        (mrContinuous_perronKernel (by omega) hsigma)
  have hlowBound : ∀ t, |t| ≤ T → ‖lowHigh t‖ ≤ M := by
    intro t ht
    dsimp only [lowHigh]
    rw [LSeries_gsA9HighArithmetic, gsA9High_deleteSmallPrimes_eq f hy]
    exact mrNorm_sourceTypicalCofactorLow_mul_high_fixedHalasz_le A hA J B (by omega) hy hJ hB
      hdisj hsmall hmass hAy hBy hmul hbound hnonpret hlogy ha0 ha hb0 hb (ht.trans hTX)
  have hFbound : ∀ t, |t| ≤ T → ‖F t‖ ≤ M * K := by
    intro t ht
    dsimp only [F]
    rw [norm_mul]
    exact mul_le_mul (hlowBound t ht) (mrNorm_sourcePerronKernel_le hX ha0 hb0 hhalf t)
      (norm_nonneg _) hM
  have hraw := hvertical hgmul hgbound y X Q S beta T (M * K) F hX hQ hQy hS hlogCβ hb0 hT
    (mul_nonneg hM hK) hcont hFbound
  rw [mrTypicalCofactorMovingPerronIntegral_eq_fourFactors A J B hgmul hgbound
    (by omega) hlogy ha hb, norm_mul]
  have hscalar : ‖(((2 * Real.pi : ℝ) : ℂ)⁻¹)‖ = (2 * Real.pi)⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  rw [hscalar]
  exact mul_le_mul_of_nonneg_left hraw (inv_nonneg.mpr (by positivity))

end

end Erdos67b
