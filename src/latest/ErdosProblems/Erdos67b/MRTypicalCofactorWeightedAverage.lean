import ErdosProblems.Erdos67b.MRTypicalCofactorWeightedPerron
import ErdosProblems.Erdos67b.MRGSA10MovingRpowAverage
import ErdosProblems.Erdos67b.MRGSA10RestoredPerronScalar

/-!
# Rectangle average of the weighted actual cofactor contour

The common source row has no height loss in its main term. The actual
moving power cancels the left prime-window growth before either parameter
is integrated. The higher-power correction stays explicit.
-/

open scoped BigOperators Classical
open Set MeasureTheory

namespace Erdos67b

open MRHalaszBands EulerResidue

noncomputable section

def mrWeightedCofactorUniformSplitError (y X : ℕ) : ℝ :=
  (X : ℝ) ^ (2 * (Real.log (y : ℝ))⁻¹) *
    (2 * gsA10PrimeLambdaHarmonicBudget X * gsA10HigherPrimePowerGeometricMass y X +
      (gsA10HigherPrimePowerGeometricMass y X) ^ 2)

def mrWeightedCofactorContourCoefficient (C M : ℝ) (y X K : ℕ) (T : ℝ) : ℝ :=
  M / 2 * (gsA10PrimeSourceWeightedRowFactor C y X K * gsA10PrimeLambdaHarmonicBudget X +
    4 * T * mrWeightedCofactorUniformSplitError y X)

def mrWeightedCofactorContourBudget (C M : ℝ) (y X K : ℕ) (eta T : ℝ) : ℝ :=
  4 * (2 * Real.pi)⁻¹ * Real.exp 1 * eta / Real.log (X : ℝ) *
    mrWeightedCofactorContourCoefficient C M y X K T

theorem mrWeightedCofactorUniformSplitError_nonneg (y X : ℕ) :
    0 ≤ mrWeightedCofactorUniformSplitError y X := by
  have hH : 0 ≤ gsA10PrimeLambdaHarmonicBudget X := by
    unfold gsA10PrimeLambdaHarmonicBudget
    positivity
  have hpp := gsA10HigherPrimePowerGeometricMass_nonneg_source y X
  unfold mrWeightedCofactorUniformSplitError
  positivity

theorem mrWeightedCofactorContourCoefficient_nonneg
    {C M T : ℝ} {y X K : ℕ} (hC : 1 ≤ C) (hM : 0 ≤ M)
    (hy : 1 ≤ y) (hX : 1 ≤ X) (hT : 0 ≤ T) :
    0 ≤ mrWeightedCofactorContourCoefficient C M y X K T := by
  have hmain := gsA10PrimeSourceAffineRowConstant_nonneg hC
  have hslope := gsA10PrimeSourceAffineRowSlope_nonneg hC hy hX
  have hH : 0 ≤ gsA10PrimeLambdaHarmonicBudget X := by
    unfold gsA10PrimeLambdaHarmonicBudget
    positivity
  have herr := mrWeightedCofactorUniformSplitError_nonneg y X
  unfold mrWeightedCofactorContourCoefficient gsA10PrimeSourceWeightedRowFactor
  positivity

theorem mrWeightedCofactorPointBudget_le_primeFactor
    {C M T alpha beta : ℝ} {y X K : ℕ} (hM : 0 ≤ M)
    (hy : 0 < y) (hyX : y ≤ X) (hT : 0 ≤ T)
    (hlogy : 0 < Real.log (y : ℝ))
    (hb0 : 0 ≤ beta) (hb : beta ≤ (Real.log (y : ℝ))⁻¹) :
    (2 * Real.pi)⁻¹ * (M * (X : ℝ) ^ (taoExponent X - alpha - 2 * beta)) *
        (gsA10PrimeSourceWeightedRowFactor C y X K *
            (((X / y : ℕ) : ℝ) ^ (2 * beta) * gsA10PrimeLambdaHarmonicBudget X) +
          4 * T * gsA10LambdaVerticalSplitError y X (taoExponent X - 2 * beta) (taoExponent X)) ≤
      (2 * Real.pi)⁻¹ * mrWeightedCofactorContourCoefficient C M y X K T *
        gsA10MovingRpowPrimeFactor y X alpha beta := by
  let growth : ℝ := ((X / y : ℕ) : ℝ) ^ (2 * beta)
  have hdiv : 1 ≤ X / y := (Nat.le_div_iff_mul_le hy).2 (by simpa using hyX)
  have hgrowth : 1 ≤ growth := Real.one_le_rpow (by exact_mod_cast hdiv) (by positivity)
  have hU := mrWeightedCofactorUniformSplitError_nonneg y X
  have hsplit : gsA10LambdaVerticalSplitError y X (taoExponent X - 2 * beta) (taoExponent X) ≤
      mrWeightedCofactorUniformSplitError y X :=
    gsA10LambdaVerticalSplitError_fixedHigh_le (show 1 ≤ X by omega) hlogy hb0 hb
  have he : 4 * T * gsA10LambdaVerticalSplitError y X (taoExponent X - 2 * beta) (taoExponent X) ≤
      4 * T * mrWeightedCofactorUniformSplitError y X * growth :=
    (mul_le_mul_of_nonneg_left hsplit (by positivity)).trans
      (le_mul_of_one_le_right (by positivity) hgrowth)
  have hfactor : 0 ≤ (2 * Real.pi)⁻¹ * (M * (X : ℝ) ^ (taoExponent X - alpha - 2 * beta)) := by
    positivity
  calc
    _ ≤ (2 * Real.pi)⁻¹ * (M * (X : ℝ) ^ (taoExponent X - alpha - 2 * beta)) *
        (gsA10PrimeSourceWeightedRowFactor C y X K *
            (growth * gsA10PrimeLambdaHarmonicBudget X) +
          4 * T * mrWeightedCofactorUniformSplitError y X * growth) :=
      mul_le_mul_of_nonneg_left (add_le_add le_rfl he) hfactor
    _ = _ := by
      unfold mrWeightedCofactorContourCoefficient gsA10MovingRpowPrimeFactor gsA10MovingPerronKernelScale
      dsimp only [growth]
      ring

theorem mrExists_norm_typicalCofactorIntegratedPerron_div_le_weightedBudget :
    ∃ C : ℝ, ∃ Y : ℕ, 1 ≤ C ∧
      ∀ (A : Finset ℕ) (_hA : ∀ p ∈ A, p.Prime)
        (J : Finset ℕ) (B : ℕ → Finset ℕ) {N X y : ℕ}
        (_hY : Y ≤ y) (_hX : 2 ≤ X) (_hy : 23 ≤ y) (_hyX : y ≤ X)
        (_hJ : ∀ j ∈ J, 1 ≤ j) (_hB : ∀ j ∈ J, B j ⊆ primesUpTo X)
        (_hdisj : Set.PairwiseDisjoint (↑J : Set ℕ) B)
        (_hsmall : ∀ j ∈ J, ∀ p ∈ B j, Real.log (p : ℝ) ≤ Real.log (X : ℝ) / 16)
        (_hmass : ∀ j ∈ J, 2 * Real.log (j : ℝ) ≤ ∑ p ∈ B j, 1 / (p : ℝ))
        (_hAy : ∀ p ∈ A, p ≤ y) (_hBy : ∀ j ∈ J, ∀ p ∈ B j, p ≤ y)
        {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
        (_hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1) (_hnonpret : MRArchimedeanNonpretentious f N X)
        {eta T : ℝ} (K : ℕ) (_hlogy : 6 ≤ Real.log (y : ℝ))
        (_heta0 : 0 ≤ eta) (_heta : eta ≤ (Real.log (y : ℝ))⁻¹)
        (_hT : 0 ≤ T) (_hTX : T ≤ X) (_hTK : T ≤ (((2 : ℕ) ^ K : ℕ) : ℝ)),
        ‖mrTypicalCofactorIntegratedPerron A J B (gsDeletePrimeBand f gsA9SmallPrime)
          (gsDeletePrimeBand_isMultiplicativeOnPositiveNat hmul gsA9SmallPrime) y X eta T‖ / (X : ℝ) ≤
          mrWeightedCofactorContourBudget C (mrTypicalCofactorFixedHighEnvelope A N X) y X K eta T := by
  obtain ⟨C, Y, hC, hpoint⟩ := mrExists_norm_typicalCofactorMovingPerronIntegral_weighted_le
  refine ⟨C, Y, hC, ?_⟩
  intro A hA J B N X y hY hX hy hyX hJ hB hdisj hsmall hmass hAy hBy f hmul hbound hnonpret
    eta T K hlogy heta0 heta hT hTX hTK
  let g := gsDeletePrimeBand f gsA9SmallPrime
  let hgmul := gsDeletePrimeBand_isMultiplicativeOnPositiveNat hmul gsA9SmallPrime
  have hgbound : ∀ n, 0 < n → ‖g n‖ ≤ 1 :=
    fun n hn ↦ norm_gsDeletePrimeBand_le_one hbound gsA9SmallPrime hn
  let M := mrTypicalCofactorFixedHighEnvelope A N X
  let D := mrWeightedCofactorContourCoefficient C M y X K T
  let scale := (2 * Real.pi)⁻¹ * D
  let P : ℝ → ℝ → ℂ := fun alpha beta ↦
    mrTypicalCofactorMovingPerronIntegral A J B g hgmul y X alpha beta T
  let Q : ℝ → ℝ → ℂ := fun _ _ ↦ 0
  let G : ℝ → ℝ → ℝ := fun alpha beta ↦ scale * gsA10MovingRpowPrimeFactor y X alpha beta
  have hM : 0 ≤ M := (Real.exp_pos _).le
  have hD : 0 ≤ D := mrWeightedCofactorContourCoefficient_nonneg hC hM (by omega) (by omega) hT
  have hscale : 0 ≤ scale := mul_nonneg (inv_nonneg.mpr (by positivity)) hD
  have hG : Continuous (Function.uncurry G) :=
    continuous_const.mul (continuous_gsA10MovingRpowPrimeFactor (by omega) hyX)
  have hP : ContinuousOn (Function.uncurry P) (Icc (0 : ℝ) eta ×ˢ Icc (0 : ℝ) eta) := by
    apply (mrContinuousOn_typicalCofactorMovingPerron_sourceRectangle A J B hgmul hgbound
      (by omega : 1 < X) hlogy T).mono
    intro z hz
    exact ⟨⟨hz.1.1, hz.1.2.trans heta⟩, ⟨hz.2.1, hz.2.2.trans heta⟩⟩
  have hQ : ContinuousOn (Function.uncurry Q) (Icc (0 : ℝ) eta ×ˢ Icc (0 : ℝ) eta) := by
    dsimp only [Q]
    fun_prop
  have hmajor : ∀ alpha ∈ Icc (0 : ℝ) eta, ∀ beta ∈ Icc (0 : ℝ) eta,
      ‖P alpha beta - Q alpha beta‖ ≤ G alpha beta := by
    intro alpha ha beta hb
    have hraw := hpoint A hA J B hY hX hy hJ hB hdisj hsmall hmass hAy hBy hmul hbound hnonpret
      K hlogy ha.1 (ha.2.trans heta) hb.1 (hb.2.trans heta) hT hTX hTK
    have hscalar := mrWeightedCofactorPointBudget_le_primeFactor
      (C := C) (M := M) (T := T) (alpha := alpha) (beta := beta) (K := K)
      (y := y) (X := X)
      hM (by omega) hyX hT (by linarith) hb.1 (hb.2.trans heta)
    simpa only [P, Q, G, scale, D, sub_zero] using hraw.trans hscalar
  have havg := norm_two_mul_doubleIntervalIntegral_sub_le_of_pointwise_continuousOn
    (P := P) (Q := Q) (G := G) heta0 hP hQ hG.continuousOn hmajor
  have havg' : ‖mrTypicalCofactorIntegratedPerron A J B g hgmul y X eta T‖ ≤
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
