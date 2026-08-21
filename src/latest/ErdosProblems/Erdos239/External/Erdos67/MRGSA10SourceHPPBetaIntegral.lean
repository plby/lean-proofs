import ErdosProblems.Erdos239.External.Erdos67.MRGSA10SourceBetaIntegral

/-!
# The square-root beta pole in the source HPP contour term

The higher-prime-power correction has only
`sqrt (((log X)⁻¹ + beta)⁻¹)`.  This file records the corresponding source
alpha--beta rectangle bound, retaining the additional factor `eta`.
-/

open MeasureTheory Set

namespace Erdos67.MRHalaszBands

noncomputable section

theorem intervalIntegral_sqrt_inv_log_add_le
    {L eta : ℝ} (hL : 0 < L) (heta : 0 ≤ eta) :
    (∫ beta : ℝ in 0..eta, Real.sqrt ((L⁻¹ + beta)⁻¹)) ≤
      eta * Real.sqrt L := by
  let d : ℝ := L⁻¹
  let pole : ℝ → ℝ := fun beta ↦
    Real.sqrt ((max (d + beta) (d / 2))⁻¹)
  have hd : 0 < d := by dsimp only [d]; positivity
  have hpole : Continuous pole := by
    dsimp only [pole]
    apply Real.continuous_sqrt.comp
    apply Continuous.inv₀
    · fun_prop
    · intro beta hzero
      have hpos : 0 < max (d + beta) (d / 2) :=
        (half_pos hd).trans_le (le_max_right _ _)
      exact hpos.ne' hzero
  have hpoleEq : ∀ beta ∈ Icc (0 : ℝ) eta,
      pole beta = Real.sqrt ((L⁻¹ + beta)⁻¹) := by
    intro beta hbeta
    dsimp only [pole, d]
    rw [max_eq_left]
    have hbeta0 : 0 ≤ beta := hbeta.1
    linarith [inv_pos.mpr hL]
  have hpoleLe : ∀ beta ∈ Icc (0 : ℝ) eta,
      pole beta ≤ Real.sqrt L := by
    intro beta hbeta
    rw [hpoleEq beta hbeta]
    have hsum : L⁻¹ ≤ L⁻¹ + beta := by linarith [hbeta.1]
    have hinv : (L⁻¹ + beta)⁻¹ ≤ L := by
      have hpos : 0 < L⁻¹ := inv_pos.mpr hL
      have := inv_anti₀ hpos hsum
      simpa only [inv_inv] using this
    exact Real.sqrt_le_sqrt hinv
  have heq :
      (∫ beta : ℝ in 0..eta, Real.sqrt ((L⁻¹ + beta)⁻¹)) =
        ∫ beta : ℝ in 0..eta, pole beta := by
    apply intervalIntegral.integral_congr
    intro beta hbeta
    have hbeta' : beta ∈ Icc (0 : ℝ) eta := by
      simpa only [uIcc_of_le heta] using hbeta
    exact (hpoleEq beta hbeta').symm
  rw [heq]
  calc
    (∫ beta : ℝ in 0..eta, pole beta) ≤
        ∫ _beta : ℝ in 0..eta, Real.sqrt L := by
      apply intervalIntegral.integral_mono_on heta
      · exact hpole.intervalIntegrable _ _
      · exact continuous_const.intervalIntegrable _ _
      · intro beta hbeta
        exact hpoleLe beta hbeta
    _ = eta * Real.sqrt L := by
      rw [intervalIntegral.integral_const]
      simp only [smul_eq_mul]
      ring

/-- Source Perron power times the HPP square-root beta pole. -/
theorem doubleIntervalIntegral_sourcePerron_symmetricBetaSqrtPole_le
    {y X : ℕ} (hy : 0 < y) (hyX : y ≤ X) (hX : 1 < X)
    {eta : ℝ} (heta : 0 ≤ eta) :
    (∫ alpha : ℝ in 0..eta,
      ∫ beta : ℝ in 0..eta,
        ((X : ℝ) ^
            (Erdos67.EulerResidue.taoExponent X - alpha - beta) *
          ((X / y : ℕ) : ℝ) ^ beta) *
            Real.sqrt (((Real.log (X : ℝ))⁻¹ + beta)⁻¹)) ≤
      Real.exp 1 * ((X : ℝ) / Real.log (X : ℝ)) *
        (eta * Real.sqrt (Real.log (X : ℝ))) := by
  let L : ℝ := Real.log (X : ℝ)
  let d : ℝ := L⁻¹
  let pole : ℝ → ℝ := fun beta ↦
    Real.sqrt ((max (d + beta) (d / 2))⁻¹)
  let F : ℝ → ℝ → ℝ := fun alpha beta ↦
    ((X : ℝ) ^
        (Erdos67.EulerResidue.taoExponent X - alpha - beta) *
      ((X / y : ℕ) : ℝ) ^ beta) * pole beta
  let G : ℝ → ℝ → ℝ := fun alpha beta ↦
    (Real.exp 1 * (X : ℝ) ^ (1 - alpha)) * pole beta
  have hL : 0 < L := by
    dsimp only [L]
    exact Real.log_pos (by exact_mod_cast hX)
  have hd : 0 < d := by dsimp only [d]; positivity
  have hXne : (X : ℝ) ≠ 0 := by
    exact_mod_cast (show X ≠ 0 by omega)
  have hdivNat : X / y ≠ 0 := Nat.ne_of_gt (Nat.div_pos hyX hy)
  have hpole : Continuous pole := by
    dsimp only [pole]
    apply Real.continuous_sqrt.comp
    apply Continuous.inv₀
    · fun_prop
    · intro beta hzero
      have hpos : 0 < max (d + beta) (d / 2) :=
        (half_pos hd).trans_le (le_max_right _ _)
      exact hpos.ne' hzero
  have hpoleEq : ∀ beta ∈ Icc (0 : ℝ) eta,
      pole beta = Real.sqrt ((L⁻¹ + beta)⁻¹) := by
    intro beta hbeta
    dsimp only [pole, d]
    rw [max_eq_left]
    have hbeta0 : 0 ≤ beta := hbeta.1
    linarith [inv_pos.mpr hL]
  have hpole0 : ∀ beta, 0 ≤ pole beta := fun beta ↦ Real.sqrt_nonneg _
  have hF : Continuous (Function.uncurry F) := by
    dsimp only [F, Function.uncurry_apply_pair]
    exact (((Real.continuous_const_rpow hXne).comp (by fun_prop)).mul
      ((Real.continuous_const_rpow (by exact_mod_cast hdivNat)).comp
        (by fun_prop))).mul (hpole.comp continuous_snd)
  have hG : Continuous (Function.uncurry G) := by
    dsimp only [G, Function.uncurry_apply_pair]
    exact (continuous_const.mul
      ((Real.continuous_const_rpow hXne).comp (by fun_prop))).mul
        (hpole.comp continuous_snd)
  have hpoint (alpha : ℝ) (beta : ℝ) (hbeta : beta ∈ Icc (0 : ℝ) eta) :
      F alpha beta ≤ G alpha beta := by
    dsimp only [F, G]
    exact mul_le_mul_of_nonneg_right
      (sourcePerron_rpow_mul_symmetricBetaGrowth_le
        hy hyX hX hbeta.1) (hpole0 beta)
  have hinner (alpha : ℝ) :
      (∫ beta : ℝ in 0..eta, F alpha beta) ≤
        ∫ beta : ℝ in 0..eta, G alpha beta := by
    apply intervalIntegral.integral_mono_on heta
    · exact (hF.comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _
    · exact (hG.comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _
    · intro beta hbeta
      exact hpoint alpha beta hbeta
  have houter :
      (∫ alpha : ℝ in 0..eta, ∫ beta : ℝ in 0..eta, F alpha beta) ≤
        ∫ alpha : ℝ in 0..eta, ∫ beta : ℝ in 0..eta, G alpha beta := by
    apply intervalIntegral.integral_mono_on heta
    · exact (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
        hF 0 eta).intervalIntegrable _ _
    · exact (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
        hG 0 eta).intervalIntegrable _ _
    · intro alpha halpha
      exact hinner alpha
  have hpoleInt : (∫ beta : ℝ in 0..eta, pole beta) ≤
      eta * Real.sqrt L := by
    have hraw := intervalIntegral_sqrt_inv_log_add_le hL heta
    have heq : (∫ beta : ℝ in 0..eta, pole beta) =
        ∫ beta : ℝ in 0..eta, Real.sqrt ((L⁻¹ + beta)⁻¹) := by
      apply intervalIntegral.integral_congr
      intro beta hbeta
      have hbeta' : beta ∈ Icc (0 : ℝ) eta := by
        simpa only [uIcc_of_le heta] using hbeta
      exact hpoleEq beta hbeta'
    rw [heq]
    exact hraw
  have halpha := intervalIntegral_rpow_one_sub_le_div_log hX heta
  have htarget :
      (∫ alpha : ℝ in 0..eta,
        ∫ beta : ℝ in 0..eta,
          ((X : ℝ) ^
              (Erdos67.EulerResidue.taoExponent X - alpha - beta) *
            ((X / y : ℕ) : ℝ) ^ beta) *
              Real.sqrt (((Real.log (X : ℝ))⁻¹ + beta)⁻¹)) =
        ∫ alpha : ℝ in 0..eta, ∫ beta : ℝ in 0..eta, F alpha beta := by
    apply intervalIntegral.integral_congr
    intro alpha halphaMem
    apply intervalIntegral.integral_congr
    intro beta hbeta
    have hbeta' : beta ∈ Icc (0 : ℝ) eta := by
      simpa only [uIcc_of_le heta] using hbeta
    dsimp only [F]
    rw [hpoleEq beta hbeta']
  rw [htarget]
  calc
    _ ≤ ∫ alpha : ℝ in 0..eta,
        ∫ beta : ℝ in 0..eta, G alpha beta := houter
    _ = (Real.exp 1 *
          (∫ alpha : ℝ in 0..eta, (X : ℝ) ^ (1 - alpha))) *
        (∫ beta : ℝ in 0..eta, pole beta) := by
      dsimp only [G]
      simp only [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_mul_const]
    _ ≤ (Real.exp 1 * ((X : ℝ) / Real.log (X : ℝ))) *
        (eta * Real.sqrt L) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left halpha (Real.exp_nonneg 1)
      · exact hpoleInt
      · exact intervalIntegral.integral_nonneg heta
          (fun beta hbeta ↦ hpole0 beta)
      · exact mul_nonneg (Real.exp_nonneg 1) (by positivity)
    _ = Real.exp 1 * ((X : ℝ) / Real.log (X : ℝ)) *
        (eta * Real.sqrt (Real.log (X : ℝ))) := by
      rfl

end

end Erdos67.MRHalaszBands

#print axioms
  Erdos67.MRHalaszBands.doubleIntervalIntegral_sourcePerron_symmetricBetaSqrtPole_le
