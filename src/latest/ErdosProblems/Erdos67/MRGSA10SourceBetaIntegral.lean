import ErdosProblems.Erdos67.MRGSA9RpowIntegral
import ErdosProblems.Erdos67.MRGSA10RpowAverage

/-!
# The source alpha--beta contour integral

On the original A.10 lines the Perron power and the symmetric prime-window
diagonal contain the product

`X^(c₀-alpha-beta) * (X/y)^beta`.

The beta powers cancel before integration.  The remaining beta singularity
has order `3/2`, so its integral is `O(sqrt (log X))`; the alpha integral
contributes `X / log X`.  This file records that scalar calculation without
any analytic L-series input.
-/

open MeasureTheory Set

namespace Erdos67.MRHalaszBands

noncomputable section

/-- Translating the source beta pole to the positive interval beginning at
`(log X)⁻¹` gives the expected square-root logarithmic bound. -/
theorem intervalIntegral_inv_log_add_rpow_neg_three_halves_le
    {L eta : ℝ} (hL : 0 < L) (heta : 0 ≤ eta) :
    (∫ beta : ℝ in 0..eta, (L⁻¹ + beta) ^ (-3 / 2 : ℝ)) ≤
      2 * Real.sqrt L := by
  have hInv : 0 < L⁻¹ := inv_pos.mpr hL
  have hends : L⁻¹ ≤ eta + L⁻¹ := by linarith
  have hbase := Erdos67.integral_inv_rpow_three_halves_le hInv hends
  have hshift :
      (∫ beta : ℝ in 0..eta, (L⁻¹ + beta) ^ (-3 / 2 : ℝ)) =
        ∫ sigma : ℝ in L⁻¹..eta + L⁻¹,
          sigma ^ (-3 / 2 : ℝ) := by
    simpa [add_comm] using
      (intervalIntegral.integral_comp_add_left
        (fun sigma : ℝ ↦ sigma ^ (-3 / 2 : ℝ)) L⁻¹
          (a := 0) (b := eta))
  have hpow : L⁻¹ ^ (-1 / 2 : ℝ) = Real.sqrt L := by
    rw [Real.inv_rpow hL.le, Real.sqrt_eq_rpow]
    rw [show (-1 / 2 : ℝ) = -(1 / 2) by ring]
    rw [Real.rpow_neg hL.le]
    simp
  rw [hshift]
  simpa only [hpow] using hbase

/-- Pointwise cancellation of the beta growth in the symmetric diagonal
against the beta decay of the original source Perron line. -/
theorem sourcePerron_rpow_mul_symmetricBetaGrowth_le
    {y X : ℕ} (hy : 0 < y) (hyX : y ≤ X) (hX : 1 < X)
    {alpha beta : ℝ} (hbeta : 0 ≤ beta) :
    (X : ℝ) ^
          (Erdos67.EulerResidue.taoExponent X - alpha - beta) *
        ((X / y : ℕ) : ℝ) ^ beta ≤
      Real.exp 1 * (X : ℝ) ^ (1 - alpha) := by
  have hXR : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hdivNat : 0 < X / y := Nat.div_pos hyX hy
  have hdiv0 : (0 : ℝ) < ((X / y : ℕ) : ℝ) := by
    exact_mod_cast hdivNat
  have hdivX : ((X / y : ℕ) : ℝ) ≤ X := by
    exact_mod_cast Nat.div_le_self X y
  have hratio : ((X / y : ℕ) : ℝ) ^ beta ≤ (X : ℝ) ^ beta :=
    Real.rpow_le_rpow hdiv0.le hdivX hbeta
  have hlog : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast hX)
  have hpowInv :
      (X : ℝ) ^ (Real.log (X : ℝ))⁻¹ = Real.exp 1 := by
    rw [Real.rpow_def_of_pos hXR]
    congr 1
    exact mul_inv_cancel₀ hlog.ne'
  calc
    (X : ℝ) ^
          (Erdos67.EulerResidue.taoExponent X - alpha - beta) *
        ((X / y : ℕ) : ℝ) ^ beta ≤
        (X : ℝ) ^
            (Erdos67.EulerResidue.taoExponent X - alpha - beta) *
          (X : ℝ) ^ beta := by
      exact mul_le_mul_of_nonneg_left hratio (Real.rpow_nonneg hXR.le _)
    _ = (X : ℝ) ^
        (Erdos67.EulerResidue.taoExponent X - alpha) := by
      rw [← Real.rpow_add hXR]
      congr 1
      ring
    _ = Real.exp 1 * (X : ℝ) ^ (1 - alpha) := by
      unfold Erdos67.EulerResidue.taoExponent
      rw [show 1 + (Real.log (X : ℝ))⁻¹ - alpha =
          (1 - alpha) + (Real.log (X : ℝ))⁻¹ by ring,
        Real.rpow_add hXR, hpowInv]
      ring

/-- The complete source power/pole rectangle.  This is the scalar integral
left after the A.13--A.14 maximum-modulus envelope and the symmetric
prime-Lambda weighted-energy estimate have been inserted. -/
theorem doubleIntervalIntegral_sourcePerron_symmetricBetaPole_le
    {y X : ℕ} (hy : 0 < y) (hyX : y ≤ X) (hX : 1 < X)
    {eta : ℝ} (heta : 0 ≤ eta) :
    (∫ alpha : ℝ in 0..eta,
      ∫ beta : ℝ in 0..eta,
        ((X : ℝ) ^
            (Erdos67.EulerResidue.taoExponent X - alpha - beta) *
          ((X / y : ℕ) : ℝ) ^ beta) *
            ((Real.log (X : ℝ))⁻¹ + beta) ^ (-3 / 2 : ℝ)) ≤
      2 * Real.exp 1 * ((X : ℝ) / Real.log (X : ℝ)) *
        Real.sqrt (Real.log (X : ℝ)) := by
  let L : ℝ := Real.log (X : ℝ)
  /- The `max` gives a globally continuous positive extension.  On the
  integration interval `beta ≥ 0` it is exactly the source pole. -/
  let pole : ℝ → ℝ := fun beta ↦
    (max (L⁻¹ + beta) (L⁻¹ / 2)) ^ (-3 / 2 : ℝ)
  let F : ℝ → ℝ → ℝ := fun alpha beta ↦
    ((X : ℝ) ^
        (Erdos67.EulerResidue.taoExponent X - alpha - beta) *
      ((X / y : ℕ) : ℝ) ^ beta) * pole beta
  let G : ℝ → ℝ → ℝ := fun alpha beta ↦
    (Real.exp 1 * (X : ℝ) ^ (1 - alpha)) * pole beta
  have hL : 0 < L := by
    dsimp only [L]
    exact Real.log_pos (by exact_mod_cast hX)
  have hXne : (X : ℝ) ≠ 0 := by
    exact_mod_cast (show X ≠ 0 by omega)
  have hdivNat : X / y ≠ 0 :=
    (Nat.ne_of_gt (Nat.div_pos hyX hy))
  have hpoleEq : ∀ beta ∈ Icc (0 : ℝ) eta,
      pole beta = (L⁻¹ + beta) ^ (-3 / 2 : ℝ) := by
    intro beta hbeta
    dsimp only [pole]
    rw [max_eq_left]
    have hInv : 0 < L⁻¹ := inv_pos.mpr hL
    have hbeta0 : 0 ≤ beta := hbeta.1
    linarith
  have hpole : Continuous pole := by
    dsimp only [pole]
    apply Continuous.rpow_const
    · fun_prop
    · intro beta
      left
      have hInv : 0 < L⁻¹ := inv_pos.mpr hL
      exact ne_of_gt (lt_of_lt_of_le (half_pos hInv)
        (le_max_right (L⁻¹ + beta) (L⁻¹ / 2)))
  have hpole0 : ∀ beta ∈ Icc (0 : ℝ) eta, 0 ≤ pole beta := by
    intro beta hbeta
    dsimp only [pole]
    exact Real.rpow_nonneg (by
      have hInv : 0 < L⁻¹ := inv_pos.mpr hL
      exact (lt_of_lt_of_le (half_pos hInv)
        (le_max_right (L⁻¹ + beta) (L⁻¹ / 2))).le) _
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
  have hpoint : ∀ alpha,
      ∀ beta ∈ Icc (0 : ℝ) eta, F alpha beta ≤ G alpha beta := by
    intro alpha beta hbeta
    dsimp only [F, G]
    exact mul_le_mul_of_nonneg_right
      (sourcePerron_rpow_mul_symmetricBetaGrowth_le
        hy hyX hX hbeta.1) (hpole0 beta hbeta)
  have hinner (alpha : ℝ) :
      (∫ beta : ℝ in 0..eta, F alpha beta) ≤
        ∫ beta : ℝ in 0..eta, G alpha beta := by
    apply intervalIntegral.integral_mono_on heta
    · exact (hF.comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _
    · exact (hG.comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _
    · exact fun beta hbeta ↦ hpoint alpha beta hbeta
  have hinnerF : Continuous (fun alpha : ℝ ↦
      ∫ beta : ℝ in 0..eta, F alpha beta) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      hF 0 eta
  have hinnerG : Continuous (fun alpha : ℝ ↦
      ∫ beta : ℝ in 0..eta, G alpha beta) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      hG 0 eta
  have houter :
      (∫ alpha : ℝ in 0..eta, ∫ beta : ℝ in 0..eta, F alpha beta) ≤
        ∫ alpha : ℝ in 0..eta, ∫ beta : ℝ in 0..eta, G alpha beta := by
    apply intervalIntegral.integral_mono_on heta
    · exact hinnerF.intervalIntegrable _ _
    · exact hinnerG.intervalIntegrable _ _
    · intro alpha halpha
      exact hinner alpha
  have hpoleInt := intervalIntegral_inv_log_add_rpow_neg_three_halves_le
    hL heta
  have hpoleSafeInt :
      (∫ beta : ℝ in 0..eta, pole beta) =
        ∫ beta : ℝ in 0..eta, (L⁻¹ + beta) ^ (-3 / 2 : ℝ) := by
    apply intervalIntegral.integral_congr
    intro beta hbeta
    have hbeta' : beta ∈ Icc (0 : ℝ) eta := by
      simpa only [uIcc_of_le heta] using hbeta
    exact hpoleEq beta hbeta'
  have halpha := intervalIntegral_rpow_one_sub_le_div_log hX heta
  have htarget :
      (∫ alpha : ℝ in 0..eta,
        ∫ beta : ℝ in 0..eta,
          ((X : ℝ) ^
              (Erdos67.EulerResidue.taoExponent X - alpha - beta) *
            ((X / y : ℕ) : ℝ) ^ beta) *
              ((Real.log (X : ℝ))⁻¹ + beta) ^ (-3 / 2 : ℝ)) =
        ∫ alpha : ℝ in 0..eta,
          ∫ beta : ℝ in 0..eta, F alpha beta := by
    apply intervalIntegral.integral_congr
    intro alpha halpha
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
        (2 * Real.sqrt (Real.log (X : ℝ))) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left halpha (Real.exp_nonneg 1)
      · rw [hpoleSafeInt]
        simpa only [L] using hpoleInt
      · exact intervalIntegral.integral_nonneg heta
          (fun beta hbeta ↦ hpole0 beta hbeta)
      · exact mul_nonneg (Real.exp_nonneg 1) (by positivity)
    _ = 2 * Real.exp 1 * ((X : ℝ) / Real.log (X : ℝ)) *
        Real.sqrt (Real.log (X : ℝ)) := by ring

end

end Erdos67.MRHalaszBands

#print axioms
  Erdos67.MRHalaszBands.doubleIntervalIntegral_sourcePerron_symmetricBetaPole_le
