import ErdosProblems.Erdos67.MRGSA10RpowAverage
import ErdosProblems.Erdos67.MRGSA10PerronErrorSchedule

/-!
# The moving-line power saving in the GS A.10 Perron error

The lower generalized-Mangoldt window on the A.10 Perron line can cost the
factor `X ^ (1 - min (c - beta) 1)`.  It must be combined with the original
Perron power before the auxiliary variables are bounded.  The `beta` growth
then cancels, leaving the decaying alpha average `X ^ (1 - alpha)`.
-/

open Set MeasureTheory

namespace Erdos67.MRHalaszBands

noncomputable section

/-- Pointwise cancellation between the moving Perron power and the possible
left-line growth of the lower generalized-Mangoldt window. -/
theorem sourcePerron_rpow_mul_leftGrowth_le
    {X : ℕ} (hX : 1 < X) {alpha beta : ℝ} (hbeta : 0 ≤ beta) :
    (X : ℝ) ^
          (Erdos67.EulerResidue.taoExponent X - alpha - beta) *
        (X : ℝ) ^
          (1 - min (Erdos67.EulerResidue.taoExponent X - beta) 1) ≤
      Real.exp 1 * (X : ℝ) ^ (1 - alpha) := by
  let c : ℝ := Erdos67.EulerResidue.taoExponent X
  have hXR : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hXone : (1 : ℝ) ≤ X := by exact_mod_cast (show 1 ≤ X by omega)
  have hlog : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast hX)
  have hcOne : 1 ≤ c := by
    dsimp only [c, Erdos67.EulerResidue.taoExponent]
    exact le_add_of_nonneg_right (inv_pos.mpr hlog).le
  have hmin : 1 - beta ≤ min (c - beta) 1 := by
    apply le_min
    · linarith
    · linarith
  have hexponent :
      (c - alpha - beta) + (1 - min (c - beta) 1) ≤ c - alpha := by
    linarith
  have hmono :
      (X : ℝ) ^
          ((c - alpha - beta) + (1 - min (c - beta) 1)) ≤
        (X : ℝ) ^ (c - alpha) :=
    Real.rpow_le_rpow_of_exponent_le hXone hexponent
  have hpowInv :
      (X : ℝ) ^ (Real.log (X : ℝ))⁻¹ = Real.exp 1 := by
    rw [Real.rpow_def_of_pos hXR]
    congr 1
    exact mul_inv_cancel₀ hlog.ne'
  calc
    (X : ℝ) ^ (c - alpha - beta) *
        (X : ℝ) ^ (1 - min (c - beta) 1) =
        (X : ℝ) ^
          ((c - alpha - beta) + (1 - min (c - beta) 1)) := by
      rw [Real.rpow_add hXR]
    _ ≤ (X : ℝ) ^ (c - alpha) := hmono
    _ = (X : ℝ) ^ ((1 - alpha) + (Real.log (X : ℝ))⁻¹) := by
      congr 1
      dsimp only [c, Erdos67.EulerResidue.taoExponent]
      ring
    _ = (X : ℝ) ^ (1 - alpha) * Real.exp 1 := by
      rw [Real.rpow_add hXR, hpowInv]
    _ = Real.exp 1 * (X : ℝ) ^ (1 - alpha) := mul_comm _ _

/-- The same cancellation on the beta-dependent Perron line which keeps
the high Dirichlet factor fixed at the Halasz point. -/
theorem sourcePerron_fixedHigh_rpow_mul_leftGrowth_le
    {X : ℕ} (hX : 1 < X) {alpha beta : ℝ} (hbeta : 0 ≤ beta) :
    (X : ℝ) ^
          (Erdos67.EulerResidue.taoExponent X - alpha - 2 * beta) *
        (X : ℝ) ^
          (1 - min
            (Erdos67.EulerResidue.taoExponent X - 2 * beta) 1) ≤
      Real.exp 1 * (X : ℝ) ^ (1 - alpha) := by
  simpa only using
    (sourcePerron_rpow_mul_leftGrowth_le
      hX (alpha := alpha) (beta := 2 * beta) (by positivity))

/-- After averaging over the source square, the moving-line growth costs
only `eta / log X`.  In particular the beta interval contributes its length,
whereas the alpha interval supplies the decisive logarithmic saving. -/
theorem doubleIntervalIntegral_sourcePerron_rpow_mul_leftGrowth_le
    {X : ℕ} (hX : 1 < X) {eta : ℝ} (heta : 0 ≤ eta) :
    (∫ alpha : ℝ in 0..eta,
      ∫ beta : ℝ in 0..eta,
        (X : ℝ) ^
            (Erdos67.EulerResidue.taoExponent X - alpha - beta) *
          (X : ℝ) ^
            (1 - min
              (Erdos67.EulerResidue.taoExponent X - beta) 1)) ≤
      Real.exp 1 * eta * ((X : ℝ) / Real.log (X : ℝ)) := by
  let F : ℝ → ℝ → ℝ := fun alpha beta ↦
    (X : ℝ) ^
        (Erdos67.EulerResidue.taoExponent X - alpha - beta) *
      (X : ℝ) ^
        (1 - min (Erdos67.EulerResidue.taoExponent X - beta) 1)
  let G : ℝ → ℝ := fun alpha ↦ Real.exp 1 * (X : ℝ) ^ (1 - alpha)
  have hXne : (X : ℝ) ≠ 0 := by
    exact_mod_cast (show X ≠ 0 by omega)
  have hF : Continuous (Function.uncurry F) := by
    dsimp only [F, Function.uncurry_apply_pair]
    exact ((Real.continuous_const_rpow hXne).comp
      (by fun_prop)).mul
      ((Real.continuous_const_rpow hXne).comp (by fun_prop))
  have hG : Continuous G := by
    dsimp only [G]
    exact continuous_const.mul
      ((Real.continuous_const_rpow hXne).comp (by fun_prop))
  have hinnerContinuous : Continuous (fun alpha : ℝ ↦
      ∫ beta : ℝ in 0..eta, F alpha beta) := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    exact hF
  have hinner (alpha : ℝ) :
      (∫ beta : ℝ in 0..eta, F alpha beta) ≤ eta * G alpha := by
    calc
      (∫ beta : ℝ in 0..eta, F alpha beta) ≤
          ∫ beta : ℝ in 0..eta, G alpha := by
        apply intervalIntegral.integral_mono_on heta
        · exact (hF.comp
            (continuous_const.prodMk continuous_id)).intervalIntegrable 0 eta
        · exact continuous_const.intervalIntegrable 0 eta
        · intro beta hbeta
          exact sourcePerron_rpow_mul_leftGrowth_le hX hbeta.1
      _ = eta * G alpha := by simp
  have houter :
      (∫ alpha : ℝ in 0..eta, ∫ beta : ℝ in 0..eta, F alpha beta) ≤
        ∫ alpha : ℝ in 0..eta, eta * G alpha := by
    apply intervalIntegral.integral_mono_on heta
    · exact hinnerContinuous.intervalIntegrable 0 eta
    · exact (hG.const_mul eta).intervalIntegrable 0 eta
    · intro alpha halpha
      exact hinner alpha
  have hdecay := intervalIntegral_rpow_one_sub_le_div_log hX heta
  change (∫ alpha : ℝ in 0..eta,
      ∫ beta : ℝ in 0..eta, F alpha beta) ≤ _
  calc
    (∫ alpha : ℝ in 0..eta, ∫ beta : ℝ in 0..eta, F alpha beta) ≤
        ∫ alpha : ℝ in 0..eta, eta * G alpha := houter
    _ = eta * Real.exp 1 *
          (∫ alpha : ℝ in 0..eta, (X : ℝ) ^ (1 - alpha)) := by
      simp only [G, intervalIntegral.integral_const_mul]
      ring
    _ ≤ eta * Real.exp 1 * ((X : ℝ) / Real.log (X : ℝ)) := by
      exact mul_le_mul_of_nonneg_left hdecay
        (mul_nonneg heta (Real.exp_nonneg 1))
    _ = Real.exp 1 * eta * ((X : ℝ) / Real.log (X : ℝ)) := by ring

end

end Erdos67.MRHalaszBands

#print axioms Erdos67.MRHalaszBands.sourcePerron_rpow_mul_leftGrowth_le
#print axioms
  Erdos67.MRHalaszBands.doubleIntervalIntegral_sourcePerron_rpow_mul_leftGrowth_le
