import ErdosProblems.Erdos67b.MRCofactorProjectionScales
import ErdosProblems.Erdos67b.MRTypicalCofactorSecondaries

/-! # A small fixed-power secondary budget and a vanishing remainder -/

open Filter
open scoped Topology

namespace Erdos67b

open MRHalaszBands

noncomputable section

def mrCofactorSecondaryMeanConstant : ℝ :=
  2 * (gsA10ShiuConstant + mrTypicalCofactorSecondSecondaryPrimeConstant)

theorem mrCofactorSecondaryMeanConstant_nonneg : 0 ≤ mrCofactorSecondaryMeanConstant := by
  exact mul_nonneg (by norm_num) (add_nonneg gsA10ShiuConstant_nonneg
    mrTypicalCofactorSecondSecondaryPrimeConstant_nonneg)

def mrCofactorSecondaryRemainder (delta : ℝ) (X : ℕ) : ℝ :=
  mrTypicalCofactorSecondSecondaryPrimeConstant / Real.log (X : ℝ) +
    12 * Real.log (X : ℝ) ^ 2 / mrCofactorPowerCutoff delta X

theorem mrTendsto_cofactorSecondaryRemainder {delta : ℝ} (hdelta : 0 < delta) :
    Tendsto (mrCofactorSecondaryRemainder delta) atTop (𝓝 0) := by
  have hfirst := EulerSubpower.tendsto_log_nat_atTop.const_div_atTop
    mrTypicalCofactorSecondSecondaryPrimeConstant
  have hsecond := (mrTendsto_log_pow_div_cofactorPowerCutoff hdelta 2).const_mul 12
  change Tendsto (fun X : ℕ ↦ mrTypicalCofactorSecondSecondaryPrimeConstant / Real.log (X : ℝ) +
    12 * Real.log (X : ℝ) ^ 2 / mrCofactorPowerCutoff delta X) atTop (𝓝 0)
  simpa only [mrCofactorSecondaryRemainder, mul_div_assoc, mul_zero, zero_add] using hfirst.add hsecond

theorem mrEventually_cofactorSecondary_le {delta : ℝ} (hdelta : 0 < delta) :
    ∀ᶠ X : ℕ in atTop,
      mrTypicalCofactorSecondaryBound (mrCofactorPowerCutoff delta X) X ≤
        mrCofactorSecondaryMeanConstant * delta + mrCofactorSecondaryRemainder delta X := by
  filter_upwards [mrEventually_cofactorPowerCutoff_log_upper hdelta,
    mrEventually_primeReciprocals_le_log, eventually_ge_atTop 2] with X hcut hprime hX
  have hL : 0 < Real.log (X : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hS := gsA10ShiuConstant_nonneg
  have hP := mrTypicalCofactorSecondSecondaryPrimeConstant_nonneg
  have hfirst : (gsA10ShiuConstant * Real.log (mrCofactorPowerCutoff delta X : ℝ) +
      mrTypicalCofactorSecondSecondaryPrimeConstant * (1 + Real.log (mrCofactorPowerCutoff delta X : ℝ))) /
        Real.log (X : ℝ) ≤ mrCofactorSecondaryMeanConstant * delta +
          mrTypicalCofactorSecondSecondaryPrimeConstant / Real.log (X : ℝ) := by
    calc
      _ = (gsA10ShiuConstant + mrTypicalCofactorSecondSecondaryPrimeConstant) *
          Real.log (mrCofactorPowerCutoff delta X : ℝ) / Real.log (X : ℝ) +
          mrTypicalCofactorSecondSecondaryPrimeConstant / Real.log (X : ℝ) := by ring
      _ ≤ (gsA10ShiuConstant + mrTypicalCofactorSecondSecondaryPrimeConstant) *
          (2 * delta * Real.log (X : ℝ)) / Real.log (X : ℝ) +
          mrTypicalCofactorSecondSecondaryPrimeConstant / Real.log (X : ℝ) := by
        gcongr
      _ = _ := by unfold mrCofactorSecondaryMeanConstant; field_simp
  have hsecond : 12 * Real.log (X : ℝ) / mrCofactorPowerCutoff delta X *
      PrimeEstimates.primeReciprocals X ≤ 12 * Real.log (X : ℝ) ^ 2 / mrCofactorPowerCutoff delta X := by
    calc
      _ ≤ 12 * Real.log (X : ℝ) / mrCofactorPowerCutoff delta X * Real.log (X : ℝ) :=
        mul_le_mul_of_nonneg_left hprime (by positivity)
      _ = _ := by ring
  exact (add_le_add hfirst hsecond).trans_eq (by
    unfold mrCofactorSecondaryRemainder
    ring)

end

end Erdos67b
