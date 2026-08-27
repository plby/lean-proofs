/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.SourcePrimeIntervalRelativeCount
import ErdosProblems.Erdos4b.FGKMTPinnedPrimeExpansion
import ErdosProblems.Erdos4b.FGKMTDimensionLogLoss
import ErdosProblems.Erdos4b.FGKMTPresieveDensityLower

/-!
# A lower count for the actual upper-half prime set

The previously proved prime-number estimate is used on a contained
half-open interval. No prime-counting hypothesis remains in this result.
-/

namespace Erdos4b.FGKMT

noncomputable section

open Filter

theorem eventually_commonPinnedPrimeSet_half_card_lower :
    ∀ᶠ x : ℕ in atTop,
      (x : ℝ) / (8 * Real.log (x : ℝ)) ≤ (commonPinnedPrimeSet (x / 2) x).card := by
  filter_upwards [Erdos4b.eventually_primeInterval_card_lower 0 (by norm_num : (0 : ℝ) < 1 / 4),
    eventually_ge_atTop (4 : ℕ)] with x hx hx4
  have hhalf : x ≤ 2 * (x / 2 + 1) := by omega
  have hAB : x / 2 + 1 ≤ x := by omega
  have hquot : (x / 2 : ℕ) * 2 ≤ x := Nat.div_mul_le_self x 2
  have hquotR : (x / 2 : ℕ) * (2 : ℝ) ≤ x := by exact_mod_cast hquot
  have hxR : (4 : ℝ) ≤ x := by exact_mod_cast hx4
  have hlength : (1 / 4 : ℝ) * x / Real.log (x : ℝ) ^ 0 ≤
      (x : ℝ) - (x / 2 + 1 : ℕ) := by
    simp only [pow_zero, div_one, Nat.cast_add, Nat.cast_one]
    linarith
  have h := hx (x / 2 + 1) x hhalf hAB le_rfl hlength
  have hsubset : auxiliaryPrimeInterval (x / 2 + 1) x ⊆ commonPinnedPrimeSet (x / 2) x := by
    intro p hp
    simp only [auxiliaryPrimeInterval, Finset.mem_filter, Finset.mem_Ico] at hp
    exact mem_commonPinnedPrimeSet.mpr ⟨by omega, by omega, hp.2⟩
  calc
    _ = (1 / 4 : ℝ) * x / (2 * Real.log (x : ℝ) ^ (0 + 1)) := by norm_num; ring
    _ ≤ (auxiliaryPrimeInterval (x / 2 + 1) x).card := h
    _ ≤ _ := by exact_mod_cast Finset.card_le_card hsubset

theorem inv_eight_log_ge_expScale {x : ℕ} (hlog : 1 ≤ Real.log (x : ℝ)) :
    Real.exp (-9 * dimensionLogLossScale x) ≤ 1 / (8 * Real.log (x : ℝ)) := by
  let S := dimensionLogLossScale x
  have hS : 1 ≤ S := one_le_dimensionLogLossScale x
  have hlogpos : 0 < Real.log (x : ℝ) := by linarith
  have hloglog : Real.log (Real.log (x : ℝ)) ≤ S := by
    have h := Real.log_le_log hlogpos (by linarith : Real.log (x : ℝ) ≤ 1 + Real.log (x : ℝ))
    dsimp [S, dimensionLogLossScale]
    linarith
  have hinvlog : Real.exp (-S) ≤ 1 / Real.log (x : ℝ) :=
    exp_neg_le_inv_of_le_exp hlogpos (Real.le_exp_of_log_le hloglog)
  have heighth : Real.exp (-8) ≤ (1 / 8 : ℝ) :=
    exp_neg_le_inv_of_le_exp (by norm_num) (by linarith [Real.add_one_le_exp 8])
  calc
    _ ≤ Real.exp (-8) * Real.exp (-S) := by
      rw [← Real.exp_add]
      apply Real.exp_monotone
      change -9 * S ≤ -8 + -S
      linarith
    _ ≤ (1 / 8 : ℝ) * (1 / Real.log (x : ℝ)) :=
      mul_le_mul heighth hinvlog (Real.exp_pos _).le (by norm_num)
    _ = _ := by ring

theorem eventually_commonPinnedPrimeSet_half_exp_lower :
    ∀ᶠ x : ℕ in atTop,
      (x : ℝ) * Real.exp (-9 * dimensionLogLossScale x) ≤
        (commonPinnedPrimeSet (x / 2) x).card := by
  have hlogTop : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_commonPinnedPrimeSet_half_card_lower,
    hlogTop.eventually (eventually_ge_atTop (1 : ℝ))] with x hx hlog
  calc
    _ ≤ (x : ℝ) * (1 / (8 * Real.log (x : ℝ))) :=
      mul_le_mul_of_nonneg_left (inv_eight_log_ge_expScale hlog) (Nat.cast_nonneg x)
    _ = (x : ℝ) / (8 * Real.log (x : ℝ)) := by ring
    _ ≤ _ := hx

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.eventually_commonPinnedPrimeSet_half_card_lower
#print axioms Erdos4b.FGKMT.eventually_commonPinnedPrimeSet_half_exp_lower
