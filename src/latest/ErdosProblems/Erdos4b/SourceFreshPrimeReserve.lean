/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.SourceIntervalAllocation
import ErdosProblems.Erdos4b.SourcePrimeIntervalRelativeCount
import ErdosProblems.Erdos4b.SourceDyadicAllocation

/-!
# Fresh primes after the allocated intervals

The reserve begins at the exact final prefix endpoint. The quarter-range
allocation leaves at least X/(16 log X) prime slots, uniformly in the
rounded total length, and these slots are disjoint from every interval.
-/

namespace Erdos4b

noncomputable section

open Filter
open scoped BigOperators Topology

theorem sourceFreshInterval_length {X total : ℕ} (hX : 4 ≤ X)
    (htotal : (total : ℝ) ≤ (X : ℝ) / 4) :
    X ≤ 2 * ((X + 1) / 2 + total) ∧ (X + 1) / 2 + total ≤ X ∧
      (X : ℝ) / 8 ≤ (X : ℝ) - ((X + 1) / 2 + total : ℕ) := by
  have hc := SmoothParameters.sourceAllocation_capacity_of_quarter_sum (by omega) htotal
  have hb : 2 * ((X + 1) / 2) ≤ X + 1 := by omega
  have hb' : (2 : ℝ) * ((X + 1) / 2 : ℕ) ≤ (X : ℝ) + 1 := by exact_mod_cast hb
  have hX' : (4 : ℝ) ≤ X := by exact_mod_cast hX
  refine ⟨by omega, hc.2, ?_⟩
  rw [Nat.cast_add]
  linarith

theorem eventually_sourceFreshPrimeCount_ge :
    ∀ᶠ X : ℕ in atTop, ∀ total : ℕ, (total : ℝ) ≤ (X : ℝ) / 4 →
      (X : ℝ) / (16 * Real.log X) ≤
        (auxiliaryPrimeInterval ((X + 1) / 2 + total) X).card := by
  have hlogTop : Tendsto (fun X : ℕ ↦ Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop 4, hlogTop.eventually_ge_atTop 1,
    eventually_primeInterval_card_ge_half_length 0 (by norm_num : (0 : ℝ) < 1 / 8)]
    with X hX hlog hprime
  intro total htotal
  have hf := sourceFreshInterval_length hX htotal
  have hcount := hprime ((X + 1) / 2 + total) X hf.1 hf.2.1 le_rfl
    (by simpa only [pow_zero, div_one, one_div_mul_eq_div] using hf.2.2)
  calc
    _ = ((X : ℝ) / 8) / (2 * Real.log X) := by ring
    _ ≤ ((X : ℝ) - ((X + 1) / 2 + total : ℕ)) / (2 * Real.log X) :=
      div_le_div_of_nonneg_right hf.2.2 (by linarith)
    _ ≤ _ := hcount

theorem sourceAllocated_disjoint_fresh {E : Finset ℕ} (length : ℕ → ℕ)
    (base X : ℕ) {m : ℕ} (hm : m ∈ E) :
    Disjoint
      (auxiliaryPrimeInterval (sourceAllocatedStart E length base m)
        (sourceAllocatedEnd E length base m))
      (auxiliaryPrimeInterval (base + ∑ j ∈ E, length j) X) := by
  rw [Finset.disjoint_left]
  intro q hqA hqR
  have hqA' := mem_auxiliaryPrimeInterval.mp hqA
  have hqR' := mem_auxiliaryPrimeInterval.mp hqR
  have hend := sourceAllocatedEnd_le_total length base hm
  omega

end

end Erdos4b
