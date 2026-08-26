/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
The sharp asymptotic counting lower bound at every sufficiently large cardinality.
Informal source: the BBMST lower construction; the passage between cardinalities
uses the unconditional doubling injection instead of specialized frame padding.
Formal author: OpenAI Codex.
-/

import ErdosProblems.Erdos1189.CountMonotone
import ErdosProblems.Erdos1189.CountingDensity
import ErdosProblems.Erdos1189.CountingNormalization

namespace Erdos1189

open Filter Asymptotics
open scoped Asymptotics

lemma precedingFrameSize_log_ratio :
    Tendsto (fun k : ℕ => Real.log k /
      Real.log (countingSize (precedingFrameIndex k : ℝ))) atTop (nhds 1) := by
  have hk0 : ∀ᶠ k : ℕ in atTop, (k : ℝ) ≠ 0 := by
    filter_upwards [eventually_ge_atTop 1] with k hk
    exact_mod_cast (show k ≠ 0 by omega)
  have heq : (fun k : ℕ => (countingSize (precedingFrameIndex k : ℝ) : ℝ)) ~[atTop]
      (fun k : ℕ => (k : ℝ)) :=
    (isEquivalent_iff_tendsto_one hk0).mpr precedingFrameSize_ratio
  have hlog0 : ∀ᶠ k : ℕ in atTop, Real.log k ≠ 0 := by
    filter_upwards [eventually_ge_atTop 2] with k hk
    exact (Real.log_pos (by exact_mod_cast (show 1 < k by omega))).ne'
  have hlog := (isEquivalent_iff_tendsto_one hlog0).mp
    (heq.log tendsto_natCast_atTop_atTop)
  have ht := hlog.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  simpa only [inv_one, Pi.div_apply, inv_div] using ht

lemma precedingFrameSize_normalization_ratio :
    Tendsto (fun k : ℕ =>
      ((countingSize (precedingFrameIndex k : ℝ) : ℝ) / k) *
        Real.sqrt ((countingSize (precedingFrameIndex k : ℝ) : ℝ) / k) *
          Real.sqrt (Real.log k / Real.log (countingSize (precedingFrameIndex k : ℝ))))
      atTop (nhds 1) := by
  have ht := (precedingFrameSize_ratio.mul precedingFrameSize_ratio.sqrt).mul
    precedingFrameSize_log_ratio.sqrt
  simpa only [Real.sqrt_one, mul_one] using ht

lemma normalization_transfer_eq {n k : ℝ} (hn : 1 < n) (hk : 0 < k) (L : ℝ) :
    (L * Real.sqrt (Real.log n) / (n * Real.sqrt n)) *
      ((n / k) * Real.sqrt (n / k) * Real.sqrt (Real.log k / Real.log n)) =
        L * Real.sqrt (Real.log k) / (k * Real.sqrt k) := by
  have hn0 := (zero_lt_one.trans hn).ne'
  have hk0 := hk.ne'
  have hsn0 := (Real.sqrt_pos.mpr (zero_lt_one.trans hn)).ne'
  have hsk0 := (Real.sqrt_pos.mpr hk).ne'
  have hsln0 := (Real.sqrt_pos.mpr (Real.log_pos hn)).ne'
  rw [Real.sqrt_div (zero_lt_one.trans hn).le, Real.sqrt_div' _ (Real.log_pos hn).le]
  field_simp

lemma irreducibleCount_pos {k : ℕ} (hk : 5 ≤ k) : 0 < irreducibleCount k :=
  (Set.ncard_pos (finite_irreducibleSetsOfSize k)).mpr
    (irreducibleSetsOfSize_nonempty_iff.mpr hk)

/-- The lower half of the requested counting asymptotic, for all large `k`. -/
theorem irreducibleCount_eventually_lower {b : ℝ} (hb : b < 4 * Real.sqrt tau / 3) :
    ∀ᶠ k : ℕ in atTop,
      b < Real.log (irreducibleCount k) * Real.sqrt (Real.log k) /
        ((k : ℝ) * Real.sqrt k) := by
  have hA : 0 < 4 * Real.sqrt tau / 3 :=
    div_pos (mul_pos (by norm_num) (Real.sqrt_pos.mpr tau_pos)) (by norm_num)
  have hf : ∀ a < 4 * Real.sqrt tau / 3, ∀ᶠ k : ℕ in atTop,
      a < Real.log (irreducibleCount (countingSize (precedingFrameIndex k : ℝ))) *
        Real.sqrt (Real.log (countingSize (precedingFrameIndex k : ℝ))) /
          ((countingSize (precedingFrameIndex k : ℝ) : ℝ) *
            Real.sqrt (countingSize (precedingFrameIndex k : ℝ))) := by
    intro a ha
    exact precedingFrameIndex_real_tendsto.eventually (counting_frame_cardinality_lower ha)
  have ht := eventually_mul_lower_of_tendsto hA (by norm_num : (0 : ℝ) < 1) hf
    precedingFrameSize_normalization_ratio (by simpa only [mul_one] using hb)
  have hsize := (countingSize_tendsto.comp precedingFrameIndex_real_tendsto).eventually
    (eventually_ge_atTop 5)
  filter_upwards [ht, hsize, eventually_ge_atTop 1] with k hk hn hk1
  change 5 ≤ countingSize (precedingFrameIndex k : ℝ) at hn
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hn1 : (1 : ℝ) < countingSize (precedingFrameIndex k : ℝ) := by
    exact_mod_cast (show 1 < countingSize (precedingFrameIndex k : ℝ) by omega)
  have hlower : countingSize (precedingFrameIndex k : ℝ) ≤ k := precedingFrameIndex_lower hk1
  have hlog : Real.log (irreducibleCount (countingSize (precedingFrameIndex k : ℝ))) ≤
      Real.log (irreducibleCount k) := Real.log_le_log
    (by exact_mod_cast irreducibleCount_pos hn) (by exact_mod_cast irreducibleCount_mono hlower)
  have hsmall : b < Real.log (irreducibleCount (countingSize (precedingFrameIndex k : ℝ))) *
      Real.sqrt (Real.log k) / ((k : ℝ) * Real.sqrt k) := by
    simpa only [normalization_transfer_eq hn1 hk0] using hk
  exact hsmall.trans_le (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right hlog (Real.sqrt_nonneg _))
    (mul_nonneg hk0.le (Real.sqrt_nonneg _)))

end Erdos1189
