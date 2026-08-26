import ErdosProblems.Erdos421.EncodedFrequencyMean
import Mathlib.Data.Rat.Lemmas
import Mathlib.Analysis.Real.Pi.Bounds

/-! # Mean-square estimates at rational frequencies of bounded denominator -/

namespace Erdos421

open MeasureTheory

theorem rational_frequency_separation {r s : ℚ} {M : ℕ}
    (hr : r.den ≤ M) (hs : s.den ≤ M) (hrs : r ≠ s) :
    1 / (M : ℝ) ^ 2 ≤ |(r : ℝ) - s| := by
  have hdenN : (r - s).den ≤ M ^ 2 :=
    (Nat.le_of_dvd (Nat.mul_pos r.den_pos s.den_pos) (Rat.sub_den_dvd r s)).trans
      (by simpa only [pow_two] using Nat.mul_le_mul hr hs)
  have hden : ((r - s).den : ℝ) ≤ (M : ℝ) ^ 2 := by exact_mod_cast hdenN
  have hdenpos : (0 : ℝ) < (r - s).den := by exact_mod_cast (r - s).den_pos
  have hnum : (1 : ℝ) ≤ |((r - s).num : ℝ)| := by
    exact_mod_cast Int.one_le_abs (Rat.num_ne_zero.mpr (sub_ne_zero.mpr hrs))
  calc
    _ ≤ 1 / ((r - s).den : ℝ) := one_div_le_one_div_of_le hdenpos hden
    _ ≤ |((r - s).num : ℝ)| / (r - s).den :=
      div_le_div_of_nonneg_right hnum hdenpos.le
    _ = _ := by
      rw [← Rat.cast_sub, Rat.cast_def, abs_div, abs_of_pos hdenpos]

theorem rational_frequency_mean_square_bound (S : Finset ℚ) (c : ℚ → ℂ)
    {M : ℕ} (hM : 0 < M) {R : ℝ}
    (hden : ∀ q ∈ S, q.den ≤ M) (hspan : ∀ q ∈ S, |(q : ℝ)| ≤ R) (a b : ℝ) :
    (∫ t in a..b, ‖∑ q ∈ S, c q * oscillatoryPhase (2 * Real.pi * q) t‖ ^ 2) ≤
      (b - a + 16 * M ^ 2 * Real.log (4 * Real.pi * R * M ^ 2 + 2)) *
        ∑ q ∈ S, ‖c q‖ ^ 2 := by
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hδ : 0 < 1 / (M : ℝ) ^ 2 := by positivity
  have hpi : 1 ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  have hω : ∀ q ∈ S, -(2 * Real.pi * R) ≤ 2 * Real.pi * (q : ℝ) ∧
      2 * Real.pi * (q : ℝ) ≤ 2 * Real.pi * R := by
    intro q hq
    have hq' := (abs_le.mp (hspan q hq))
    constructor <;> nlinarith [Real.pi_pos]
  have hsep : ∀ r ∈ S, ∀ s ∈ S, r ≠ s →
      1 / (M : ℝ) ^ 2 ≤ |2 * Real.pi * (r : ℝ) - 2 * Real.pi * (s : ℝ)| := by
    intro r hr s hs hrs
    have hb := rational_frequency_separation (hden r hr) (hden s hs) hrs
    rw [← mul_sub, abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
    nlinarith [abs_nonneg ((r : ℝ) - s)]
  have hb := separated_frequency_sum_bound S c (fun q ↦ 2 * Real.pi * (q : ℝ))
    hδ hω hsep a b
  have harg : (2 * Real.pi * R - -(2 * Real.pi * R)) / (1 / (M : ℝ) ^ 2) + 2 =
      4 * Real.pi * R * M ^ 2 + 2 := by field_simp; ring
  have hfactor : 16 / (1 / (M : ℝ) ^ 2) = 16 * M ^ 2 := by field_simp
  simpa only [harg, hfactor] using hb

end Erdos421
