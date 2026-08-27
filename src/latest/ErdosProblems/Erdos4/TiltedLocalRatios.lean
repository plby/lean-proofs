import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

/-!
# Elementary local correlation bounds

The negative quadratic terms in the avoidance ratios may be retained.
This gives bounds in terms of common forbidden residues alone, stronger
than the Taylor bounds used in Sections 4 and 5 of the manuscript.
-/

namespace Erdos4.Tilted

theorem quotient_le_one_add_four {N D c : ℝ}
    (hD : 1 / 4 ≤ D) (hc : 0 ≤ c) (hN : N - D ≤ c) :
    N / D ≤ 1 + 4 * c := by
  apply (div_le_iff₀ (show 0 < D by linarith)).mpr
  nlinarith [mul_nonneg hc (show 0 ≤ D - 1 / 4 by linarith)]

theorem avoidance_denominator_ge {a b : ℝ} (ha : a ≤ 1 / 2) (hb : b ≤ 1 / 2) :
    1 / 4 ≤ (1 - a) * (1 - b) := by
  have hh := mul_le_mul (show (1 / 2 : ℝ) ≤ 1 - a by linarith)
    (show (1 / 2 : ℝ) ≤ 1 - b by linarith) (by norm_num) (show 0 ≤ 1 - a by linarith)
  norm_num at hh ⊢
  exact hh

theorem avoidance_ratio_le {a b c : ℝ} (ha0 : 0 ≤ a) (hb0 : 0 ≤ b)
    (ha : a ≤ 1 / 2) (hb : b ≤ 1 / 2) (hc : 0 ≤ c) :
    (1 - (a + b - c)) / ((1 - a) * (1 - b)) ≤ 1 + 4 * c := by
  apply quotient_le_one_add_four (avoidance_denominator_ge ha hb) hc
  nlinarith [mul_nonneg ha0 hb0]

theorem tilted_avoidance_ratio_le {a b c β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (ha : a ≤ 1 / 2) (hb : b ≤ 1 / 2) (hc : 0 ≤ c) :
    (1 - β * (a + b - c)) / ((1 - β * a) * (1 - β * b)) ≤ 1 + 4 * c := by
  have hβa : β * a ≤ a := mul_le_of_le_one_left ha0 hβ1
  have hβb : β * b ≤ b := mul_le_of_le_one_left hb0 hβ1
  have hβc : β * c ≤ c := mul_le_of_le_one_left hc hβ1
  have hh := avoidance_ratio_le (mul_nonneg hβ0 ha0) (mul_nonneg hβ0 hb0)
    (hβa.trans ha) (hβb.trans hb) (mul_nonneg hβ0 hc)
  have heq : 1 - β * (a + b - c) = 1 - (β * a + β * b - β * c) := by ring
  rw [heq]
  exact hh.trans (by linarith)

theorem mixed_avoidance_ratio_le {a b c β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (ha : a ≤ 1 / 2) (hb : b ≤ 1 / 2) (hc : 0 ≤ c) :
    (1 - (a + b - c)) / ((1 - a) * (1 - β * b)) ≤ 1 + 4 * c := by
  have hβb : β * b ≤ b := mul_le_of_le_one_left hb0 hβ1
  have hD := avoidance_denominator_ge ha (hβb.trans hb)
  calc
    _ ≤ (1 - (a + β * b - c)) / ((1 - a) * (1 - β * b)) :=
      div_le_div_of_nonneg_right (by linarith) (by linarith)
    _ ≤ _ := avoidance_ratio_le ha0 (mul_nonneg hβ0 hb0) ha (hβb.trans hb) hc

theorem rooted_avoidance_ratio_le {a b c r : ℝ}
    (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (hr0 : 0 ≤ r)
    (ha : r + a ≤ 1 / 2) (hb : r + b ≤ 1 / 2) (hc : 0 ≤ c) :
    ((1 - r) * (1 - r - a - b + c)) / ((1 - r - a) * (1 - r - b)) ≤
      1 + 4 * c := by
  apply quotient_le_one_add_four (by simpa only [sub_add_eq_sub_sub] using avoidance_denominator_ge ha hb) hc
  nlinarith [mul_nonneg ha0 hb0, mul_nonneg hr0 hc]

theorem rooted_mixed_avoidance_ratio_le {a b c d β : ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (hd0 : 0 ≤ d)
    (ha : d + a ≤ 1 / 2) (hb : d + b ≤ 1 / 2) (hc : 0 ≤ c) :
    ((1 - β * d) * (1 - d - a - b + c)) /
        ((1 - d - a) * (1 - β * (d + b))) ≤ 1 + 4 * c := by
  have hβd : β * d ≤ d := mul_le_of_le_one_left hd0 hβ1
  have hβb : β * b ≤ b := mul_le_of_le_one_left hb0 hβ1
  have hβdb : β * (d + b) ≤ 1 / 2 :=
    (mul_le_of_le_one_left (add_nonneg hd0 hb0) hβ1).trans hb
  have hfactor : 0 ≤ 1 - β * d := by linarith
  have hD := avoidance_denominator_ge ha hβdb
  have hh := rooted_avoidance_ratio_le (show 0 ≤ d + a - β * d by linarith)
    (mul_nonneg hβ0 hb0) (mul_nonneg hβ0 hd0)
    (show β * d + (d + a - β * d) ≤ 1 / 2 by linarith)
    (show β * d + β * b ≤ 1 / 2 by nlinarith) hc
  have heq :
      ((1 - β * d) * (1 - β * d - (d + a - β * d) - β * b + c)) /
          ((1 - β * d - (d + a - β * d)) * (1 - β * d - β * b)) =
      ((1 - β * d) * (1 - d - a - β * b + c)) /
          ((1 - d - a) * (1 - β * (d + b))) := by ring
  rw [heq] at hh
  apply le_trans _ hh
  apply div_le_div_of_nonneg_right _ (by nlinarith)
  exact mul_le_mul_of_nonneg_left (by linarith) hfactor

end Erdos4.Tilted
