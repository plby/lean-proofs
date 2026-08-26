/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierPinnedSingularSeries

/-!
# Exact lower bounds for the combined pinned singular factors

After cancellation of the normalizing powers, every non-cofactor rough
factor is at least one. Every cofactor factor dominates `(p-2)/(p-1)`.
These are exact inequalities, with no asymptotic remainder.
-/

namespace Erdos4b

theorem one_le_pinned_noncofactor_ratio {k p : ℝ} (hk : 1 ≤ k) (hp : 2 * k < p) :
    1 ≤ (1 - 1 / p) ^ 2 * (1 - (2 * k - 2) / p) / (1 - 2 * k / p) := by
  have hp0 : 0 < p := by linarith
  have hden : 0 < 1 - 2 * k / p := sub_pos.mpr ((div_lt_one hp0).mpr hp)
  apply (le_div_iff₀ hden).mpr
  rw [one_mul]
  have hid : (1 - 1 / p) ^ 2 * (1 - (2 * k - 2) / p) - (1 - 2 * k / p) =
      (2 * (k - 1) * (2 * p - 1) + p) / p ^ 3 := by
    field_simp
    ring
  have hn : 0 ≤ (2 * (k - 1) * (2 * p - 1) + p) / p ^ 3 := by
    have hk0 : 0 ≤ k - 1 := by linarith
    have hp1 : 0 ≤ 2 * p - 1 := by linarith
    positivity
  linarith

theorem one_sub_inv_le_pinned_cofactor_ratio {k p : ℝ} (hk : 1 ≤ k) (hp : k < p) :
    1 - 1 / p ≤ (1 - 1 / p) ^ 2 * (1 - (k - 1) / p) / (1 - k / p) := by
  have hp0 : 0 < p := by linarith
  have hpk : 0 < p - k := by linarith
  have hden : 1 - k / p ≠ 0 := (sub_pos.mpr ((div_lt_one hp0).mpr hp)).ne'
  have hid : (1 - 1 / p) ^ 2 * (1 - (k - 1) / p) / (1 - k / p) - (1 - 1 / p) =
      (p - 1) * (k - 1) / (p ^ 2 * (p - k)) := by
    field_simp
    ring
  have hn : 0 ≤ (p - 1) * (k - 1) / (p ^ 2 * (p - k)) := by
    have hk0 : 0 ≤ k - 1 := by linarith
    have hp1 : 0 ≤ p - 1 := by linarith
    positivity
  linarith

theorem cofactor_residual_factor_le_one_sub_inv {p : ℝ} (hp : 1 < p) :
    (p - 2) / (p - 1) ≤ 1 - 1 / p := by
  have hp0 : 0 < p := by linarith
  have hp1 : 0 < p - 1 := by linarith
  have hid : (1 - 1 / p) - (p - 2) / (p - 1) = 1 / (p * (p - 1)) := by
    field_simp
    ring
  have hn : 0 ≤ 1 / (p * (p - 1)) := by positivity
  linarith

end Erdos4b
