/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Variance comparisons for disks whose radii scale with distance to the endpoint.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.EndpointScale

namespace Erdos521

theorem geometricVariance_le_one_div {x : ℝ} (hx : 0 ≤ x) (hx₁ : x < 1) (N : ℕ) :
    geometricVariance x N ≤ 1 / (1 - x) := by
  have hV := geometricVariance_nonneg x N
  have hid := geometricVariance_mul_one_sub_sq x N
  have hden : 1 - x ≤ 1 - x ^ 2 := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hden hV
  apply (le_div_iff₀ (sub_pos.mpr hx₁)).mpr
  nlinarith [pow_nonneg hx (2 * N)]

theorem local_boundary_variance_le (n : ℕ) {x : ℝ} (hx : 0 ≤ x) (hx₁ : x < 1)
    (htail : x ^ (2 * (n + 1)) ≤ 1 / 2) :
    1 + geometricVariance (x + 4 * ((1 - x) / 8)) (n + 1) ≤
      12 * geometricVariance x (n + 1) := by
  have hL : 0 < 1 - x := sub_pos.mpr hx₁
  have hy₀ : 0 ≤ x + 4 * ((1 - x) / 8) := by positivity
  have hy₁ : x + 4 * ((1 - x) / 8) < 1 := by linarith
  have hupper : geometricVariance (x + 4 * ((1 - x) / 8)) (n + 1) ≤ 2 / (1 - x) := by
    apply (geometricVariance_le_one_div hy₀ hy₁ (n + 1)).trans_eq
    rw [show 1 - (x + 4 * ((1 - x) / 8)) = (1 - x) / 2 by ring]
    field_simp
  have hlower := geometricVariance_lower hx₁ (n + 1) htail
  calc
    1 + geometricVariance (x + 4 * ((1 - x) / 8)) (n + 1) ≤ 1 + 2 / (1 - x) :=
      add_le_add le_rfl hupper
    _ ≤ 3 / (1 - x) := by
      apply (le_div_iff₀ hL).mpr
      rw [add_mul, div_mul_cancel₀ _ hL.ne', one_mul]
      linarith
    _ = 12 * (4 * (1 - x))⁻¹ := by field_simp; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hlower (by norm_num)

end Erdos521
