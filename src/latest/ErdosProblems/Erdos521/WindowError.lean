/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Normalized probability bounds for coefficient-window truncation.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.WindowVariance

namespace Erdos521

theorem window_Ico_subset_range {L U N : ℕ} (hUN : U ≤ N) : Finset.Ico L U ⊆ Finset.range N := by
  intro k hk
  exact Finset.mem_range.mpr ((Finset.mem_Ico.mp hk).2.trans_le hUN)

theorem windowPowerSum_normalized_error {x t : ℝ} (hx : 0 ≤ x) (hx₁ : x < 1) (ht : 0 < t)
    {L U N : ℕ} (hLU : L ≤ U) (hUN : U ≤ N) (htail : x ^ (2 * N) ≤ 1 / 2) :
    sequenceLaw.real {ε | t * Real.sqrt (geometricVariance x N) ≤
      |powerSum ε N x - windowPowerSum ε (Finset.Ico L U) x|} ≤
      4 * ((L : ℝ) * (1 - x) + x ^ (2 * U)) / t ^ 2 := by
  have hV : 0 < geometricVariance x N :=
    (inv_pos.mpr (by positivity : 0 < 4 * (1 - x))).trans_le (geometricVariance_lower hx₁ N htail)
  have h := windowPowerSum_error_probability (window_Ico_subset_range (L := L) hUN) x
    (mul_pos ht (Real.sqrt_pos.mpr hV))
  rw [mul_pow, Real.sq_sqrt hV.le] at h
  apply h.trans
  calc
    _ ≤ (4 * ((L : ℝ) * (1 - x) + x ^ (2 * U)) * geometricVariance x N) /
        (t ^ 2 * geometricVariance x N) :=
      div_le_div_of_nonneg_right (omitted_geometricVariance_normalized hx hx₁ hLU hUN htail) (by positivity)
    _ = _ := by field_simp

end Erdos521
