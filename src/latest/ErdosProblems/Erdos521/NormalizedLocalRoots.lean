/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Variance-normalized tails for local root counts at the natural spatial scale.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.SingleLocalRoots
import ErdosProblems.Erdos521.LocalVariance
import ErdosProblems.Erdos521.NormalizedSmallBall

namespace Erdos521

theorem localRootCount_normalized_probability_split (n k : ℕ) {x t : ℝ}
    (hx : 0 ≤ x) (hx₁ : x < 1) (ht : 0 < t)
    (htail : x ^ (2 * (n + 1)) ≤ 1 / 2) :
    sequenceLaw.real {ε | k ≤ localRootCount ε n x ((1 - x) / 8)} ≤
      sequenceLaw.real {ε | |powerSum ε (n + 1) x| ≤ t * Real.sqrt (geometricVariance x (n + 1))} +
        24 / (t ^ 2 * (4 : ℝ) ^ k) := by
  have hV := geometricVariance_succ_pos x n
  have hδ : 0 < t * Real.sqrt (geometricVariance x (n + 1)) := mul_pos ht (Real.sqrt_pos.mpr hV)
  have h := localRootCount_single_probability_split n k x (by positivity : 0 < (1 - x) / 8) hδ
  rw [abs_of_nonneg hx] at h
  apply h.trans
  apply add_le_add le_rfl
  calc
    2 * (1 + geometricVariance (x + 4 * ((1 - x) / 8)) (n + 1)) /
        ((t * Real.sqrt (geometricVariance x (n + 1))) ^ 2 * (4 : ℝ) ^ k) ≤
        (24 * geometricVariance x (n + 1)) /
          ((t * Real.sqrt (geometricVariance x (n + 1))) ^ 2 * (4 : ℝ) ^ k) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      have hbound := local_boundary_variance_le n hx hx₁ htail
      linarith
    _ = _ := by rw [mul_pow, Real.sq_sqrt hV.le]; field_simp

theorem localRootCount_normalized_probability (n k L : ℕ) (hL : 2 * L ≤ n + 1)
    {x t : ℝ} (hx₀ : 1 / 2 ≤ x) (hx₁ : x < 1) (ht : 0 < t)
    (htail : x ^ (2 * (n + 1)) ≤ 1 / 2) :
    let c : ℝ := 1 / (4 * Real.pi ^ 2)
    sequenceLaw.real {ε | k ≤ localRootCount ε n x ((1 - x) / 8)} ≤
      Real.exp (1 / 2) * (t * Real.sqrt (Real.pi / c) +
        Real.exp (-c * geometricVariance x (n + 1)) +
        2 * Real.exp (-((t * Real.sqrt (geometricVariance x (n + 1))) * (x ^ L)⁻¹) ^ 2 / 2)) +
        24 / (t ^ 2 * (4 : ℝ) ^ k) := by
  apply (localRootCount_normalized_probability_split n k (by linarith) hx₁ ht htail).trans
  exact add_le_add (powerSum_smallBall_normalized n L hL hx₀ hx₁.le ht) le_rfl

end Erdos521
