/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Small-ball estimates expressed in units of the polynomial standard deviation.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.SmallBall

namespace Erdos521

theorem normalized_smallBall_sqrt {c V t : ℝ} (hc : 0 < c) (hV : 0 < V) (ht : 0 < t) :
    Real.sqrt (Real.pi / (c * V / (t * Real.sqrt V) ^ 2)) = t * Real.sqrt (Real.pi / c) := by
  have hid : Real.pi / (c * V / (t * Real.sqrt V) ^ 2) = (Real.pi / c) * t ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hV.le]
    field_simp
  rw [hid, Real.sqrt_mul (div_nonneg Real.pi_pos.le hc.le), Real.sqrt_sq_eq_abs, abs_of_pos ht,
    mul_comm]

theorem powerSum_smallBall_normalized (n L : ℕ) (hL : 2 * L ≤ n + 1)
    {x t : ℝ} (hx₀ : 1 / 2 ≤ x) (hx₁ : x ≤ 1) (ht : 0 < t) :
    let c : ℝ := 1 / (4 * Real.pi ^ 2)
    sequenceLaw.real {ε | |powerSum ε (n + 1) x| ≤ t * Real.sqrt (geometricVariance x (n + 1))} ≤
      Real.exp (1 / 2) * (t * Real.sqrt (Real.pi / c) +
        Real.exp (-c * geometricVariance x (n + 1)) +
        2 * Real.exp (-((t * Real.sqrt (geometricVariance x (n + 1))) * (x ^ L)⁻¹) ^ 2 / 2)) := by
  have hV := geometricVariance_succ_pos x n
  have h := powerSum_smallBall n L hL hx₀ hx₁ (mul_pos ht (Real.sqrt_pos.mpr hV))
  dsimp only at h ⊢
  rwa [normalized_smallBall_sqrt (by positivity : 0 < 1 / (4 * Real.pi ^ 2)) hV ht] at h

end Erdos521
