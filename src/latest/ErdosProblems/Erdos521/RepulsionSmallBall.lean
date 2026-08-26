/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Uniform small-ball control on the bulk interval needed for root repulsion.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.LacunaryScale

namespace Erdos521

theorem powerSum_smallBall_repulsion_scale (n j : ℕ) (hn : 1 < n) {C x z : ℝ}
    (hC : 0 < C) (hj : 6 * (j : ℝ) ≤ C * Real.log n)
    (hx₀ : 9 / 10 ≤ x) (hx₁ : x ≤ endpointCenter C n) :
    sequenceLaw.real {ε | |powerSum ε (n + 1) x - z| ≤ (1 / 4) * (1 / 8 : ℝ) ^ j} ≤
      (1 / 4 : ℝ) ^ j := by
  have hn₀ : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn)
  have hxpos : 0 < x := by linarith
  have hxlt : x < 1 := by
    apply hx₁.trans_lt
    exact sub_lt_self _ (div_pos (mul_pos hC hlog) hn₀)
  obtain ⟨L, hL, hstride, hupper, hlength⟩ := exists_lacunary_stride hxpos hxlt
  have hL₀ : (0 : ℝ) ≤ L := Nat.cast_nonneg L
  have hdist : C * Real.log n / n ≤ 1 - x := by
    change x ≤ 1 - C * Real.log n / n at hx₁
    linarith
  have hLdist := (mul_le_mul_of_nonneg_left hdist hL₀).trans hlength
  have hLlog : (L : ℝ) * (C * Real.log n) ≤ 3 * n := by
    apply (div_le_iff₀ hn₀).mp
    simpa only [mul_div_assoc] using hLdist
  have hLj := mul_le_mul_of_nonneg_left hj hL₀
  have hdegree : L * (2 * j) ≤ n := by
    have hreal : (L : ℝ) * (2 * (j : ℝ)) ≤ n := by nlinarith
    exact_mod_cast hreal
  exact geometric_subsequence_smallBall_dyadic n L j hL hdegree
    (pow_pos hxpos L).le hupper (lacunary_stride_square_lower hx₀ L hstride)

end Erdos521
