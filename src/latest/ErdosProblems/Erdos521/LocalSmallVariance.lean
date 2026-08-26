/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
The lacunary estimate handles local root-count tails when the variance is small.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.LocalTailParameters

namespace Erdos521

theorem local_small_variance_smallBall (n j : ℕ) (hj : 8 ≤ j) {x : ℝ}
    (hx : 9 / 10 ≤ x) (hx₁ : x < 1) (hgap : 32 * (j : ℝ) ≤ n * (1 - x))
    (hV : geometricVariance x (n + 1) ≤ j) :
    sequenceLaw.real {ε | |powerSum ε (n + 1) x| ≤
      (1 / 2 : ℝ) ^ j * Real.sqrt (geometricVariance x (n + 1))} ≤ (1 / 4 : ℝ) ^ (j / 12) := by
  obtain ⟨L, hL, hstride, hq, hLgap⟩ := exists_lacunary_stride (by linarith : 0 < x) hx₁
  have hdegree : L * (2 * (j / 12)) ≤ n := by
    have hjdiv : (j / 12 : ℕ) * (12 : ℝ) ≤ j := by
      exact_mod_cast (Nat.div_mul_le_self j 12)
    have hm := mul_le_mul_of_nonneg_right hLgap (by positivity : 0 ≤ (2 : ℝ) * (j / 12 : ℕ))
    have hcast : ((L * (2 * (j / 12)) : ℕ) : ℝ) * (1 - x) ≤ n * (1 - x) := by
      push_cast
      nlinarith [(Nat.cast_nonneg (j / 12) : (0 : ℝ) ≤ (j / 12 : ℕ))]
    exact_mod_cast (mul_le_mul_iff_left₀ (sub_pos.mpr hx₁)).mp hcast
  have hsmall := geometric_subsequence_smallBall_dyadic n L (j / 12) hL hdegree
    (z := 0) (pow_nonneg (by linarith : 0 ≤ x) _) hq (lacunary_stride_square_lower hx L hstride)
  apply le_trans _ (by simpa only [sub_zero] using hsmall)
  exact MeasureTheory.measureReal_mono (fun ε hε ↦
    hε.trans (dyadic_normalized_radius_le_lacunary j hj (geometricVariance_nonneg _ _) hV))

end Erdos521
