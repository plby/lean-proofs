import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Scalar exponential bounds for adaptive concentration

The rational upper bound for the exponential yields a linear bound on
`exp(t*x)` for `0 ≤ x ≤ C`. This avoids assuming the false signed version of
the paper's concentration lemma.
-/

namespace Arxiv2411_18291

theorem exp_mul_le_linear {x C t : ℝ} (hx : 0 ≤ x) (hxC : x ≤ C)
    (ht : 0 ≤ t) (htC : t * C < 2) :
    Real.exp (t * x) ≤ 1 + (2 * t / (2 - t * C)) * x := by
  have htx : 0 ≤ t * x := mul_nonneg ht hx
  have hle : t * x ≤ t * C := mul_le_mul_of_nonneg_left hxC ht
  have hd : 0 < 2 - t * C := by linarith
  have hdx : 0 < 2 - t * x := by linarith
  calc
    Real.exp (t * x) ≤ (2 + t * x) / (2 - t * x) :=
      Real.exp_le_two_add_div_two_sub htx (by linarith)
    _ = 1 + 2 * (t * x) / (2 - t * x) := by field_simp; ring
    _ ≤ 1 + 2 * (t * x) / (2 - t * C) := by
      exact add_le_add_right (div_le_div_of_nonneg_left (by positivity) hd (by linarith)) 1
    _ = _ := by ring

/-- The parameters used below give a bound stronger than the printed one. -/
theorem adaptive_chernoff_parameters {C c : ℝ} (hC : 0 < C) (hc : 0 < c) :
    let t := c / ((1 + c) * C)
    let g := 2 * t / (2 - t * C)
    0 < t ∧ 0 ≤ g ∧ t * C < 2 ∧
      -t * (1 + c) + g = -(c ^ 2 / ((2 + c) * C)) := by
  dsimp only
  have hc1 : 0 < 1 + c := by positivity
  have hc2 : 0 < 2 + c := by positivity
  have ht : 0 < c / ((1 + c) * C) := by positivity
  have htc : c / ((1 + c) * C) * C < 1 := by
    field_simp
    linarith
  have hd : 0 < 2 - c / ((1 + c) * C) * C := by linarith
  refine ⟨ht, by positivity, by linarith, ?_⟩
  field_simp [hc1.ne', hC.ne']
  ring_nf
  field_simp [hc2.ne', show c + 2 ≠ 0 by linarith]
  ring

end Arxiv2411_18291
