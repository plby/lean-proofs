import Mathlib

namespace Erdos489

/-- A natural-cutoff average has the same limit at real cutoffs rounded up.
For a natural left endpoint n, n < ceil(x) is equivalent to n < x. -/
theorem tendsto_ceil_cutoff (f : ℕ → ℝ) {L : ℝ}
    (h : Filter.Tendsto (fun n : ℕ => f n / (n : ℝ))
      Filter.atTop (nhds L)) :
    Filter.Tendsto (fun x : ℝ => f ⌈x⌉₊ / x) Filter.atTop (nhds L) := by
  have hprod := (h.comp tendsto_nat_ceil_atTop).mul
    (tendsto_nat_ceil_div_atTop (R := ℝ))
  simp only [mul_one] at hprod
  apply hprod.congr'
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with x hx
  have hc : (⌈x⌉₊ : ℝ) ≠ 0 := (hx.trans_le (Nat.le_ceil x)).ne'
  dsimp
  field_simp [hc, hx.ne']

end Erdos489
