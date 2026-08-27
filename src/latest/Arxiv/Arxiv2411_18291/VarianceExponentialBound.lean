import Arxiv.Arxiv2411_18291.IndependentConcentration

/-!
# Quadratic exponential control for variance-sensitive concentration

The scalar bound is valid for signed increments. It keeps their linear
term and controls the remainder by the square, which can be compensated
using the conditional second moment of a martingale increment.
-/

namespace Arxiv2411_18291

theorem exp_mul_le_quadratic_of_upper_bound {x b t : ℝ} (hb : 0 ≤ b) (hx : x ≤ b)
    (ht : 0 ≤ t) (htb : t * b < 2) :
    Real.exp (t * x) ≤ 1 + t * x + (t ^ 2 / (2 - t * b)) * x ^ 2 := by
  have hden : 0 < 2 - t * b := by linarith only [htb]
  have htxb : t * x ≤ t * b := mul_le_mul_of_nonneg_left hx ht
  by_cases htx : 0 ≤ t * x
  · have hdenx : 0 < 2 - t * x := by linarith only [htb, htxb]
    calc
      _ ≤ (2 + t * x) / (2 - t * x) :=
        Real.exp_le_two_add_div_two_sub htx (by linarith only [htb, htxb])
      _ = 1 + t * x + (t * x) ^ 2 / (2 - t * x) := by field_simp; ring
      _ ≤ 1 + t * x + (t * x) ^ 2 / (2 - t * b) := by
        have hdiv := div_le_div_of_nonneg_left (sq_nonneg (t * x)) hden
          (show 2 - t * b ≤ 2 - t * x by linarith only [htxb])
        linarith only [hdiv]
      _ = _ := by ring
  · have hneg := exp_neg_le_quadratic (show 0 ≤ -(t * x) by linarith only [htx])
    simp only [neg_neg, neg_sq, sub_neg_eq_add] at hneg
    have htb0 := mul_nonneg ht hb
    calc
      _ ≤ 1 + t * x + (t * x) ^ 2 / 2 := hneg
      _ ≤ 1 + t * x + (t * x) ^ 2 / (2 - t * b) := by
        have hdiv := div_le_div_of_nonneg_left (sq_nonneg (t * x)) hden
          (show 2 - t * b ≤ 2 by linarith only [htb0])
        linarith only [hdiv]
      _ = _ := by ring

theorem variance_chernoff_parameters {a b v : ℝ} (ha : 0 < a) (hb : 0 < b) (hv : 0 ≤ v) :
    let t := a / (v + a * b)
    let g := t ^ 2 / (2 - t * b)
    0 < t ∧ 0 ≤ g ∧ t * b < 2 ∧
      -t * a + g * v = -(a ^ 2 / (2 * v + a * b)) ∧
      -(a ^ 2 / (2 * v + a * b)) ≤ -(a ^ 2 / (2 * (v + a * b))) := by
  have hbase : 0 < v + a * b := by positivity
  have hfinal : 0 < 2 * v + a * b := by positivity
  have htb : a / (v + a * b) * b ≤ 1 := by
    rw [div_mul_eq_mul_div]
    apply (div_le_one hbase).mpr
    linarith only [hv]
  have hden : 0 < 2 - a / (v + a * b) * b := by linarith only [htb]
  refine ⟨by positivity, by positivity, by linarith only [htb], ?_, ?_⟩
  · field_simp [hbase.ne']
    ring_nf
    field_simp [show v * 2 + a * b ≠ 0 by positivity]
    ring
  · apply neg_le_neg
    exact div_le_div_of_nonneg_left (sq_nonneg a) hfinal (by nlinarith only [ha, hb])

end Arxiv2411_18291
