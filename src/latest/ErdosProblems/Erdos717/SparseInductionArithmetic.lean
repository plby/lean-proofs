/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Analytic estimates for the low-core recursion and its boundary cases. -/

import ErdosProblems.Erdos717.SparseHighStep

open Function Set

namespace Erdos717

theorem sparsePotential_lt_one_of_edge_square_small
    (n m a : ℕ) (hn : 0 < n) (hm : 0 < m) (ha : 0 < a)
    (hlogn : 100 ≤ Real.log n)
    (hA : (1 / 64 : ℝ) ≤
      ((m : ℝ) / (n : ℝ) ^ 2) * a)
    (hsmall : (((m : ℝ) / (n : ℝ) ^ 2) ^ 2) * n < 5000000000) :
    sparsePotential n m a < 1 := by
  let d : ℝ := (m : ℝ) / (n : ℝ) ^ 2
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hd : 0 < d := by positivity
  have hApos : 0 < d * (a : ℝ) := lt_of_lt_of_le (by norm_num) hA
  have hlogC : Real.log (5000000000 : ℝ) < 100 :=
    log_lt_hundred_of_le_ten_pow_ten (by norm_num) (by norm_num)
  have hlogSmall := Real.strictMonoOn_log
    (by positivity : 0 < d ^ 2 * (n : ℝ)) (by norm_num : (0 : ℝ) < 5000000000)
    (by simpa only [d] using hsmall)
  rw [Real.log_mul (pow_ne_zero 2 hd.ne') hnR.ne', Real.log_pow] at hlogSmall
  norm_num at hlogSmall
  have hlogInv : Real.log (1 / d) = -Real.log d := by
    rw [one_div, Real.log_inv]
  have hfrac : Real.log n / (1000000000000 * (d * a)) ≤
      64 * Real.log n / 1000000000000 := by
    rw [div_le_iff₀ (by positivity : 0 < 1000000000000 * (d * a))]
    nlinarith
  have hexponent : Real.log n / 2 +
      Real.log n / (1000000000000 * (d * a)) -
      4 * Real.log (1 / d) - 1000 < 0 := by
    rw [hlogInv]
    nlinarith only [hlogSmall, hlogC, hfrac, hlogn]
  rw [sparsePotential_eq_exp_log n m a hn hm ha]
  rw [Real.exp_lt_one_iff]
  simpa only [d, mul_assoc] using hexponent

/-- Below the fixed large-order threshold, the leading `exp (-1000)`
factor makes the sparse potential smaller than one.  This is the base case
needed when the sparse induction passes to an induced core. -/
theorem sparsePotential_lt_one_of_order_small
    (n m a : ℕ) (hn : 0 < n) (hm : 0 < m) (ha : 0 < a)
    (hA : (1 / 64 : ℝ) ≤
      ((m : ℝ) / (n : ℝ) ^ 2) * a)
    (hdle : (m : ℝ) / (n : ℝ) ^ 2 ≤ 1)
    (hnsmall : n < 10 ^ 100) :
    sparsePotential n m a < 1 := by
  let d : ℝ := (m : ℝ) / (n : ℝ) ^ 2
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hd : 0 < d := by positivity
  have hA' : (1 / 64 : ℝ) ≤ d * a := by simpa only [d] using hA
  have hApos : 0 < d * (a : ℝ) := lt_of_lt_of_le (by norm_num) hA'
  have hlogn0 : 0 ≤ Real.log (n : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn.ne')
  have hnsmallR : (n : ℝ) < 10 ^ (100 : ℕ) := by exact_mod_cast hnsmall
  have hlogn : Real.log (n : ℝ) < Real.log (10 ^ (100 : ℕ) : ℝ) :=
    Real.strictMonoOn_log hnR (by norm_num) hnsmallR
  rw [Real.log_pow] at hlogn
  norm_num at hlogn
  have hlogTen : Real.log (10 : ℝ) < 9 := by
    convert Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 10) using 1 <;>
      norm_num
  have hlognUpper : Real.log (n : ℝ) < 900 := by nlinarith
  have hy : 0 ≤ Real.log (1 / d) := by
    exact Real.log_nonneg ((one_le_div₀ hd).2 (by simpa only [d] using hdle))
  have hfrac : Real.log n / (1000000000000 * (d * a)) ≤
      64 * Real.log n / 1000000000000 := by
    rw [div_le_iff₀ (by positivity : 0 < 1000000000000 * (d * a))]
    nlinarith
  have hexponent : Real.log n / 2 +
      Real.log n / (1000000000000 * (d * a)) -
      4 * Real.log (1 / d) - 1000 < 0 := by
    nlinarith
  rw [sparsePotential_eq_exp_log n m a hn hm ha]
  rw [Real.exp_lt_one_iff]
  simpa only [d, mul_assoc] using hexponent

/-- In the `a > n/16` boundary, the sparse potential is already below the
topological-density scale. -/
theorem five_mul_card_mul_sparsePotential_sq_lt_edges
    (n m a : ℕ) (hn : 0 < n) (hm : 0 < m) (ha : 0 < a)
    (hlogn : 100 ≤ Real.log n)
    (hdle : (m : ℝ) / (n : ℝ) ^ 2 ≤ 1)
    (halarge : (n : ℝ) < 16 * a)
    (hedgeLarge : (1 : ℝ) ≤
      (((m : ℝ) / (n : ℝ) ^ 2) ^ 2) * n) :
    5 * (n : ℝ) * (sparsePotential n m a) ^ 2 < m := by
  let d : ℝ := (m : ℝ) / (n : ℝ) ^ 2
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hd : 0 < d := by positivity
  have hdle' : d ≤ 1 := by simpa only [d] using hdle
  have hy : 0 ≤ Real.log (1 / d) := by
    exact Real.log_nonneg ((one_le_div₀ hd).2 hdle')
  have hroot : Real.sqrt n ≤ d * n := by
    have hsqrt0 : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
    have hdn0 : 0 ≤ d * (n : ℝ) := by positivity
    apply (sq_le_sq₀ hsqrt0 hdn0).mp
    rw [Real.sq_sqrt hnR.le]
    nlinarith [by simpa only [d] using hedgeLarge]
  have hlogSqrt : Real.log n ≤ 2 * Real.sqrt n := by
    have h := Real.log_natCast_le_rpow_div n (by norm_num : (0 : ℝ) < 1 / 2)
    simpa [Real.sqrt_eq_rpow, mul_comm] using h
  have hA : d * (a : ℝ) > d * n / 16 := by
    nlinarith [mul_lt_mul_of_pos_left halarge hd]
  have hextra : Real.log n / (1000000000000 * (d * a)) < 1 := by
    rw [div_lt_iff₀ (by positivity : 0 < 1000000000000 * (d * a))]
    have hdn : Real.sqrt n ≤ d * n := hroot
    nlinarith
  have hpotPos : 0 < sparsePotential n m a := by
    simp only [sparsePotential]
    positivity
  have hleftPos : 0 < 5 * (n : ℝ) * (sparsePotential n m a) ^ 2 := by positivity
  have hlogInv : Real.log (1 / d) = -Real.log d := by
    rw [one_div, Real.log_inv]
  have hlogFive : Real.log (5 : ℝ) < 4 := by
    have := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 5)
      (by norm_num : (5 : ℝ) ≠ 1)
    nlinarith
  have hlogPotential : Real.log (sparsePotential n m a) =
      Real.log n / 2 + Real.log n / (1000000000000 * (d * a)) -
        4 * Real.log (1 / d) - 1000 := by
    rw [sparsePotential_eq_exp_log n m a hn hm ha, Real.log_exp]
    simp only [d, mul_assoc]
  have hmEq : (m : ℝ) = d * n ^ 2 := by
    dsimp only [d]
    field_simp
  apply (Real.log_lt_log_iff hleftPos hmR).mp
  rw [Real.log_mul (mul_ne_zero (by norm_num : (5 : ℝ) ≠ 0) hnR.ne')
      (pow_ne_zero 2 hpotPos.ne'),
    Real.log_mul (by norm_num : (5 : ℝ) ≠ 0) hnR.ne',
    Real.log_pow, hlogPotential, hmEq,
    Real.log_mul hd.ne' (pow_ne_zero 2 hnR.ne'), Real.log_pow, hlogInv]
  nlinarith

theorem sparse_low_log_comparison
    {x x' y A t : ℝ}
    (hx : 100 ≤ x) (hy : 20 ≤ y) (hA : 0 < A)
    (hAy : A * y ≤ x / 10000000000000000)
    (ht : 10 ≤ t) (hxx' : x - 7 ≤ x') :
    x / 2 + x / (1000000000000 * A) - 4 * y ≤
      x' / 2 + t * x' / (1000000000000 * A) -
        4 * (y + Real.log t) := by
  have hx0 : 0 ≤ x := by linarith
  have hy0 : 0 ≤ y := by linarith
  have ht0 : 0 < t := by linarith
  have hlogt : Real.log t ≤ t :=
    (Real.log_le_sub_one_of_pos ht0).trans (by linarith)
  have htx : (4 / 5 : ℝ) * t * x ≤ t * x' - x := by
    have hmul := mul_le_mul_of_nonneg_left hxx' ht0.le
    nlinarith
  have hxy : 100 * y ≤ x / (1000000000000 * A) := by
    rw [le_div_iff₀ (by positivity : 0 < 1000000000000 * A)]
    nlinarith
  have hgain : 80 * t * y ≤
      (t * x' - x) / (1000000000000 * A) := by
    calc
      80 * t * y = ((4 / 5 : ℝ) * t) * (100 * y) := by ring
      _ ≤ ((4 / 5 : ℝ) * t) *
          (x / (1000000000000 * A)) :=
            mul_le_mul_of_nonneg_left hxy (mul_nonneg (by norm_num) ht0.le)
      _ = ((4 / 5 : ℝ) * t * x) / (1000000000000 * A) := by ring
      _ ≤ (t * x' - x) / (1000000000000 * A) := by
        exact div_le_div_of_nonneg_right htx (by positivity)
  have hloss : 4 * Real.log t + (x - x') / 2 ≤ 80 * t * y := by
    have hlog4 : 4 * Real.log t ≤ 4 * t :=
      mul_le_mul_of_nonneg_left hlogt (by norm_num)
    nlinarith
  have hdiff : t * x' / (1000000000000 * A) -
      x / (1000000000000 * A) =
      (t * x' - x) / (1000000000000 * A) := by ring
  rw [← sub_nonneg] at hgain
  rw [← hdiff] at hgain
  nlinarith

/-- The logarithmic sparse hypothesis survives a core whose density drops
by a factor at least ten while its order drops by at most eight. -/
theorem sparse_log_condition_of_density_drop
    {x x' y A q : ℝ}
    (hx : 100 ≤ x) (hy : 20 ≤ y)
    (hqpos : 0 < q) (hq : q ≤ 1 / 10)
    (hxx' : x - 7 ≤ x')
    (hAy : A * y ≤ x / 10000000000000000) :
    (q * A) * (y + Real.log (1 / q)) ≤ x' / 10000000000000000 := by
  have hq1 : q ≤ 1 := hq.trans (by norm_num)
  have hlog : Real.log (1 / q) ≤ 1 / q :=
    (Real.log_le_sub_one_of_pos (one_div_pos.mpr hqpos)).trans (by linarith)
  have hqlog : q * Real.log (1 / q) ≤ 1 := by
    have := mul_le_mul_of_nonneg_left hlog hqpos.le
    calc
      q * Real.log (1 / q) ≤ q * (1 / q) := this
      _ = 1 := by field_simp
  have hqy : q * y ≤ y / 10 := by
    nlinarith
  have hone : (1 : ℝ) ≤ y / 20 := by nlinarith
  have hsum : q * (y + Real.log (1 / q)) ≤ 3 * y / 20 := by
    nlinarith
  have hx' : 9 * x / 10 ≤ x' := by nlinarith
  have hx'pos : 0 < x' := by nlinarith
  by_cases hA0 : A ≤ 0
  · have : q * A ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hqpos.le hA0
    have hlogNonneg : 0 ≤ y + Real.log (1 / q) := by
      have : 1 ≤ 1 / q := (one_le_div₀ hqpos).2 hq1
      nlinarith [Real.log_nonneg this]
    exact (mul_nonpos_of_nonpos_of_nonneg this hlogNonneg).trans
      (div_nonneg hx'pos.le (by norm_num))
  · have hApos : 0 < A := lt_of_not_ge hA0
    have hscaled := mul_le_mul_of_nonneg_left hsum hApos.le
    have hAy' := hAy
    nlinarith

end Erdos717
