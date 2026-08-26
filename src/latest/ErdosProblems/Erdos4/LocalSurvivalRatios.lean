import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Tactic

/-!
# Elementary relative errors for local survival factors

The Bernoulli remainder is quadratic. Dividing by the independent
baseline costs at most two when the local modulus is at least twice the
number of integers. Finite products of these relative errors are then
controlled by the exponential of their sum.
-/

open scoped BigOperators

namespace Erdos4.LocalSurvivalRatios

theorem bernoulli_remainder {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (r : ℕ) :
    0 ≤ (1 - x) ^ r - 1 + (r : ℝ) * x ∧
      (1 - x) ^ r - 1 + (r : ℝ) * x ≤ (r : ℝ) ^ 2 * x ^ 2 := by
  induction r with
  | zero => simp
  | succ r ih =>
    have hrec : (1 - x) ^ (r + 1) - 1 + ((r + 1 : ℕ) : ℝ) * x =
        (1 - x) * ((1 - x) ^ r - 1 + (r : ℝ) * x) + (r : ℝ) * x ^ 2 := by
      rw [pow_succ, Nat.cast_add, Nat.cast_one]
      ring
    rw [hrec]
    constructor
    · exact add_nonneg (mul_nonneg (sub_nonneg.mpr hx1) ih.1)
        (mul_nonneg (Nat.cast_nonneg r) (sq_nonneg x))
    · have hstep : (1 - x) * ((1 - x) ^ r - 1 + (r : ℝ) * x) ≤
          (1 - x) ^ r - 1 + (r : ℝ) * x := by
        nlinarith [mul_nonneg hx0 ih.1]
      calc
        _ ≤ (r : ℝ) ^ 2 * x ^ 2 + (r : ℝ) * x ^ 2 :=
          add_le_add (hstep.trans ih.2) le_rfl
        _ ≤ _ := by
          rw [Nat.cast_add, Nat.cast_one]
          nlinarith [mul_nonneg (Nat.cast_nonneg r) (sq_nonneg x), sq_nonneg x]

theorem local_ratio_error {x v : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (r : ℕ) (hv0 : 0 ≤ v) (hvr : v ≤ r) (hsmall : (r : ℝ) * x ≤ 1 / 2) :
    |(1 - v * x) / (1 - x) ^ r - 1| ≤
      2 * (r : ℝ) ^ 2 * x ^ 2 + 2 * ((r : ℝ) - v) * x := by
  have hrem := bernoulli_remainder hx0 hx1 r
  have hb : (1 / 2 : ℝ) ≤ (1 - x) ^ r := by linarith
  have hbpos : 0 < (1 - x) ^ r := lt_of_lt_of_le (by norm_num) hb
  have hdef : 0 ≤ ((r : ℝ) - v) * x := mul_nonneg (sub_nonneg.mpr hvr) hx0
  have hd : |1 - v * x - (1 - x) ^ r| ≤
      ((r : ℝ) - v) * x + (r : ℝ) ^ 2 * x ^ 2 := by
    apply abs_le.mpr
    constructor <;> nlinarith
  have heq : (1 - v * x) / (1 - x) ^ r - 1 =
      (1 - v * x - (1 - x) ^ r) / (1 - x) ^ r := by field_simp
  rw [heq, abs_div, abs_of_pos hbpos]
  calc
    _ ≤ (((r : ℝ) - v) * x + (r : ℝ) ^ 2 * x ^ 2) / (1 - x) ^ r :=
      div_le_div_of_nonneg_right hd hbpos.le
    _ ≤ (((r : ℝ) - v) * x + (r : ℝ) ^ 2 * x ^ 2) / (1 / 2 : ℝ) :=
      div_le_div_of_nonneg_left (add_nonneg hdef (mul_nonneg (sq_nonneg _) (sq_nonneg _)))
        (by norm_num) hb
    _ = _ := by ring

theorem local_modulus_ratio_error (ell r v : ℕ) (hell : 2 ≤ ell)
    (hvr : v ≤ r) (hsize : 2 * r ≤ ell) :
    |(1 - (v : ℝ) / ell) / (1 - 1 / (ell : ℝ)) ^ r - 1| ≤
      2 * (r : ℝ) ^ 2 / (ell : ℝ) ^ 2 + 2 * ((r : ℝ) - v) / ell := by
  have helpos : (0 : ℝ) < ell := by exact_mod_cast (show 0 < ell by omega)
  have helone : (1 : ℝ) ≤ ell := by exact_mod_cast (show 1 ≤ ell by omega)
  have hx1 : 1 / (ell : ℝ) ≤ 1 := (div_le_one helpos).mpr helone
  have hsmall : (r : ℝ) * (1 / ell) ≤ 1 / 2 := by
    have hh : (2 : ℝ) * r ≤ ell := by exact_mod_cast hsize
    rw [mul_one_div, div_le_iff₀ helpos]
    linarith
  have hh := local_ratio_error (by positivity : (0 : ℝ) ≤ 1 / ell) hx1 r
    (Nat.cast_nonneg v) (by exact_mod_cast hvr) hsmall
  simpa only [mul_one_div, one_div_pow, ← div_eq_mul_inv] using hh

theorem product_ratio_error_le {P : Type*} [Fintype P]
    (a b e : P → ℝ) {E : ℝ} (hlocal : ∀ l, |a l / b l - 1| ≤ e l)
    (hsum : (∑ l, e l) ≤ E) :
    |(∏ l, a l) / (∏ l, b l) - 1| ≤ Real.exp E - 1 := by
  have hh := Finset.norm_prod_one_add_sub_one_le Finset.univ (fun l => a l / b l - 1)
  have hpoint (l : P) : 1 + (a l / b l - 1) = a l / b l := by ring
  simp only [hpoint, Real.norm_eq_abs, Finset.prod_div_distrib] at hh
  exact hh.trans (sub_le_sub_right (Real.exp_le_exp.mpr
    ((Finset.sum_le_sum (fun l _hl => hlocal l)).trans hsum)) 1)

end Erdos4.LocalSurvivalRatios
