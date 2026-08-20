import ErdosProblems.Erdos746.BinomialBounds
import ErdosProblems.Erdos746.Asymptotics
import Mathlib.Data.Nat.Choose.Bounds

/-! # The medium-size expansion range for Erdős 746 -/

open Filter
open scoped Topology

namespace Erdos746

noncomputable section

/-- The edge probability in the medium-range calculation. -/
def mediumP (c : ℝ) (n : ℕ) : ℝ :=
  c * Real.log (n : ℝ) / (n : ℝ)

/-- The probability that one vertex outside an `s`-set meets it. -/
def mediumQ (c : ℝ) (n s : ℕ) : ℝ :=
  1 - (1 - mediumP c n) ^ s

/-- The expected number of outside neighbours of a fixed `s`-set. -/
def mediumMu (c : ℝ) (n s : ℕ) : ℝ :=
  ((n - s : ℕ) : ℝ) * mediumQ c n s

/-- The lower-tail contribution after choosing the fixed `s`-set. -/
def mediumUnionTerm (c : ℝ) (n s : ℕ) : ℝ :=
  (n.choose s : ℝ) *
    binomialLowerTail (n - s) (2 * s + 1) (mediumQ c n s)

/-- On `[0,1]`, `1-exp(-x)` is at least `x/2`. -/
lemma half_le_one_sub_exp_neg {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    x / 2 ≤ 1 - Real.exp (-x) := by
  have hden : 0 < 1 + x := by linarith
  have hexp : 1 + x ≤ Real.exp x := by
    simpa [add_comm] using Real.add_one_le_exp x
  have hinv : Real.exp (-x) ≤ 1 / (1 + x) := by
    rw [Real.exp_neg, inv_eq_one_div]
    exact one_div_le_one_div_of_le hden hexp
  have hfrac : 1 / (1 + x) ≤ 1 - x / 2 := by
    rw [div_le_iff₀ hden]
    nlinarith [mul_nonneg hx0 (sub_nonneg.mpr hx1)]
  linarith

/-- If `0 ≤ p ≤ 1` and `ps ≤ 1`, a bundle of `s` independent edges is
occupied with probability at least `ps/2`. -/
lemma half_mul_le_one_sub_one_sub_pow {p : ℝ} (s : ℕ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hps : p * (s : ℝ) ≤ 1) :
    p * (s : ℝ) / 2 ≤ 1 - (1 - p) ^ s := by
  have hx0 : 0 ≤ p * (s : ℝ) := mul_nonneg hp0 (Nat.cast_nonneg s)
  have hbase0 : 0 ≤ 1 - p := sub_nonneg.mpr hp1
  have hbase : 1 - p ≤ Real.exp (-p) := by
    have h := Real.add_one_le_exp (-p)
    linarith
  have hpow : (1 - p) ^ s ≤ Real.exp (-(p * (s : ℝ))) := by
    calc
      (1 - p) ^ s ≤ Real.exp (-p) ^ s :=
        pow_le_pow_left₀ hbase0 hbase s
      _ = Real.exp (-(p * (s : ℝ))) := by
        rw [← Real.exp_nat_mul]
        congr 1
        push_cast
        ring
  have hhalf := half_le_one_sub_exp_neg hx0 hps
  linarith

/-- The elementary union bound `1-(1-p)^s ≤ ps`. -/
lemma one_sub_one_sub_pow_le_mul {p : ℝ} (s : ℕ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    1 - (1 - p) ^ s ≤ p * (s : ℝ) := by
  induction s with
  | zero => simp
  | succ s ih =>
      have hb0 : 0 ≤ 1 - p := sub_nonneg.mpr hp1
      have hb1 : 1 - p ≤ 1 := by linarith
      have hpow0 : 0 ≤ (1 - p) ^ s := pow_nonneg hb0 s
      have hpow1 : (1 - p) ^ s ≤ 1 := pow_le_one₀ hb0 hb1
      rw [pow_succ]
      push_cast
      nlinarith

/-- The logarithmic factor occurring in Range II is eventually absorbed
by `n^(c/8)`. -/
lemma eventually_medium_polynomial_absorbed {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop,
      4 * Real.log (n : ℝ) ^ 2 *
          (Real.exp 1 * c * Real.log (n : ℝ) / 2) ^ 2 ≤
        Real.exp ((c / 8) * Real.log (n : ℝ)) := by
  let A : ℝ := Real.exp 1 ^ 2 * c ^ 2
  have hA : 0 < A := by positivity
  have hdom := eventually_log_rpow_le_mul_rpow (4 : ℝ)
    (a := c / 8) (η := 1 / A) (by positivity) (by positivity)
  filter_upwards [hdom, eventually_gt_atTop (0 : ℕ)] with n hn hn0
  have hmul := mul_le_mul_of_nonneg_left hn hA.le
  have hrpow : (n : ℝ) ^ (c / 8) =
      Real.exp ((c / 8) * Real.log (n : ℝ)) := by
    rw [Real.rpow_def_of_pos (Nat.cast_pos.mpr hn0)]
    congr 1
    ring
  rw [one_div, ← mul_assoc, mul_inv_cancel₀ hA.ne', one_mul, hrpow] at hmul
  rw [show Real.log (n : ℝ) ^ (4 : ℝ) =
      Real.log (n : ℝ) ^ 4 by simp] at hmul
  calc
    4 * Real.log (n : ℝ) ^ 2 *
        (Real.exp 1 * c * Real.log (n : ℝ) / 2) ^ 2 =
      A * Real.log (n : ℝ) ^ 4 := by
        dsimp [A]
        ring
    _ ≤ Real.exp ((c / 8) * Real.log (n : ℝ)) := hmul

/-- The explicit Range-II error tends to zero. -/
lemma tendsto_medium_range_error_zero {c : ℝ} (hc : 0 < c) :
    Tendsto (fun n : ℕ ↦
      (n : ℝ) * Real.exp (-(c / 8) * (n : ℝ) / Real.log (n : ℝ)))
      atTop (nhds 0) :=
  tendsto_nat_mul_exp_neg_nat_div_log (by positivity)

end

end Erdos746
