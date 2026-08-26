import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# The derivative tower of a logarithmic phase

This file records, uniformly in the natural derivative order, the elementary
calculus facts for the real phase `x ↦ a * log x`.  For positive derivative
order `j`, its `j`-th derivative is

`a * (-1)^(j - 1) * (j - 1)! * x^(-j)`.

The final lemmas package the exact absolute value and its upper and lower
bounds on a positive dyadic interval.  These are the hypotheses needed by
finite derivative tests for exponential sums.
-/

open Set

namespace Erdos67b.LogDerivativeTower

noncomputable section

/-- The natural-order derivative tower of `x ↦ a * log x`.

The successor presentation avoids subtraction in the defining formula:
order `j + 1` has coefficient `(-1)^j j!` and power `-(j+1)`. -/
def logDerivative (a : ℝ) : ℕ → ℝ → ℝ
  | 0 => fun x => a * Real.log x
  | j + 1 => fun x =>
      a * (-1 : ℝ) ^ j * (j.factorial : ℝ) * x ^ (-(j + 1 : ℤ))

/-- A short name for the derivative tower, convenient in derivative-test
statements. -/
abbrev F := logDerivative

@[simp]
theorem logDerivative_zero (a x : ℝ) :
    logDerivative a 0 x = a * Real.log x := rfl

@[simp]
theorem logDerivative_succ (a x : ℝ) (j : ℕ) :
    logDerivative a (j + 1) x =
      a * (-1 : ℝ) ^ j * (j.factorial : ℝ) * x ^ (-(j + 1 : ℤ)) := rfl

/-- The conventional positive-order formula, written with `j - 1`. -/
theorem logDerivative_of_pos (a x : ℝ) {j : ℕ} (hj : 0 < j) :
    logDerivative a j x =
      a * (-1 : ℝ) ^ (j - 1) * ((j - 1).factorial : ℝ) *
        x ^ (-(j : ℤ)) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hj)
  simp only [logDerivative_succ, Nat.succ_sub_one]
  congr 2

@[simp]
theorem F_zero (a x : ℝ) : F a 0 x = a * Real.log x := rfl

@[simp]
theorem F_succ (a x : ℝ) (j : ℕ) :
    F a (j + 1) x =
      a * (-1 : ℝ) ^ j * (j.factorial : ℝ) * x ^ (-(j + 1 : ℤ)) := rfl

theorem F_of_pos (a x : ℝ) {j : ℕ} (hj : 0 < j) :
    F a j x =
      a * (-1 : ℝ) ^ (j - 1) * ((j - 1).factorial : ℝ) *
        x ^ (-(j : ℤ)) :=
  logDerivative_of_pos a x hj

/-- Each entry in the tower differentiates to the next entry on the positive
half-line. -/
theorem hasDerivAt_logDerivative (a : ℝ) (j : ℕ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (logDerivative a j) (logDerivative a (j + 1) x) x := by
  cases j with
  | zero =>
      simpa [logDerivative] using (Real.hasDerivAt_log hx.ne').const_mul a
  | succ j =>
      have hp := hasDerivAt_zpow (-(j + 1 : ℤ)) x (Or.inl hx.ne')
      have hd := hp.const_mul
        (a * (-1 : ℝ) ^ j * (j.factorial : ℝ))
      change HasDerivAt
        (fun y : ℝ =>
          a * (-1 : ℝ) ^ j * (j.factorial : ℝ) * y ^ (-(j + 1 : ℤ)))
        (logDerivative a (j.succ + 1) x) x
      refine hd.congr_deriv ?_
      simp only [logDerivative_succ]
      rw [Nat.factorial_succ]
      push_cast
      ring_nf

/-- Short-name version of `hasDerivAt_logDerivative`. -/
theorem hasDerivAt_F (a : ℝ) (j : ℕ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (F a j) (F a (j + 1) x) x :=
  hasDerivAt_logDerivative a j hx

/-- Removing the alternating sign leaves a non-alternating expression. -/
theorem sign_normalized_logDerivative (a x : ℝ) (j : ℕ) :
    (-1 : ℝ) ^ j * logDerivative a (j + 1) x =
      a * (j.factorial : ℝ) * x ^ (-(j + 1 : ℤ)) := by
  rw [logDerivative_succ]
  have hs : (-1 : ℝ) ^ j * (-1 : ℝ) ^ j = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  calc
    (-1 : ℝ) ^ j *
        (a * (-1 : ℝ) ^ j * (j.factorial : ℝ) * x ^ (-(j + 1 : ℤ))) =
        a * ((-1 : ℝ) ^ j * (-1 : ℝ) ^ j) *
          (j.factorial : ℝ) * x ^ (-(j + 1 : ℤ)) := by ring
    _ = a * (j.factorial : ℝ) * x ^ (-(j + 1 : ℤ)) := by rw [hs]; ring

/-- In particular, after correcting by the alternating sign, every positive
order derivative is nonnegative when `a` is nonnegative. -/
theorem sign_normalized_logDerivative_nonneg {a x : ℝ} (ha : 0 ≤ a)
    (hx : 0 < x) (j : ℕ) :
    0 ≤ (-1 : ℝ) ^ j * logDerivative a (j + 1) x := by
  rw [sign_normalized_logDerivative]
  positivity

/-- Strict sign alternation when the logarithmic coefficient is positive. -/
theorem sign_normalized_logDerivative_pos {a x : ℝ} (ha : 0 < a)
    (hx : 0 < x) (j : ℕ) :
    0 < (-1 : ℝ) ^ j * logDerivative a (j + 1) x := by
  rw [sign_normalized_logDerivative]
  positivity

/-- Sign-normalized formula in conventional order notation `j ≥ 1`. -/
theorem sign_normalized_F_of_pos (a x : ℝ) {j : ℕ} (hj : 0 < j) :
    (-1 : ℝ) ^ (j - 1) * F a j x =
      a * ((j - 1).factorial : ℝ) * x ^ (-(j : ℤ)) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hj)
  convert sign_normalized_logDerivative a x j using 1 <;> norm_num

/-- Exact magnitude of the positive-order derivative on the positive axis. -/
theorem abs_logDerivative_succ {a x : ℝ} (hx : 0 < x) (j : ℕ) :
    |logDerivative a (j + 1) x| =
      |a| * (j.factorial : ℝ) * x ^ (-(j + 1 : ℤ)) := by
  rw [logDerivative_succ, abs_mul, abs_mul, abs_mul, abs_zpow]
  simp [abs_pow, abs_of_pos hx]

/-- Exact magnitude in conventional order notation `j ≥ 1`. -/
theorem abs_F_of_pos {a x : ℝ} (hx : 0 < x) {j : ℕ} (hj : 0 < j) :
    |F a j x| =
      |a| * ((j - 1).factorial : ℝ) * x ^ (-(j : ℤ)) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hj)
  convert abs_logDerivative_succ hx j using 1
  norm_num

/-- Lower dyadic magnitude bound at arbitrary natural derivative order. -/
theorem dyadic_lower_abs_logDerivative_succ {a X x : ℝ} (hX : 0 < X)
    (hx : x ∈ Icc X (2 * X)) (j : ℕ) :
    |a| * (j.factorial : ℝ) * (2 * X) ^ (-(j + 1 : ℤ)) ≤
      |logDerivative a (j + 1) x| := by
  rw [abs_logDerivative_succ (hX.trans_le hx.1)]
  have hpow : x ^ (j + 1) ≤ (2 * X) ^ (j + 1) := by
    exact pow_le_pow_left₀ (hX.le.trans hx.1) hx.2 _
  have hinv : ((2 * X) ^ (j + 1))⁻¹ ≤ (x ^ (j + 1))⁻¹ := by
    exact inv_anti₀ (pow_pos (hX.trans_le hx.1) _) hpow
  simp only [zpow_neg]
  exact mul_le_mul_of_nonneg_left hinv (mul_nonneg (abs_nonneg a) (Nat.cast_nonneg _))

/-- Upper dyadic magnitude bound at arbitrary natural derivative order. -/
theorem dyadic_upper_abs_logDerivative_succ {a X x : ℝ} (hX : 0 < X)
    (hx : x ∈ Icc X (2 * X)) (j : ℕ) :
    |logDerivative a (j + 1) x| ≤
      |a| * (j.factorial : ℝ) * X ^ (-(j + 1 : ℤ)) := by
  rw [abs_logDerivative_succ (hX.trans_le hx.1)]
  have hpow : X ^ (j + 1) ≤ x ^ (j + 1) := by
    exact pow_le_pow_left₀ hX.le hx.1 _
  have hinv : (x ^ (j + 1))⁻¹ ≤ (X ^ (j + 1))⁻¹ := by
    exact inv_anti₀ (pow_pos hX _) hpow
  simp only [zpow_neg]
  exact mul_le_mul_of_nonneg_left hinv (mul_nonneg (abs_nonneg a) (Nat.cast_nonneg _))

/-- The two-sided dyadic derivative estimate in one statement. -/
theorem dyadic_abs_logDerivative_succ {a X x : ℝ} (hX : 0 < X)
    (hx : x ∈ Icc X (2 * X)) (j : ℕ) :
    |a| * (j.factorial : ℝ) * (2 * X) ^ (-(j + 1 : ℤ)) ≤
        |logDerivative a (j + 1) x| ∧
      |logDerivative a (j + 1) x| ≤
        |a| * (j.factorial : ℝ) * X ^ (-(j + 1 : ℤ)) :=
  ⟨dyadic_lower_abs_logDerivative_succ hX hx j,
    dyadic_upper_abs_logDerivative_succ hX hx j⟩

/-- The two-sided dyadic estimate in conventional order notation `j ≥ 1`. -/
theorem dyadic_abs_F_of_pos {a X x : ℝ} (hX : 0 < X)
    (hx : x ∈ Icc X (2 * X)) {j : ℕ} (hj : 0 < j) :
    |a| * ((j - 1).factorial : ℝ) * (2 * X) ^ (-(j : ℤ)) ≤
        |F a j x| ∧
      |F a j x| ≤
        |a| * ((j - 1).factorial : ℝ) * X ^ (-(j : ℤ)) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hj)
  have h := dyadic_abs_logDerivative_succ (a := a) hX hx j
  constructor
  · convert h.1 using 1
    norm_num
  · convert h.2 using 1
    norm_num

end

end Erdos67b.LogDerivativeTower
