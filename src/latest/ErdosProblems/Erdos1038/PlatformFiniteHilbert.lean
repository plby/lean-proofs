import ErdosProblems.Erdos1038.PlatformSecondKindChebyshev

/-!
# The regularized finite Hilbert transform of cosine modes

For `n ≥ 1`, the apparent singularity in

`(cos(nφ) - cos(nθ)) / (cos θ - cos φ)`

is removable.  We construct its polynomial extension by a two-step
Chebyshev recurrence, prove the exact divided-difference identity, and
compute its normalized half-circle integral.  This is the finite-mode
principal-value calculation used by the endpoint-corrected adjoint.
-/

set_option warningAsError false

open MeasureTheory Polynomial

namespace Erdos1038

noncomputable section

open Polynomial.Chebyshev

/-- Polynomial extension of the negative cosine divided difference, before
the final sign from the denominator `cos θ - cos φ` is applied. -/
def finiteHilbertKernelPolynomial : ℕ → ℝ → Polynomial ℝ
  | 0, _ => 0
  | 1, _ => 1
  | n + 2, t =>
      C (2 * t) * finiteHilbertKernelPolynomial (n + 1) t -
        finiteHilbertKernelPolynomial n t +
        C 2 * T ℝ (n + 1)

@[simp] lemma finiteHilbertKernelPolynomial_zero (t : ℝ) :
    finiteHilbertKernelPolynomial 0 t = 0 := rfl

@[simp] lemma finiteHilbertKernelPolynomial_one (t : ℝ) :
    finiteHilbertKernelPolynomial 1 t = 1 := rfl

lemma finiteHilbertKernelPolynomial_add_two (n : ℕ) (t : ℝ) :
    finiteHilbertKernelPolynomial (n + 2) t =
      C (2 * t) * finiteHilbertKernelPolynomial (n + 1) t -
        finiteHilbertKernelPolynomial n t + C 2 * T ℝ (n + 1) := rfl

/-- Exact polynomial divided-difference identity for `T_n`. -/
theorem chebyshevT_sub_eval_eq_mul_finiteHilbertKernel
    (n : ℕ) (t : ℝ) :
    T ℝ n - C ((T ℝ n).eval t) =
      (X - C t) * finiteHilbertKernelPolynomial n t := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp [finiteHilbertKernelPolynomial]
  | more n ih0 ih1 =>
      rw [show ((n + 2 : ℕ) : ℤ) = (n : ℤ) + 2 by omega,
        T_add_two, finiteHilbertKernelPolynomial_add_two]
      simp only [eval_sub, eval_mul, eval_ofNat, eval_X,
        map_sub, map_mul, map_ofNat]
      norm_num only [Nat.cast_add, Nat.cast_one] at ih1
      calc
        2 * X * T ℝ ((n : ℤ) + 1) - T ℝ n -
              (2 * C t * C ((T ℝ ((n : ℤ) + 1)).eval t) -
                C ((T ℝ n).eval t)) =
            2 * (X - C t) * T ℝ ((n : ℤ) + 1) +
              2 * C t *
                (T ℝ ((n : ℤ) + 1) -
                  C ((T ℝ ((n : ℤ) + 1)).eval t)) -
              (T ℝ n - C ((T ℝ n).eval t)) := by ring
        _ = 2 * (X - C t) * T ℝ ((n : ℤ) + 1) +
              2 * C t *
                ((X - C t) * finiteHilbertKernelPolynomial (n + 1) t) -
              (X - C t) * finiteHilbertKernelPolynomial n t := by
            rw [ih0, ih1]
        _ = (X - C t) *
              (2 * C t * finiteHilbertKernelPolynomial (n + 1) t -
                finiteHilbertKernelPolynomial n t +
                2 * T ℝ ((n : ℤ) + 1)) := by ring

/-- The removable extension of the regularized finite Hilbert quotient. -/
def finiteHilbertRegularizedCos (n : ℕ) (theta phi : ℝ) : ℝ :=
  -(finiteHilbertKernelPolynomial n (Real.cos theta)).eval (Real.cos phi)

lemma continuous_finiteHilbertRegularizedCos (n : ℕ) (theta : ℝ) :
    Continuous (finiteHilbertRegularizedCos n theta) := by
  unfold finiteHilbertRegularizedCos
  fun_prop

lemma intervalIntegrable_finiteHilbertRegularizedCos
    (n : ℕ) (theta : ℝ) :
    IntervalIntegrable (finiteHilbertRegularizedCos n theta)
      volume 0 Real.pi :=
  (continuous_finiteHilbertRegularizedCos n theta).intervalIntegrable _ _

/-- Away from the removable diagonal, the polynomial extension is the
original regularized quotient. -/
theorem finiteHilbertRegularizedCos_eq_div
    {n : ℕ} {theta phi : ℝ}
    (hoff : Real.cos theta ≠ Real.cos phi) :
    finiteHilbertRegularizedCos n theta phi =
      (Real.cos ((n : ℝ) * phi) - Real.cos ((n : ℝ) * theta)) /
        (Real.cos theta - Real.cos phi) := by
  have hpoly := congrArg
    (fun p : Polynomial ℝ ↦ p.eval (Real.cos phi))
    (chebyshevT_sub_eval_eq_mul_finiteHilbertKernel n (Real.cos theta))
  simp only [eval_sub, eval_mul, eval_C, eval_X, T_real_cos] at hpoly
  unfold finiteHilbertRegularizedCos
  apply (eq_div_iff (sub_ne_zero.mpr hoff)).2
  calc
    -eval (Real.cos phi)
          (finiteHilbertKernelPolynomial n (Real.cos theta)) *
        (Real.cos theta - Real.cos phi) =
      (Real.cos phi - Real.cos theta) *
        eval (Real.cos phi)
          (finiteHilbertKernelPolynomial n (Real.cos theta)) := by ring
    _ = Real.cos ((n : ℝ) * phi) - Real.cos ((n : ℝ) * theta) :=
      hpoly.symm

lemma intervalIntegrable_chebyshevT_cos (n : ℕ) :
    IntervalIntegrable
      (fun phi : ℝ ↦ (T ℝ n).eval (Real.cos phi))
      volume 0 Real.pi := by
  simpa only [T_real_cos] using! intervalIntegrable_cos_nat_mul n

lemma intervalIntegrable_finiteHilbertKernel
    (n : ℕ) (t : ℝ) :
    IntervalIntegrable
      (fun phi : ℝ ↦
        (finiteHilbertKernelPolynomial n t).eval (Real.cos phi))
      volume 0 Real.pi := by
  apply Continuous.intervalIntegrable
  fun_prop

lemma integral_chebyshevT_cos_zero_pi {n : ℕ} (hn : 0 < n) :
    (∫ phi in 0..Real.pi, (T ℝ n).eval (Real.cos phi)) = 0 := by
  simp only [T_real_cos]
  simpa using! integral_cos_nat_mul_zero_pi hn

/-- The normalized mean of the divided-difference kernel is `U_(n-1)(t)`.
The index is written in `ℤ`, so the base case `n = 0` naturally uses
`U_(-1)=0`. -/
theorem one_div_pi_mul_integral_finiteHilbertKernel
    (n : ℕ) (t : ℝ) :
    (1 / Real.pi) *
        (∫ phi in 0..Real.pi,
          (finiteHilbertKernelPolynomial n t).eval (Real.cos phi)) =
      (U ℝ ((n : ℤ) - 1)).eval t := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one =>
      rw [show ((1 : ℕ) : ℤ) - 1 = 0 by norm_num]
      simp [finiteHilbertKernelPolynomial]
  | more n ih0 ih1 =>
      have hnext := intervalIntegrable_finiteHilbertKernel (n + 1) t
      have hprev := intervalIntegrable_finiteHilbertKernel n t
      have hT := intervalIntegrable_chebyshevT_cos (n + 1)
      norm_num only [Nat.cast_add, Nat.cast_one] at hT
      have hTint := integral_chebyshevT_cos_zero_pi
        (n := n + 1) (Nat.succ_pos n)
      norm_num only [Nat.cast_add, Nat.cast_one] at hTint
      rw [finiteHilbertKernelPolynomial_add_two]
      simp only [eval_add, eval_sub, eval_mul, eval_C]
      rw [intervalIntegral.integral_add
          ((hnext.const_mul (2 * t)).sub hprev) (hT.const_mul 2),
        intervalIntegral.integral_sub
          (hnext.const_mul (2 * t)) hprev,
        intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul,
        hTint]
      have hnext' :
          (1 / Real.pi) *
              (∫ phi in 0..Real.pi,
                (finiteHilbertKernelPolynomial (n + 1) t).eval
                  (Real.cos phi)) =
            (U ℝ (((n + 1 : ℕ) : ℤ) - 1)).eval t := ih1
      have hprev' :
          (1 / Real.pi) *
              (∫ phi in 0..Real.pi,
                (finiteHilbertKernelPolynomial n t).eval (Real.cos phi)) =
            (U ℝ ((n : ℤ) - 1)).eval t := ih0
      have hU := congrArg (fun p : Polynomial ℝ ↦ p.eval t)
        (U_add_two (R := ℝ) ((n : ℤ) - 1))
      simp only [eval_sub, eval_mul, eval_ofNat, eval_X] at hU
      rw [show (n : ℤ) - 1 + 1 = n by ring,
        show (n : ℤ) - 1 + 2 = (n : ℤ) + 1 by ring] at hU
      have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
      field_simp [hpi] at hnext' hprev' ⊢
      norm_num only [Nat.cast_add, Nat.cast_one] at hnext'
      rw [show (n : ℤ) + 1 - 1 = n by ring] at hnext'
      rw [show ((n + 2 : ℕ) : ℤ) - 1 = (n : ℤ) + 1 by omega]
      rw [hnext', hprev', hU]
      ring

/-- Exact finite Hilbert-transform identity in its removable form. -/
theorem one_div_pi_mul_integral_finiteHilbertRegularizedCos
    (n : ℕ) (theta : ℝ) :
    (1 / Real.pi) *
        (∫ phi in 0..Real.pi, finiteHilbertRegularizedCos n theta phi) =
      -(U ℝ ((n : ℤ) - 1)).eval (Real.cos theta) := by
  unfold finiteHilbertRegularizedCos
  rw [intervalIntegral.integral_neg]
  calc
    (1 / Real.pi) *
        -(∫ phi in 0..Real.pi,
          (finiteHilbertKernelPolynomial n (Real.cos theta)).eval
            (Real.cos phi)) =
      -((1 / Real.pi) *
        (∫ phi in 0..Real.pi,
          (finiteHilbertKernelPolynomial n (Real.cos theta)).eval
            (Real.cos phi))) := by ring
    _ = _ := by rw [one_div_pi_mul_integral_finiteHilbertKernel]

/-- Odd frequency `n=2m+1`: the transform is the negative even `U` mode. -/
theorem one_div_pi_mul_integral_finiteHilbertRegularizedCos_odd
    (m : ℕ) (theta : ℝ) :
    (1 / Real.pi) *
        (∫ phi in 0..Real.pi,
          finiteHilbertRegularizedCos (2 * m + 1) theta phi) =
      -evenSecondKindAngularMode m theta := by
  rw [one_div_pi_mul_integral_finiteHilbertRegularizedCos,
    evenSecondKindAngularMode_eq_chebyshevU]
  congr 2
  simp [evenSecondKindIndex]

/-- Positive even frequency `n=2(m+1)`: the transform is the negative odd
`U` mode with `m+1` summands. -/
theorem one_div_pi_mul_integral_finiteHilbertRegularizedCos_even
    (m : ℕ) (theta : ℝ) :
    (1 / Real.pi) *
        (∫ phi in 0..Real.pi,
          finiteHilbertRegularizedCos (2 * (m + 1)) theta phi) =
      -oddSecondKindAngularMode (m + 1) theta := by
  rw [one_div_pi_mul_integral_finiteHilbertRegularizedCos,
    oddSecondKindAngularMode_eq_chebyshevU]
  congr 2

end

end Erdos1038
