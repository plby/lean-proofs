import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.HasseDeriv
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic

/-!
# Reduced derivatives for the quadratic Stepanov polynomial

Multiplication by `f^k` clears the denominators from differentiating
`f^t g`.  The resulting polynomial has degree growing only linearly in
the derivative order, independently of the exponent `t`.
-/

namespace Pollack17.Stepanov

open Polynomial

variable {K : Type*} [Field K]

noncomputable def reducedDerivative (f : K[X]) (t : K) (g : K[X]) : ℕ → K[X]
  | 0 => g
  | k + 1 => f * (reducedDerivative f t g k).derivative +
      C (t - k) * f.derivative * reducedDerivative f t g k

theorem mul_derivative_pow (f : K[X]) (k : ℕ) :
    f * (f ^ k).derivative = C (k : K) * f ^ k * f.derivative := by
  cases k with
  | zero => simp
  | succ k =>
    rw [derivative_pow_succ, pow_succ]
    push_cast
    ring

theorem mul_derivative_pow_mul (f g : K[X]) (k : ℕ) :
    f * (f ^ k * g).derivative =
      C (k : K) * f ^ k * f.derivative * g + f ^ (k + 1) * g.derivative := by
  rw [derivative_mul, mul_add, ← mul_assoc, mul_derivative_pow]
  rw [pow_succ]
  ring

theorem pow_mul_iterate_derivative (f g : K[X]) (t k : ℕ) :
    f ^ k * derivative^[k] (f ^ t * g) =
      f ^ t * reducedDerivative f (t : K) g k := by
  induction k with
  | zero => simp [reducedDerivative]
  | succ k ih =>
    have hderiv := congrArg (fun P : K[X] => f * P.derivative) ih
    rw [mul_derivative_pow_mul, mul_derivative_pow_mul] at hderiv
    simp only [map_natCast] at hderiv
    rw [Function.iterate_succ_apply', reducedDerivative]
    simp only [map_sub, map_natCast]
    linear_combination hderiv - (k : K[X]) * f.derivative * ih

theorem reducedDerivative_natDegree_le (f g : K[X]) (t : K) (k : ℕ) :
    (reducedDerivative f t g k).natDegree ≤ g.natDegree + k * f.natDegree := by
  induction k with
  | zero => simp [reducedDerivative]
  | succ k ih =>
    rw [reducedDerivative]
    apply (Polynomial.natDegree_add_le _ _).trans
    apply max_le
    · have hderiv := (Polynomial.natDegree_derivative_le
        (reducedDerivative f t g k)).trans (Nat.sub_le _ _)
      have hmul := Polynomial.natDegree_mul_le
        (p := f) (q := (reducedDerivative f t g k).derivative)
      nlinarith
    · have hderiv := (Polynomial.natDegree_derivative_le f).trans (Nat.sub_le _ _)
      have hconst := Polynomial.natDegree_C_mul_le (t - (k : K)) f.derivative
      have hmul := Polynomial.natDegree_mul_le
        (p := C (t - (k : K)) * f.derivative) (q := reducedDerivative f t g k)
      nlinarith

theorem iterate_derivative_mul_of_derivative_zero (g H : K[X])
    (hH : H.derivative = 0) (k : ℕ) :
    derivative^[k] (g * H) = derivative^[k] g * H := by
  induction k with
  | zero => rfl
  | succ k ih => simp [Function.iterate_succ_apply', ih, derivative_mul, hH]

theorem derivative_frobenius_monomial {p : ℕ} [CharP K p] (b : ℕ) :
    (X ^ (p * b) : K[X]).derivative = 0 := by
  rw [derivative_X_pow]
  simp [Nat.cast_mul]

theorem eval_pow_mul_iterate_derivative_frobenius {p : ℕ} [CharP K p]
    (f g : K[X]) (t k b : ℕ) (x : K) (hx : x ^ p = x) :
    f.eval x ^ k * (derivative^[k] ((f ^ t * g) * X ^ (p * b))).eval x =
      f.eval x ^ t * (reducedDerivative f (t : K) g k).eval x * x ^ b := by
  rw [iterate_derivative_mul_of_derivative_zero _ _ (derivative_frobenius_monomial b)]
  simp only [eval_mul, eval_pow, eval_X]
  rw [pow_mul, hx, ← mul_assoc]
  have h := congrArg (fun P : K[X] => P.eval x) (pow_mul_iterate_derivative f g t k)
  simpa only [eval_mul, eval_pow] using congrArg (fun z : K => z * x ^ b) h

end Pollack17.Stepanov
