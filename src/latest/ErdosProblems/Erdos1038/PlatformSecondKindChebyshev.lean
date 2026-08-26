import ErdosProblems.Erdos1038.PlatformPoissonSecondKind
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic

/-!
# Identification of the angular modes with Chebyshev `U`

The Poisson moment calculation used explicit finite cosine sums.  Here we
identify those sums with mathlib's Chebyshev polynomials of the second kind.
This is the exact interface needed by the finite Hilbert-transform identity.
-/

set_option warningAsError false

open Polynomial

namespace Erdos1038

noncomputable section

open Polynomial.Chebyshev

/-- Even second-kind index `2m`, expressed as an integer. -/
def evenSecondKindIndex (m : ℕ) : ℤ := 2 * (m : ℤ)

/-- Odd second-kind index `2m-1`, including the base index `-1`. -/
def oddSecondKindIndex (m : ℕ) : ℤ := 2 * (m : ℤ) - 1

/-- The elementary two-step identity `U_n-U_{n-2}=2T_n`. -/
theorem chebyshevU_sub_two_eq_two_mul_T (n : ℤ) :
    U ℝ n - U ℝ (n - 2) = 2 * T ℝ n := by
  have hT := T_eq_U_sub_X_mul_U (R := ℝ) n
  have hU := U_eq (R := ℝ) n
  have hprev : U ℝ (n - 2) = 2 * X * U ℝ (n - 1) - U ℝ n := by
    linear_combination hU
  rw [hprev]
  calc
    U ℝ n - (2 * X * U ℝ (n - 1) - U ℝ n) =
        2 * (U ℝ n - X * U ℝ (n - 1)) := by ring
    _ = 2 * T ℝ n := by rw [← hT]

lemma chebyshevU_eval_two_step (n : ℤ) (theta : ℝ) :
    (U ℝ n).eval (Real.cos theta) =
      (U ℝ (n - 2)).eval (Real.cos theta) +
        2 * Real.cos ((n : ℝ) * theta) := by
  have h := congrArg (fun p : Polynomial ℝ ↦ p.eval (Real.cos theta))
    (chebyshevU_sub_two_eq_two_mul_T n)
  simp only [eval_sub, eval_mul, eval_ofNat, T_real_cos] at h
  linarith

/-- The explicit even cosine sum is exactly `U_(2m)(cos θ)`. -/
theorem evenSecondKindAngularMode_eq_chebyshevU
    (m : ℕ) (theta : ℝ) :
    evenSecondKindAngularMode m theta =
      (U ℝ (evenSecondKindIndex m)).eval (Real.cos theta) := by
  induction m with
  | zero => simp [evenSecondKindAngularMode, evenSecondKindIndex]
  | succ m ih =>
      rw [evenSecondKindAngularMode_succ, ih]
      have h := (chebyshevU_eval_two_step
        (evenSecondKindIndex (m + 1)) theta).symm
      have hindex : evenSecondKindIndex (m + 1) - 2 =
          evenSecondKindIndex m := by
        simp [evenSecondKindIndex]
        ring
      rw [hindex] at h
      have hfrequency : ((evenSecondKindIndex (m + 1) : ℤ) : ℝ) =
          ((2 * (m + 1) : ℕ) : ℝ) := by
        simp [evenSecondKindIndex]
      rw [hfrequency] at h
      exact h

/-- The explicit odd cosine sum is exactly `U_(2m-1)(cos θ)`. -/
theorem oddSecondKindAngularMode_eq_chebyshevU
    (m : ℕ) (theta : ℝ) :
    oddSecondKindAngularMode m theta =
      (U ℝ (oddSecondKindIndex m)).eval (Real.cos theta) := by
  induction m with
  | zero => simp [oddSecondKindAngularMode, oddSecondKindIndex]
  | succ m ih =>
      rw [oddSecondKindAngularMode_succ, ih]
      have h := (chebyshevU_eval_two_step
        (oddSecondKindIndex (m + 1)) theta).symm
      have hindex : oddSecondKindIndex (m + 1) - 2 =
          oddSecondKindIndex m := by
        simp [oddSecondKindIndex]
        ring
      rw [hindex] at h
      have hfrequency : ((oddSecondKindIndex (m + 1) : ℤ) : ℝ) =
          ((2 * m + 1 : ℕ) : ℝ) := by
        simp [oddSecondKindIndex]
        ring
      rw [hfrequency] at h
      exact h

end

end Erdos1038
