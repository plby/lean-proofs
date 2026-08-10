import Arxiv.Arxiv2407_19026.NumericalProfilesLimitTrimmed

/-!
# Bernstein-polynomial support for the first-profile limit certificate

This recursive form records the same unnormalized Bernstein basis used by
the exact certificates, while making coefficient nonnegativity immediate
from the coefficient type.
-/

namespace Arxiv2407_19026

noncomputable section

def beta0BernsteinValue :
    ℕ → List ℕ → ℝ → ℝ
  | _, [], _ => 0
  | 0, coefficient :: _, _ => coefficient
  | n + 1, coefficient :: coefficients, u =>
      coefficient * (1 - u) ^ (n + 1) +
        u * beta0BernsteinValue n coefficients u

def beta0BernsteinPower :
    ℕ → List ℕ → RationalPowerPolynomial
  | _, [] => []
  | 0, coefficient :: _ => [coefficient]
  | n + 1, coefficient :: coefficients =>
      rationalPowerAdd
        (rationalPowerScale coefficient
          (rationalPowerPow [1, -1] (n + 1)))
        (rationalPowerMul [0, 1]
          (beta0BernsteinPower n coefficients))

def rationalPowerCompWithTail
    (initial : RationalPowerPolynomial)
    (tail : RationalPowerPolynomial)
    (q : RationalPowerPolynomial) :
    RationalPowerPolynomial :=
  match initial with
  | [] => tail
  | coefficient :: coefficients =>
      rationalPowerAdd [coefficient]
        (rationalPowerMul q
          (rationalPowerCompWithTail coefficients tail q))

def beta0BernsteinPowerWithTail :
    ℕ → List ℕ → RationalPowerPolynomial →
      RationalPowerPolynomial
  | _, [], tail => tail
  | 0, coefficient :: _, _ => [coefficient]
  | n + 1, coefficient :: coefficients, tail =>
      rationalPowerAdd
        (rationalPowerScale coefficient
          (rationalPowerPow [1, -1] (n + 1)))
        (rationalPowerMul [0, 1]
          (beta0BernsteinPowerWithTail
            n coefficients tail))

lemma rational_power_comp_append
    (initial suffix q : RationalPowerPolynomial) :
    rationalPowerComp (initial ++ suffix) q =
      rationalPowerCompWithTail initial
        (rationalPowerComp suffix q) q := by
  induction initial with
  | nil =>
      rfl
  | cons coefficient coefficients ih =>
      simp only [List.cons_append, rationalPowerComp,
        rationalPowerCompWithTail]
      rw [ih]

lemma beta0_bernstein_power_append
    (n : ℕ) (initial suffix : List ℕ)
    (hinitial : initial.length ≤ n) :
    beta0BernsteinPower n (initial ++ suffix) =
      beta0BernsteinPowerWithTail n initial
        (beta0BernsteinPower
          (n - initial.length) suffix) := by
  induction initial generalizing n with
  | nil =>
      simp [beta0BernsteinPowerWithTail]
  | cons coefficient coefficients ih =>
      cases n with
      | zero =>
          simp at hinitial
      | succ n =>
          have hcoefficients : coefficients.length ≤ n := by
            simpa using hinitial
          simp only [List.cons_append,
            beta0BernsteinPower,
            beta0BernsteinPowerWithTail]
          rw [ih n hcoefficients]
          congr 3
          simp

lemma beta0_bernstein_value_nonneg
    (n : ℕ) (coefficients : List ℕ)
    {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ beta0BernsteinValue n coefficients u := by
  induction n generalizing coefficients with
  | zero =>
      cases coefficients <;>
        simp [beta0BernsteinValue]
  | succ n ih =>
      cases coefficients with
      | nil =>
          simp [beta0BernsteinValue]
      | cons coefficient coefficients =>
          rw [beta0BernsteinValue]
          exact add_nonneg
            (mul_nonneg (Nat.cast_nonneg _)
              (pow_nonneg (sub_nonneg.mpr hu.2) _))
            (mul_nonneg hu.1 (ih coefficients))

lemma beta0_bernstein_power_eval
    (n : ℕ) (coefficients : List ℕ) (u : ℝ) :
    rationalPowerEval
        (beta0BernsteinPower n coefficients) u =
      beta0BernsteinValue n coefficients u := by
  induction n generalizing coefficients with
  | zero =>
      cases coefficients <;>
        norm_num [beta0BernsteinPower,
          beta0BernsteinValue, rationalPowerEval]
  | succ n ih =>
      cases coefficients with
      | nil =>
          simp [beta0BernsteinPower,
            beta0BernsteinValue, rationalPowerEval]
      | cons coefficient coefficients =>
          rw [beta0BernsteinPower,
            rationalPowerEval_add,
            rationalPowerEval_scale,
            rationalPowerEval_pow,
            rationalPowerEval_mul, ih]
          rw [show rationalPowerEval [1, -1] u =
              1 - u by
            norm_num [rationalPowerEval]
            all_goals ring]
          rw [show rationalPowerEval [0, 1] u = u by
            norm_num [rationalPowerEval]]
          rfl

end

end Arxiv2407_19026
