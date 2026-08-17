import ErdosProblems.Erdos543.FiniteProbability

/-!
# Quantitative Bonferroni-to-Poisson estimates

This file isolates the analytic last step in the factorial-moment method used
for Erdős Problem 543.  Uniform relative control of the factorial moments up
to an odd Bonferroni order yields an explicit estimate for the zero event.

The error has two parts: the finite exponential-series tail and the accumulated
factorial-moment error.  The latter is deliberately stated quantitatively; in
applications it must be small compared with `exp (-lambda)`.
-/

open scoped BigOperators

namespace Erdos543.BonferroniAnalytic

open Finset
open Erdos543.FiniteProbability

noncomputable section

variable {Omega : Type*} [Fintype Omega]

/-- The alternating exponential polynomial through degree `m`. -/
noncomputable def poissonTrunc (lambda : ℝ) (m : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (m + 1),
    (-1 : ℝ) ^ j * lambda ^ j / (j.factorial : ℝ)

/-- Rewriting the alternating Poisson polynomial as the Taylor polynomial of
`exp` at `-lambda`. -/
theorem poissonTrunc_eq_sum_pow_neg (lambda : ℝ) (m : ℕ) :
    poissonTrunc lambda m =
      ∑ j ∈ Finset.range (m + 1),
        (-lambda) ^ j / (j.factorial : ℝ) := by
  apply Finset.sum_congr rfl
  intro j hj
  rw [neg_pow]
  ring

/-- The error between a Bonferroni sum and the corresponding Poisson
polynomial is at most the sum of the individual factorial-moment errors. -/
theorem abs_bonferroniSum_sub_poissonTrunc_le
    (Z : Omega → ℕ) (lambda : ℝ) (m : ℕ) :
    |bonferroniSum Z m - poissonTrunc lambda m| ≤
      ∑ j ∈ Finset.range (m + 1),
        |factorialMoment Z j - lambda ^ j| / (j.factorial : ℝ) := by
  rw [bonferroniSum, poissonTrunc, ← Finset.sum_sub_distrib]
  calc
    |∑ j ∈ Finset.range (m + 1),
        ((-1 : ℝ) ^ j * factorialMoment Z j / (j.factorial : ℝ) -
          (-1 : ℝ) ^ j * lambda ^ j / (j.factorial : ℝ))| ≤
        ∑ j ∈ Finset.range (m + 1),
          |(-1 : ℝ) ^ j * factorialMoment Z j / (j.factorial : ℝ) -
            (-1 : ℝ) ^ j * lambda ^ j / (j.factorial : ℝ)| := by
      exact Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j ∈ Finset.range (m + 1),
          |factorialMoment Z j - lambda ^ j| / (j.factorial : ℝ) := by
      apply Finset.sum_congr rfl
      intro j hj
      have halg :
          (-1 : ℝ) ^ j * factorialMoment Z j / (j.factorial : ℝ) -
              (-1 : ℝ) ^ j * lambda ^ j / (j.factorial : ℝ) =
            (-1 : ℝ) ^ j * (factorialMoment Z j - lambda ^ j) /
              (j.factorial : ℝ) := by ring
      have hfactorial : |(j.factorial : ℝ)| = (j.factorial : ℝ) :=
        abs_of_nonneg (Nat.cast_nonneg _)
      rw [halg, abs_div, abs_mul, abs_neg_one_pow, one_mul, hfactorial]

/-- Uniform relative factorial-moment error through order `m` accumulates to
at most `epsilon` times the positive exponential polynomial. -/
theorem abs_bonferroniSum_sub_poissonTrunc_le_rel
    (Z : Omega → ℕ) {lambda epsilon : ℝ} {m R : ℕ}
    (_hlambda : 0 ≤ lambda) (_hepsilon : 0 ≤ epsilon) (hmR : m ≤ R)
    (hmom : ∀ j ≤ R,
      |factorialMoment Z j - lambda ^ j| ≤ epsilon * lambda ^ j) :
    |bonferroniSum Z m - poissonTrunc lambda m| ≤
      epsilon * ∑ j ∈ Finset.range (m + 1),
        lambda ^ j / (j.factorial : ℝ) := by
  refine (abs_bonferroniSum_sub_poissonTrunc_le Z lambda m).trans ?_
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  have hjR : j ≤ R := by
    have hjm : j ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    exact hjm.trans hmR
  have hfac : (0 : ℝ) ≤ (j.factorial : ℝ) := by positivity
  calc
    |factorialMoment Z j - lambda ^ j| / (j.factorial : ℝ) ≤
        (epsilon * lambda ^ j) / (j.factorial : ℝ) :=
      div_le_div_of_nonneg_right (hmom j hjR) hfac
    _ = epsilon * (lambda ^ j / (j.factorial : ℝ)) := by ring

/-- A convenient exponential upper bound for the accumulated relative
factorial-moment error. -/
theorem abs_bonferroniSum_sub_poissonTrunc_le_exp
    (Z : Omega → ℕ) {lambda epsilon : ℝ} {m R : ℕ}
    (hlambda : 0 ≤ lambda) (hepsilon : 0 ≤ epsilon) (hmR : m ≤ R)
    (hmom : ∀ j ≤ R,
      |factorialMoment Z j - lambda ^ j| ≤ epsilon * lambda ^ j) :
    |bonferroniSum Z m - poissonTrunc lambda m| ≤ epsilon * Real.exp lambda := by
  refine (abs_bonferroniSum_sub_poissonTrunc_le_rel Z hlambda hepsilon hmR hmom).trans ?_
  exact mul_le_mul_of_nonneg_left
    (Real.sum_le_exp_of_nonneg hlambda (m + 1)) hepsilon

/-- Explicit exponential-series tail bound, valid once the truncation order
is at least twice the size of the argument. -/
theorem abs_exp_neg_sub_poissonTrunc_le
    {lambda : ℝ} {n : ℕ} (hlambda : 0 ≤ lambda) (hn : 0 < n)
    (htrunc : lambda / (n + 1 : ℝ) ≤ 1 / 2) :
    |Real.exp (-lambda) - poissonTrunc lambda (n - 1)| ≤
      2 * lambda ^ n / (n.factorial : ℝ) := by
  have hcomplex :
        ‖Complex.exp (-(lambda : ℂ)) -
            ∑ j ∈ Finset.range n,
              (-(lambda : ℂ)) ^ j / (j.factorial : ℂ)‖ ≤
          ‖-(lambda : ℂ)‖ ^ n / (n.factorial : ℝ) * 2 := by
      apply Complex.exp_bound'
      simpa [Complex.norm_real, abs_of_nonneg hlambda] using htrunc
  have hnsub : n - 1 + 1 = n := Nat.sub_add_cancel hn
  rw [poissonTrunc_eq_sum_pow_neg, hnsub]
  have hcast :
        ((Real.exp (-lambda) -
            ∑ j ∈ Finset.range n, (-lambda) ^ j / (j.factorial : ℝ) : ℝ) : ℂ) =
          Complex.exp (-(lambda : ℂ)) -
            ∑ j ∈ Finset.range n,
              (-(lambda : ℂ)) ^ j / (j.factorial : ℂ) := by
    norm_cast
  calc
    |Real.exp (-lambda) -
        ∑ j ∈ Finset.range n, (-lambda) ^ j / (j.factorial : ℝ)| =
        ‖Complex.exp (-(lambda : ℂ)) -
          ∑ j ∈ Finset.range n,
            (-(lambda : ℂ)) ^ j / (j.factorial : ℂ)‖ := by
      rw [← Real.norm_eq_abs, ← Complex.norm_real, hcast]
    _ ≤ ‖-(lambda : ℂ)‖ ^ n / (n.factorial : ℝ) * 2 := hcomplex
    _ = 2 * lambda ^ n / (n.factorial : ℝ) := by
      rw [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlambda]
      ring

/-- Absolute error form of the quantitative factorial-moment criterion.

The moments are controlled through order `2*r+1`.  The condition
`lambda ≤ r+1` is exactly what is needed to control both adjacent Taylor
truncations by a geometric tail estimate. -/
theorem abs_prob_zero_sub_exp_neg_le
    [Nonempty Omega] (Z : Omega → ℕ) {lambda epsilon : ℝ} {r : ℕ}
    (hlambda : 0 ≤ lambda) (hepsilon : 0 ≤ epsilon)
    (htrunc : lambda ≤ (r + 1 : ℕ))
    (hmom : ∀ j ≤ 2 * r + 1,
      |factorialMoment Z j - lambda ^ j| ≤ epsilon * lambda ^ j) :
    |prob {omega | Z omega = 0} - Real.exp (-lambda)| ≤
      2 * lambda ^ (2 * r + 1) / ((2 * r + 1).factorial : ℝ) +
        epsilon * Real.exp lambda := by
  let P : ℝ := prob {omega | Z omega = 0}
  let TEven : ℝ := poissonTrunc lambda (2 * r)
  let TOdd : ℝ := poissonTrunc lambda (2 * r + 1)
  let tail : ℝ := 2 * lambda ^ (2 * r + 1) /
    ((2 * r + 1).factorial : ℝ)
  let momentError : ℝ := epsilon * Real.exp lambda
  have hPupper : P ≤ bonferroniSum Z (2 * r) := by
    exact prob_eq_zero_le_bonferroni_even Z r
  have hPlower : bonferroniSum Z (2 * r + 1) ≤ P := by
    exact bonferroni_odd_le_prob_eq_zero Z r
  have hEvenMoment : |bonferroniSum Z (2 * r) - TEven| ≤ momentError := by
    exact abs_bonferroniSum_sub_poissonTrunc_le_exp Z hlambda hepsilon
      (by omega) hmom
  have hOddMoment : |bonferroniSum Z (2 * r + 1) - TOdd| ≤ momentError := by
    exact abs_bonferroniSum_sub_poissonTrunc_le_exp Z hlambda hepsilon
      (by omega) hmom
  have hdenomEven :
      lambda / (((2 * r + 1 : ℕ) : ℝ) + 1) ≤ (1 / 2 : ℝ) := by
    have hden : (0 : ℝ) < ((2 * r + 1 : ℕ) : ℝ) + 1 := by positivity
    rw [div_le_iff₀ hden]
    norm_num [Nat.cast_add, Nat.cast_mul] at htrunc ⊢
    linarith
  have hEvenTaylor : |Real.exp (-lambda) - TEven| ≤ tail := by
    simpa [TEven, tail] using
      (abs_exp_neg_sub_poissonTrunc_le (n := 2 * r + 1) hlambda (by omega)
        hdenomEven)
  have hdenomOdd :
      lambda / (((2 * r + 2 : ℕ) : ℝ) + 1) ≤ (1 / 2 : ℝ) := by
    have hden : (0 : ℝ) < ((2 * r + 2 : ℕ) : ℝ) + 1 := by positivity
    rw [div_le_iff₀ hden]
    norm_num [Nat.cast_add, Nat.cast_mul] at htrunc ⊢
    linarith
  have hOddTaylorRaw :
      |Real.exp (-lambda) - TOdd| ≤
        2 * lambda ^ (2 * r + 2) / ((2 * r + 2).factorial : ℝ) := by
    simpa [TOdd] using
      (abs_exp_neg_sub_poissonTrunc_le (n := 2 * r + 2) hlambda (by omega)
        hdenomOdd)
  have hOddTailLe :
      2 * lambda ^ (2 * r + 2) / ((2 * r + 2).factorial : ℝ) ≤ tail := by
    have hratio : lambda / (2 * r + 2 : ℕ) ≤ 1 := by
      have hdenom : (0 : ℝ) < (2 * r + 2 : ℕ) := by positivity
      apply (div_le_one hdenom).2
      exact htrunc.trans (by norm_cast; omega)
    have htailnonneg : 0 ≤ tail := by
      dsimp [tail]
      positivity
    have heq :
        2 * lambda ^ (2 * r + 2) / ((2 * r + 2).factorial : ℝ) =
          tail * (lambda / (2 * r + 2 : ℕ)) := by
      dsimp [tail]
      rw [show 2 * r + 2 = (2 * r + 1) + 1 by omega, pow_succ,
        Nat.factorial_succ]
      push_cast
      field_simp
    rw [heq]
    exact mul_le_of_le_one_right htailnonneg hratio
  have hOddTaylor : |Real.exp (-lambda) - TOdd| ≤ tail :=
    hOddTaylorRaw.trans hOddTailLe
  rw [abs_le] at hEvenMoment hOddMoment hEvenTaylor hOddTaylor ⊢
  constructor
  · calc
      -(tail + momentError) ≤ TOdd - momentError - Real.exp (-lambda) := by
        linarith [hOddTaylor.1]
      _ ≤ bonferroniSum Z (2 * r + 1) - Real.exp (-lambda) := by
        linarith [hOddMoment.1]
      _ ≤ P - Real.exp (-lambda) := by linarith
  · calc
      P - Real.exp (-lambda) ≤
          bonferroniSum Z (2 * r) - Real.exp (-lambda) := by linarith
      _ ≤ TEven + momentError - Real.exp (-lambda) := by
        linarith [hEvenMoment.2]
      _ ≤ tail + momentError := by linarith [hEvenTaylor.2]

/-- Relative-error form of `abs_prob_zero_sub_exp_neg_le`.  This is the form
used in Poisson approximation: after division by `exp (-lambda)`, the moment
error is amplified by `exp (2*lambda)`. -/
theorem abs_prob_zero_div_exp_neg_sub_one_le
    [Nonempty Omega] (Z : Omega → ℕ) {lambda epsilon : ℝ} {r : ℕ}
    (hlambda : 0 ≤ lambda) (hepsilon : 0 ≤ epsilon)
    (htrunc : lambda ≤ (r + 1 : ℕ))
    (hmom : ∀ j ≤ 2 * r + 1,
      |factorialMoment Z j - lambda ^ j| ≤ epsilon * lambda ^ j) :
    |prob {omega | Z omega = 0} / Real.exp (-lambda) - 1| ≤
      Real.exp lambda *
        (2 * lambda ^ (2 * r + 1) / ((2 * r + 1).factorial : ℝ) +
          epsilon * Real.exp lambda) := by
  have habs := abs_prob_zero_sub_exp_neg_le Z hlambda hepsilon htrunc hmom
  have hexp : Real.exp (-lambda) ≠ 0 := (Real.exp_pos _).ne'
  rw [div_sub_one hexp, abs_div, abs_of_pos (Real.exp_pos _),
    Real.exp_neg, div_inv_eq_mul]
  rw [Real.exp_neg] at habs
  simpa [mul_comm] using
    (mul_le_mul_of_nonneg_left habs (Real.exp_pos lambda).le)

/-- Version of the relative factorial-moment criterion with a separately
named available truncation order `R`.  Any odd Bonferroni order `2*r+1` below
`R` may be selected. -/
theorem abs_prob_zero_div_exp_neg_sub_one_le_of_le
    [Nonempty Omega] (Z : Omega → ℕ) {lambda epsilon : ℝ} {r R : ℕ}
    (hlambda : 0 ≤ lambda) (hepsilon : 0 ≤ epsilon)
    (htrunc : lambda ≤ (r + 1 : ℕ)) (horder : 2 * r + 1 ≤ R)
    (hmom : ∀ j ≤ R,
      |factorialMoment Z j - lambda ^ j| ≤ epsilon * lambda ^ j) :
    |prob {omega | Z omega = 0} / Real.exp (-lambda) - 1| ≤
      Real.exp lambda *
        (2 * lambda ^ (2 * r + 1) / ((2 * r + 1).factorial : ℝ) +
          epsilon * Real.exp lambda) := by
  apply abs_prob_zero_div_exp_neg_sub_one_le Z hlambda hepsilon htrunc
  intro j hj
  exact hmom j (hj.trans horder)

end

end Erdos543.BonferroniAnalytic
