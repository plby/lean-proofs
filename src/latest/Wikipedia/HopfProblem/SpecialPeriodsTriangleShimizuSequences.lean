import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Convergence of the Shimizu matrix recurrences

The lower-left and upper-left matrix entries in the conjugation argument satisfy
`q (n + 1) = -(q n)^2` and `a (n + 1) = 1 - a n * q n`.  A strict initial
bound on `|q 0|` gives geometric decay of `q`, a uniform bound on `a`, and the
limits `q → 0` and `a → 1`.
-/

noncomputable section

open Filter
open scoped Topology

namespace Wikipedia.HopfProblem.SpecialPeriods.Triangle

theorem shimizu_recurrence_abs_le_initial (q : ℕ → ℝ)
    (hq : ∀ n, q (n + 1) = -(q n) ^ 2) (hsmall : |q 0| ≤ 1) (n : ℕ) :
    |q n| ≤ |q 0| := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
      rw [hq, abs_neg, abs_pow, pow_two]
      calc
        |q n| * |q n| ≤ |q 0| * |q 0| :=
          mul_le_mul ih ih (abs_nonneg _) (abs_nonneg _)
        _ ≤ |q 0| := by nlinarith [abs_nonneg (q 0)]

/-- An ordinary geometric bound suffices, although the recurrence decays faster. -/
theorem shimizu_recurrence_geometric_bound (q : ℕ → ℝ)
    (hq : ∀ n, q (n + 1) = -(q n) ^ 2) (hsmall : |q 0| ≤ 1) (n : ℕ) :
    |q n| ≤ |q 0| ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [hq, abs_neg, abs_pow, pow_two]
      calc
        |q n| * |q n| ≤ |q 0| * |q 0| ^ (n + 1) :=
          mul_le_mul (shimizu_recurrence_abs_le_initial q hq hsmall n) ih
            (abs_nonneg _) (abs_nonneg _)
        _ = |q 0| ^ (n + 1 + 1) := by rw [pow_succ]; ring

theorem shimizu_recurrence_a_bound (q a : ℕ → ℝ)
    (hq : ∀ n, q (n + 1) = -(q n) ^ 2)
    (ha : ∀ n, a (n + 1) = 1 - a n * q n) (hsmall : |q 0| < 1) (n : ℕ) :
    |a n| ≤ (1 + |a 0|) / (1 - |q 0|) := by
  let M : ℝ := (1 + |a 0|) / (1 - |q 0|)
  have hd : 0 < 1 - |q 0| := sub_pos.mpr hsmall
  have hM : 0 ≤ M := div_nonneg (by positivity) hd.le
  have hM_eq : M * (1 - |q 0|) = 1 + |a 0| :=
    div_mul_cancel₀ _ hd.ne'
  have hM_step : 1 + M * |q 0| ≤ M := by
    nlinarith [abs_nonneg (a 0)]
  change |a n| ≤ M
  induction n with
  | zero =>
      apply (le_div_iff₀ hd).mpr
      nlinarith [mul_nonneg (abs_nonneg (a 0)) (abs_nonneg (q 0))]
  | succ n ih =>
      rw [ha]
      calc
        |1 - a n * q n| ≤ |(1 : ℝ)| + |a n * q n| := by
          simpa only [Real.norm_eq_abs] using norm_sub_le (1 : ℝ) (a n * q n)
        _ = 1 + |a n| * |q n| := by rw [abs_one, abs_mul]
        _ ≤ 1 + M * |q 0| :=
          add_le_add (le_refl 1) (mul_le_mul ih
            (shimizu_recurrence_abs_le_initial q hq hsmall.le n) (abs_nonneg _) hM)
        _ ≤ M := hM_step

/-- The coupled recurrences tend to the parabolic matrix entries. -/
theorem shimizu_recurrence_tendsto (q a : ℕ → ℝ)
    (hq : ∀ n, q (n + 1) = -(q n) ^ 2)
    (ha : ∀ n, a (n + 1) = 1 - a n * q n) (hsmall : |q 0| < 1) :
    Tendsto q atTop (𝓝 0) ∧ Tendsto a atTop (𝓝 1) := by
  have hpow : Tendsto (fun n : ℕ => |q 0| ^ (n + 1)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (abs_nonneg _) hsmall).comp
      (tendsto_add_atTop_nat 1)
  have hqt : Tendsto q atTop (𝓝 0) := by
    apply squeeze_zero_norm (f := q) (fun n => ?_) hpow
    exact shimizu_recurrence_geometric_bound q hq hsmall.le n
  let M : ℝ := (1 + |a 0|) / (1 - |q 0|)
  have hM : 0 ≤ M := div_nonneg (by positivity) (sub_pos.mpr hsmall).le
  have hprod : Tendsto (fun n => a n * q n) atTop (𝓝 0) := by
    refine squeeze_zero_norm (f := fun n : ℕ => a n * q n)
      (a := fun n => M * |q 0| ^ (n + 1)) ?_ ?_
    · intro n
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (shimizu_recurrence_a_bound q a hq ha hsmall n)
        (shimizu_recurrence_geometric_bound q hq hsmall.le n) (abs_nonneg _) hM
    · simpa only [mul_zero] using hpow.const_mul M
  refine ⟨hqt, (tendsto_add_atTop_iff_nat 1).mp ?_⟩
  simpa only [ha, sub_zero] using hprod.const_sub 1

end Wikipedia.HopfProblem.SpecialPeriods.Triangle
