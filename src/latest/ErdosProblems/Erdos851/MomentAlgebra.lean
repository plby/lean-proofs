/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos851.FiniteSecondMoment
import Mathlib.Tactic.Linarith

/-!
# Numerical second-moment assembly for Erdős problem 851

This packages the only real-algebra calculation used after the arithmetic
first- and second-moment estimates.  The constants are intentionally loose:
an error parameter `η` yields exceptional proportion at most `6η`.
-/

open scoped BigOperators

namespace Erdos851

/-- A large mean and nearly independent second moment force positive support
on at least a `1-6η` proportion of a finite set. -/
theorem one_sub_six_mul_le_positiveSupport
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (R : ι → ℕ)
    {η μ X : ℝ}
    (hη : 0 < η) (hηsmall : η ≤ 1 / 6)
    (hμ : 0 < μ) (hlarge : 1 ≤ η * μ)
    (hX : 0 < X)
    (hfirst : (1 - η) * μ * X ≤ ∑ i ∈ S, (R i : ℝ))
    (hsecond : (∑ i ∈ S, (R i : ℝ) ^ 2) ≤
      (1 + 2 * η) * μ ^ 2 * X + μ * X) :
    (1 - 6 * η) * X ≤ ((S.filter fun i ↦ 0 < R i).card : ℝ) := by
  let L : ℝ := (1 - η) * μ * X
  let U : ℝ := (1 + 2 * η) * μ ^ 2 * X + μ * X
  have hL : 0 ≤ L := by
    dsimp [L]
    have : 0 ≤ 1 - η := by linarith
    positivity
  have hU : 0 < U := by
    dsimp [U]
    have hcoef : 0 < 1 + 2 * η := by linarith
    positivity
  have hpaley : L ^ 2 ≤
      ((S.filter fun i ↦ 0 < R i).card : ℝ) * U :=
    lower_sq_le_card_pos_mul_upper S R hL hfirst hsecond
  have hmuAbsorb : μ ≤ η * μ ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hlarge hμ.le]
  have hUbound : U ≤ (1 + 3 * η) * μ ^ 2 * X := by
    dsimp [U]
    nlinarith [mul_le_mul_of_nonneg_right hmuAbsorb hX.le]
  have hcoef : (1 - 6 * η) * (1 + 3 * η) ≤ (1 - η) ^ 2 := by
    nlinarith [sq_nonneg η]
  have hnumeric : (1 - 6 * η) * X * U ≤ L ^ 2 := by
    have htarget : 0 ≤ 1 - 6 * η := by linarith
    calc
      (1 - 6 * η) * X * U ≤
          (1 - 6 * η) * X * ((1 + 3 * η) * μ ^ 2 * X) :=
        mul_le_mul_of_nonneg_left hUbound (mul_nonneg htarget hX.le)
      _ = ((1 - 6 * η) * (1 + 3 * η)) * μ ^ 2 * X ^ 2 := by ring
      _ ≤ (1 - η) ^ 2 * μ ^ 2 * X ^ 2 := by
        have hmuSq :
            ((1 - 6 * η) * (1 + 3 * η)) * μ ^ 2 ≤
              (1 - η) ^ 2 * μ ^ 2 :=
          mul_le_mul_of_nonneg_right hcoef (sq_nonneg μ)
        exact mul_le_mul_of_nonneg_right hmuSq (sq_nonneg X)
      _ = L ^ 2 := by dsimp [L]; ring
  have hmul : (1 - 6 * η) * X * U ≤
      ((S.filter fun i ↦ 0 < R i).card : ℝ) * U :=
    hnumeric.trans hpaley
  exact (mul_le_mul_iff_of_pos_right hU).mp hmul

end Erdos851
