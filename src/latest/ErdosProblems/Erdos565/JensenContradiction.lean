import ErdosProblems.Erdos565.FiniteAnalysis
import Mathlib.Tactic

/-!
# The final finite Jensen contradiction

This file isolates the last purely analytic step in the proof of the
specialised container theorem.  A finite probability distribution cannot
simultaneously have small expected Janson energy, large squared expected
mass, and the pointwise inequality forced by failure of Jansonness.

The second part records the numerical square-root estimate used immediately
before that contradiction.  Keeping these facts separate from the
hypergraph definitions makes explicit that this stage uses only finite sums
and elementary real algebra.
-/

open scoped BigOperators

namespace Erdos565
namespace JensenContradiction

/-- Jensen's inequality and a pointwise energy lower bound force the same
lower bound after taking a finite expectation. -/
theorem sq_expectation_le_denominator_mul_expectation
    {Ω : Type*} (outcomes : Finset Ω) (prob mass energy : Ω → ℝ)
    {denominator : ℝ}
    (hprob : ∀ ω ∈ outcomes, 0 ≤ prob ω)
    (hprob_sum : ∑ ω ∈ outcomes, prob ω = 1)
    (hdenominator : 0 < denominator)
    (hpointwise : ∀ ω ∈ outcomes,
      mass ω ^ 2 / denominator ≤ energy ω) :
    (∑ ω ∈ outcomes, prob ω * mass ω) ^ 2 ≤
      denominator * ∑ ω ∈ outcomes, prob ω * energy ω := by
  have hjensen :
      (∑ ω ∈ outcomes, prob ω * mass ω) ^ 2 ≤
        ∑ ω ∈ outcomes, prob ω * mass ω ^ 2 :=
    FiniteAnalysis.sq_weighted_sum_le_of_sum_eq_one
      outcomes prob mass hprob hprob_sum
  calc
    (∑ ω ∈ outcomes, prob ω * mass ω) ^ 2
        ≤ ∑ ω ∈ outcomes, prob ω * mass ω ^ 2 := hjensen
    _ ≤ ∑ ω ∈ outcomes, prob ω * (denominator * energy ω) := by
      apply Finset.sum_le_sum
      intro ω hω
      exact mul_le_mul_of_nonneg_left
        (by simpa [mul_comm] using
          ((div_le_iff₀ hdenominator).mp (hpointwise ω hω))) (hprob ω hω)
    _ = denominator * ∑ ω ∈ outcomes, prob ω * energy ω := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ω hω
      ring

/-- The exact contradiction used at the end of the specialised container
argument.  The strict inequalities are deliberately stated in the same
orientation as the paper: the expected energy is less than `1 + 4 * γ`,
whereas the square of the expected mass is larger than
`(1 + 4 * γ) * denominator`. -/
theorem expectation_contradiction
    {Ω : Type*} (outcomes : Finset Ω) (prob mass energy : Ω → ℝ)
    {γ denominator : ℝ}
    (hprob : ∀ ω ∈ outcomes, 0 ≤ prob ω)
    (hprob_sum : ∑ ω ∈ outcomes, prob ω = 1)
    (hdenominator : 0 < denominator)
    (hpointwise : ∀ ω ∈ outcomes,
      mass ω ^ 2 / denominator ≤ energy ω)
    (henergy : (∑ ω ∈ outcomes, prob ω * energy ω) < 1 + 4 * γ)
    (hmass : (1 + 4 * γ) * denominator <
      (∑ ω ∈ outcomes, prob ω * mass ω) ^ 2) : False := by
  have hupper := sq_expectation_le_denominator_mul_expectation
    outcomes prob mass energy hprob hprob_sum hdenominator hpointwise
  have hstrict :
      denominator * (∑ ω ∈ outcomes, prob ω * energy ω) <
        denominator * (1 + 4 * γ) :=
    mul_lt_mul_of_pos_left henergy hdenominator
  have :
      (∑ ω ∈ outcomes, prob ω * mass ω) ^ 2 <
        (1 + 4 * γ) * denominator := by
    calc
      (∑ ω ∈ outcomes, prob ω * mass ω) ^ 2
          ≤ denominator * ∑ ω ∈ outcomes, prob ω * energy ω := hupper
      _ < denominator * (1 + 4 * γ) := hstrict
      _ = (1 + 4 * γ) * denominator := mul_comm _ _
  exact (not_lt_of_ge hmass.le) this

/-- A square-root consequence of `16 * R' ≤ R`. -/
lemma four_mul_sqrt_le_sqrt
    {R R' : ℝ} (hRR' : 16 * R' ≤ R) :
    4 * Real.sqrt R' ≤ Real.sqrt R := by
  calc
    4 * Real.sqrt R' = Real.sqrt (16 * R') := by
      rw [Real.sqrt_mul (by norm_num : 0 ≤ (16 : ℝ))]
      norm_num
    _ ≤ Real.sqrt R := Real.sqrt_le_sqrt hRR'

/-- The strict numerical estimate used for the expected mass.  In the
application, `γ = sqrt (8 * η)`, so `γ² = 8η`; the statement uses the latter
identity because it is the exact algebraic fact needed by the proof. -/
theorem sqrt_mass_square_gt
    {R R' η γ : ℝ}
    (hR : 0 < R) (hR' : 0 ≤ R') (hRR' : 16 * R' ≤ R)
    (hγ : 0 < γ) (hγlt : γ < 1 / 4)
    (hγη : γ ^ 2 = 8 * η) :
    (1 + 4 * γ) * (R' + η * R) <
      (Real.sqrt R' + γ * Real.sqrt R / 2) ^ 2 := by
  have hsqrtR' : 0 ≤ Real.sqrt R' := Real.sqrt_nonneg _
  have hsqrtR_sq : Real.sqrt R ^ 2 = R := Real.sq_sqrt hR.le
  have hsqrtR'_sq : Real.sqrt R' ^ 2 = R' := Real.sq_sqrt hR'
  have hsqrt_dom : 4 * Real.sqrt R' ≤ Real.sqrt R :=
    four_mul_sqrt_le_sqrt hRR'
  have hcross : 4 * R' ≤ Real.sqrt R' * Real.sqrt R := by
    calc
      4 * R' = Real.sqrt R' * (4 * Real.sqrt R') := by
        nlinarith
      _ ≤ Real.sqrt R' * Real.sqrt R :=
        mul_le_mul_of_nonneg_left hsqrt_dom hsqrtR'
  have hη : η = γ ^ 2 / 8 := by nlinarith
  have hpositive : 0 < γ ^ 2 * R * (1 / 8 - γ / 2) := by
    have hγsq : 0 < γ ^ 2 := sq_pos_of_pos hγ
    have hfactor : 0 < 1 / 8 - γ / 2 := by linarith
    positivity
  have hcross_nonneg :
      0 ≤ γ * (Real.sqrt R' * Real.sqrt R - 4 * R') :=
    mul_nonneg hγ.le (sub_nonneg.mpr hcross)
  have hidentity :
      (Real.sqrt R' + γ * Real.sqrt R / 2) ^ 2 -
          (1 + 4 * γ) * (R' + η * R) =
        γ * (Real.sqrt R' * Real.sqrt R - 4 * R') +
          γ ^ 2 * R * (1 / 8 - γ / 2) := by
    rw [hη]
    nlinarith
  rw [← sub_pos]
  rw [hidentity]
  exact add_pos_of_nonneg_of_pos hcross_nonneg hpositive

end JensenContradiction
end Erdos565
