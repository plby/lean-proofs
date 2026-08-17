import Mathlib

/-!
# Elementary probability on a finite uniform space

This file supplies the part of the first- and second-moment method which does
not require measure theory.  A probability space is represented by a finite,
nonempty type `Ω`; all points of `Ω` have the same weight.  In particular,
probabilities and expectations reduce definitionally to finite cardinalities
and finite sums.

The main estimate is `probability_zero_le_variance_div_expectation_sq`.  It is
the usual Chebyshev estimate at zero:

`P(X = 0) ≤ Var(X) / E[X]²`

whenever `E[X] > 0`.  The final two lemmas record the first- and second-moment
expansions for a count which is a finite sum of indicators.  The latter turns
the second moment into a sum of pairwise overlap probabilities.
-/

open scoped BigOperators

namespace Erdos807
namespace FiniteUniform

variable {Ω : Type*} [Fintype Ω]

/-- Probability of an event in the uniform probability space on `Ω`. -/
noncomputable def probability (P : Ω → Prop) : ℝ := by
  exact (Nat.card {ω // P ω} : ℝ) / Fintype.card Ω

/-- Expectation in the uniform probability space on `Ω`. -/
noncomputable def expectation (X : Ω → ℝ) : ℝ :=
  (∑ ω, X ω) / Fintype.card Ω

/-- The second moment `E[X²]` in the uniform probability space on `Ω`. -/
noncomputable def secondMoment (X : Ω → ℝ) : ℝ :=
  expectation fun ω ↦ X ω ^ 2

/-- Variance, defined directly as `E[(X - E[X])²]`. -/
noncomputable def variance (X : Ω → ℝ) : ℝ :=
  expectation fun ω ↦ (X ω - expectation X) ^ 2

/-- A real-valued indicator of a proposition. -/
noncomputable def indicator (P : Prop) : ℝ := by
  classical
  exact if P then 1 else 0

/-- Expectation of a natural-valued counting random variable. -/
noncomputable def natExpectation (X : Ω → ℕ) : ℝ :=
  expectation fun ω ↦ (X ω : ℝ)

/-- Second moment of a natural-valued counting random variable. -/
noncomputable def natSecondMoment (X : Ω → ℕ) : ℝ :=
  secondMoment fun ω ↦ (X ω : ℝ)

/-- Variance of a natural-valued counting random variable. -/
noncomputable def natVariance (X : Ω → ℕ) : ℝ :=
  variance fun ω ↦ (X ω : ℝ)

/-- A finite sum of indicators, viewed as a real-valued random variable. -/
noncomputable def indicatorCount {ι : Type*} (S : Finset ι)
    (P : ι → Ω → Prop) (ω : Ω) : ℝ :=
  ∑ i ∈ S, indicator (P i ω)

section Nonempty

variable [Nonempty Ω]

lemma card_pos : (0 : ℝ) < Fintype.card Ω := by
  exact_mod_cast Fintype.card_pos

lemma card_ne_zero : (Fintype.card Ω : ℝ) ≠ 0 :=
  ne_of_gt card_pos

/-- Probability is exactly event cardinality divided by sample-space
cardinality.  This theorem is useful for unfolding without exposing the
implementation choice in downstream proofs. -/
theorem probability_eq_card_div (P : Ω → Prop) [DecidablePred P] :
    probability P =
      ((Finset.univ.filter P).card : ℝ) / Fintype.card Ω := by
  classical
  unfold probability
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

/-- Expectation is exactly the finite sum divided by sample-space
cardinality. -/
theorem expectation_eq_sum_div (X : Ω → ℝ) :
    expectation X = (∑ ω, X ω) / Fintype.card Ω :=
  rfl

/-- Exact finite-sum formula for the expectation of a natural-valued count. -/
theorem natExpectation_eq_sum_div (X : Ω → ℕ) :
    natExpectation X = (∑ ω, (X ω : ℝ)) / Fintype.card Ω :=
  rfl

/-- Exact finite-sum formula for the second moment of a natural-valued count. -/
theorem natSecondMoment_eq_sum_div (X : Ω → ℕ) :
    natSecondMoment X = (∑ ω, (X ω : ℝ) ^ 2) / Fintype.card Ω :=
  rfl

theorem probability_nonneg (P : Ω → Prop) : 0 ≤ probability P := by
  classical
  exact div_nonneg (Nat.cast_nonneg _) card_pos.le

theorem probability_le_one (P : Ω → Prop) : probability P ≤ 1 := by
  classical
  rw [probability_eq_card_div]
  apply (div_le_one card_pos).2
  exact_mod_cast Finset.card_filter_le (s := Finset.univ) P

theorem probability_false : probability (fun _ : Ω ↦ False) = 0 := by
  classical
  simp [probability]

theorem probability_true : probability (fun _ : Ω ↦ True) = 1 := by
  classical
  simp [probability, card_ne_zero]

theorem expectation_const (c : ℝ) : expectation (fun _ : Ω ↦ c) = c := by
  simp [expectation, card_ne_zero]

theorem expectation_add (X Y : Ω → ℝ) :
    expectation (fun ω ↦ X ω + Y ω) = expectation X + expectation Y := by
  simp [expectation, Finset.sum_add_distrib, add_div]

theorem expectation_smul (c : ℝ) (X : Ω → ℝ) :
    expectation (fun ω ↦ c * X ω) = c * expectation X := by
  simp only [expectation, ← Finset.mul_sum]
  ring

/-- Expectation commutes with a finite sum. -/
theorem expectation_finset_sum {ι : Type*} (S : Finset ι) (X : ι → Ω → ℝ) :
    expectation (fun ω ↦ ∑ i ∈ S, X i ω) =
      ∑ i ∈ S, expectation (X i) := by
  classical
  simp only [expectation, Finset.sum_div]
  rw [Finset.sum_comm]

/-- Monotonicity of expectation on a finite uniform space. -/
theorem expectation_mono {X Y : Ω → ℝ} (h : ∀ ω, X ω ≤ Y ω) :
    expectation X ≤ expectation Y := by
  rw [expectation, expectation]
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun ω _ ↦ h ω) card_pos.le

/-- Monotonicity of event probability. -/
theorem probability_mono {P Q : Ω → Prop} (h : ∀ ω, P ω → Q ω) :
    probability P ≤ probability Q := by
  classical
  rw [probability_eq_card_div, probability_eq_card_div]
  exact div_le_div_of_nonneg_right (by
    exact_mod_cast Finset.card_le_card
      (Finset.monotone_filter_right Finset.univ fun ω _ ↦ h ω)) card_pos.le

/-- An event probability is the expectation of its indicator. -/
theorem expectation_indicator (P : Ω → Prop) :
    expectation (fun ω ↦ indicator (P ω)) = probability P := by
  classical
  rw [probability_eq_card_div]
  unfold expectation
  congr 1
  rw [Finset.card_eq_sum_ones, Nat.cast_sum]
  simp only [Nat.cast_one, Finset.sum_filter, indicator]

/-- The union bound for two events. -/
theorem probability_or_le (P Q : Ω → Prop) :
    probability (fun ω ↦ P ω ∨ Q ω) ≤ probability P + probability Q := by
  classical
  rw [← expectation_indicator, ← expectation_indicator, ← expectation_indicator,
    ← expectation_add]
  apply expectation_mono
  intro ω
  by_cases hP : P ω <;> by_cases hQ : Q ω <;> simp [indicator, hP, hQ]

/-- The finite union bound. -/
theorem probability_biUnion_le {ι : Type*} (S : Finset ι) (P : ι → Ω → Prop) :
    probability (fun ω ↦ ∃ i ∈ S, P i ω) ≤
      ∑ i ∈ S, probability (P i) := by
  classical
  rw [← expectation_indicator]
  calc
    expectation (fun ω ↦ indicator (∃ i ∈ S, P i ω))
        ≤ expectation (fun ω ↦ ∑ i ∈ S, indicator (P i ω)) := by
          apply expectation_mono
          intro ω
          by_cases h : ∃ i ∈ S, P i ω
          · obtain ⟨i, hiS, hiP⟩ := h
            have hex : ∃ j ∈ S, P j ω := ⟨i, hiS, hiP⟩
            rw [show indicator (∃ j ∈ S, P j ω) = 1 by
              simp [indicator, hex]]
            have hi : (1 : ℝ) ≤ ∑ j ∈ S, indicator (P j ω) := by
              calc
                (1 : ℝ) = indicator (P i ω) := by simp [indicator, hiP]
                _ ≤ ∑ j ∈ S, indicator (P j ω) :=
                  Finset.single_le_sum (s := S)
                    (f := fun j ↦ indicator (P j ω))
                    (fun j _ ↦ by unfold indicator; split <;> positivity) hiS
            exact hi
          · rw [show indicator (∃ i ∈ S, P i ω) = 0 by simp [indicator, h]]
            exact Finset.sum_nonneg fun i _ ↦ by
              unfold indicator
              split <;> positivity
    _ = ∑ i ∈ S, probability (P i) := by
      rw [expectation_finset_sum]
      apply Finset.sum_congr rfl
      intro i _
      exact expectation_indicator (P i)

/-- Markov's inequality on a finite uniform space. -/
theorem probability_le_expectation_div {X : Ω → ℝ} (hX : ∀ ω, 0 ≤ X ω)
    {a : ℝ} (ha : 0 < a) :
    probability (fun ω ↦ a ≤ X ω) ≤ expectation X / a := by
  classical
  let T := Finset.univ.filter fun ω ↦ a ≤ X ω
  have hT : a * (T.card : ℝ) ≤ ∑ ω ∈ T, X ω := by
    calc
      a * (T.card : ℝ) = ∑ ω ∈ T, a := by simp [mul_comm]
      _ ≤ ∑ ω ∈ T, X ω :=
        Finset.sum_le_sum fun ω hω ↦ (Finset.mem_filter.mp hω).2
  have hsub : ∑ ω ∈ T, X ω ≤ ∑ ω, X ω := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intro ω _ _
    exact hX ω
  have hcount : a * (T.card : ℝ) ≤ ∑ ω, X ω := hT.trans hsub
  rw [probability_eq_card_div, expectation, div_div]
  change (T.card : ℝ) / Fintype.card Ω ≤
    (∑ ω, X ω) / (Fintype.card Ω * a)
  rw [div_le_div_iff₀ card_pos (mul_pos card_pos ha)]
  nlinarith

/-- Markov's inequality for a natural-valued count, with a real threshold. -/
theorem probability_nat_cast_ge_le_expectation_div (X : Ω → ℕ) {a : ℝ}
    (ha : 0 < a) :
    probability (fun ω ↦ a ≤ (X ω : ℝ)) ≤ natExpectation X / a := by
  exact probability_le_expectation_div (X := fun ω ↦ (X ω : ℝ))
    (fun ω ↦ Nat.cast_nonneg (X ω)) ha

/-- The variance identity `Var(X) = E[X²] - E[X]²`. -/
theorem variance_eq_secondMoment_sub_expectation_sq (X : Ω → ℝ) :
    variance X = secondMoment X - expectation X ^ 2 := by
  rw [variance]
  calc
    expectation (fun ω ↦ (X ω - expectation X) ^ 2) =
        expectation (fun ω ↦
          X ω ^ 2 + ((-2 * expectation X) * X ω + expectation X ^ 2)) := by
      congr 1
      funext ω
      ring
    _ = expectation (fun ω ↦ X ω ^ 2) +
          (expectation (fun ω ↦ (-2 * expectation X) * X ω) +
            expectation (fun _ : Ω ↦ expectation X ^ 2)) := by
      rw [expectation_add, expectation_add]
    _ = secondMoment X +
          ((-2 * expectation X) * expectation X + expectation X ^ 2) := by
      rw [expectation_smul, expectation_const]
      rfl
    _ = secondMoment X - expectation X ^ 2 := by ring

/-- Variance identity specialized to a natural-valued counting random
variable. -/
theorem natVariance_eq_secondMoment_sub_expectation_sq (X : Ω → ℕ) :
    natVariance X = natSecondMoment X - natExpectation X ^ 2 := by
  simpa only [natVariance, natSecondMoment, natExpectation, secondMoment] using
    variance_eq_secondMoment_sub_expectation_sq (X := fun ω ↦ (X ω : ℝ))

theorem variance_nonneg (X : Ω → ℝ) : 0 ≤ variance X := by
  exact div_nonneg (Finset.sum_nonneg fun ω _ ↦ sq_nonneg _) card_pos.le

/-- Chebyshev's inequality specialized to the event that a random variable
vanishes.  Nonnegativity of `X` is not needed: positivity of its expectation
is the exact hypothesis used in this finite argument. -/
theorem probability_zero_le_variance_div_expectation_sq (X : Ω → ℝ)
    (hmean : 0 < expectation X) :
    probability (fun ω ↦ X ω = 0) ≤ variance X / expectation X ^ 2 := by
  calc
    probability (fun ω ↦ X ω = 0) ≤
        probability (fun ω ↦ expectation X ^ 2 ≤ (X ω - expectation X) ^ 2) := by
      apply probability_mono
      intro ω hω
      simpa [hω]
    _ ≤ expectation (fun ω ↦ (X ω - expectation X) ^ 2) /
          expectation X ^ 2 := by
      exact probability_le_expectation_div (fun ω ↦ sq_nonneg _)
        (sq_pos_of_pos hmean)
    _ = variance X / expectation X ^ 2 := rfl

/-- The zero-probability variance bound for a natural-valued count. -/
theorem probability_nat_zero_le_variance_div_expectation_sq (X : Ω → ℕ)
    (hmean : 0 < natExpectation X) :
    probability (fun ω ↦ X ω = 0) ≤
      natVariance X / natExpectation X ^ 2 := by
  simpa only [natExpectation, natVariance, Nat.cast_eq_zero] using
    probability_zero_le_variance_div_expectation_sq
      (X := fun ω ↦ (X ω : ℝ)) hmean

/-- Pointwise overlap expansion for the square of a sum of indicators. -/
theorem indicatorCount_sq {ι : Type*} (S : Finset ι) (P : ι → Ω → Prop)
    (ω : Ω) :
    indicatorCount S P ω ^ 2 =
      ∑ i ∈ S, ∑ j ∈ S, indicator (P i ω ∧ P j ω) := by
  classical
  simp only [indicatorCount, pow_two, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hPi : P i ω <;> by_cases hPj : P j ω <;>
    simp [indicator, hPi, hPj]

/-- First moment of a finite indicator count. -/
theorem expectation_indicatorCount {ι : Type*} (S : Finset ι)
    (P : ι → Ω → Prop) :
    expectation (indicatorCount S P) = ∑ i ∈ S, probability (P i) := by
  classical
  change expectation (fun ω ↦ ∑ i ∈ S, indicator (P i ω)) = _
  rw [expectation_finset_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact expectation_indicator (P i)

/-- Second moment of a finite indicator count, expanded into pairwise overlap
probabilities. -/
theorem secondMoment_indicatorCount {ι : Type*} (S : Finset ι)
    (P : ι → Ω → Prop) :
    secondMoment (indicatorCount S P) =
      ∑ i ∈ S, ∑ j ∈ S, probability (fun ω ↦ P i ω ∧ P j ω) := by
  classical
  rw [secondMoment]
  simp_rw [indicatorCount_sq S P]
  rw [expectation_finset_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [expectation_finset_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact expectation_indicator fun ω ↦ P i ω ∧ P j ω

end Nonempty

end FiniteUniform
end Erdos807
