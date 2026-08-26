import Mathlib.Tactic

/-!
# Finite averaging for the matched-prefix potential

The argument uses finite sums, not a probability-space construction. If every
index has a positive proportion of choices that halve its contribution, one
choice contracts the total weighted potential by the corresponding factor.
-/

namespace Erdos547

open Finset
open scoped BigOperators

variable {I C : Type*}

open scoped Classical in
/-- A simultaneous halving event for a positive proportion of the choices at
every index gives a deterministic contraction of the total weight. -/
theorem exists_choice_weight_contraction (indices : Finset I) (choices : Finset C)
    (hchoices : choices.Nonempty) (weight : I → ℝ)
    (hweight : ∀ i ∈ indices, 0 ≤ weight i) (good : I → C → Prop) (p : ℝ)
    (hproportion : ∀ i ∈ indices, p * choices.card ≤ (choices.filter (good i)).card) :
    ∃ c ∈ choices, (∑ i ∈ indices, if good i c then weight i / 2 else weight i) ≤
      (1 - p / 2) * ∑ i ∈ indices, weight i := by
  classical
  have hrow (i : I) (hi : i ∈ indices) :
      (∑ c ∈ choices, if good i c then weight i / 2 else weight i) ≤
        (choices.card : ℝ) * ((1 - p / 2) * weight i) := by
    have heq : (∑ c ∈ choices, if good i c then weight i / 2 else weight i) =
        (choices.card : ℝ) * weight i - (choices.filter (good i)).card * (weight i / 2) := by
      calc
        _ = ∑ c ∈ choices, (weight i - if good i c then weight i / 2 else 0) := by
          apply Finset.sum_congr rfl
          intro c _
          split_ifs <;> ring
        _ = _ := by
          rw [Finset.sum_sub_distrib, ← Finset.sum_filter]
          simp
    rw [heq]
    have hprod := mul_le_mul_of_nonneg_right (hproportion i hi)
      (div_nonneg (hweight i hi) (by norm_num : (0 : ℝ) ≤ 2))
    nlinarith only [hprod]
  have hsum : (∑ c ∈ choices, ∑ i ∈ indices,
      if good i c then weight i / 2 else weight i) ≤
        ∑ _c ∈ choices, (1 - p / 2) * ∑ i ∈ indices, weight i := by
    rw [Finset.sum_comm]
    calc
      _ ≤ ∑ i ∈ indices, (choices.card : ℝ) * ((1 - p / 2) * weight i) :=
        Finset.sum_le_sum hrow
      _ = _ := by
        simp only [← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
        ring
  exact Finset.exists_le_of_sum_le hchoices hsum

/-- The potential associated to nonnegative integer exposure counts. -/
noncomputable def exposurePotential (indices : Finset I) (count : I → ℕ) : ℝ :=
  ∑ i ∈ indices, (1 / 2 : ℝ) ^ count i

theorem exposurePotential_nonneg (indices : Finset I) (count : I → ℕ) :
    0 ≤ exposurePotential indices count := by
  apply Finset.sum_nonneg
  intro i _
  positivity

theorem exposurePotential_le_card (indices : Finset I) (count : I → ℕ) :
    exposurePotential indices count ≤ indices.card := by
  calc
    _ ≤ ∑ _i ∈ indices, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      exact pow_le_one₀ (by norm_num) (by norm_num)
    _ = _ := by simp

open scoped Classical in
/-- A choice that increases each exposure count, and increases it strictly
on a proportion `p` of choices for each index, contracts the potential. -/
theorem exists_choice_exposure_contraction (indices : Finset I) (choices : Finset C)
    (hchoices : choices.Nonempty) (count : I → ℕ) (next : C → I → ℕ)
    (good : I → C → Prop) (p : ℝ)
    (hproportion : ∀ i ∈ indices, p * choices.card ≤ (choices.filter (good i)).card)
    (hmono : ∀ c ∈ choices, ∀ i ∈ indices, count i ≤ next c i)
    (hincrease : ∀ c ∈ choices, ∀ i ∈ indices, good i c → count i + 1 ≤ next c i) :
    ∃ c ∈ choices, exposurePotential indices (next c) ≤
      (1 - p / 2) * exposurePotential indices count := by
  classical
  obtain ⟨c, hc, hbound⟩ := exists_choice_weight_contraction indices choices hchoices
    (fun i ↦ (1 / 2 : ℝ) ^ count i) (fun _ _ ↦ by positivity) good p hproportion
  refine ⟨c, hc, le_trans ?_ hbound⟩
  apply Finset.sum_le_sum
  intro i hi
  by_cases hgood : good i c
  · rw [if_pos hgood]
    calc
      (1 / 2 : ℝ) ^ next c i ≤ (1 / 2 : ℝ) ^ (count i + 1) :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) (hincrease c hc i hi hgood)
      _ = _ := by rw [pow_succ]; ring
  · rw [if_neg hgood]
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (hmono c hc i hi)

end Erdos547

#print axioms Erdos547.exists_choice_exposure_contraction
