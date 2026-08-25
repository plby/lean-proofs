import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# A cardinality bound for the Rankin mass of a finite prime set

The elements of the set need not be small: splitting at its cardinality
controls the sum of their negative powers by a function of that cardinality.
-/

namespace Pollack17

open scoped BigOperators

theorem sum_Icc_rpow_sub_one_le (K : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) :
    (∑ n ∈ Finset.Icc 1 K, (n : ℝ) ^ (δ - 1)) ≤
      (K : ℝ) ^ δ * (1 + Real.log (K : ℝ)) := by
  calc
    (∑ n ∈ Finset.Icc 1 K, (n : ℝ) ^ (δ - 1)) ≤
        ∑ n ∈ Finset.Icc 1 K, (K : ℝ) ^ δ * (n : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro n hn
      have hn0 : 0 < (n : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hn).1
      rw [Real.rpow_sub_one hn0.ne', div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow (Nat.cast_nonneg _)
          (by exact_mod_cast (Finset.mem_Icc.mp hn).2) hδ)
        (inv_nonneg.mpr hn0.le)
    _ = (K : ℝ) ^ δ * (harmonic K : ℝ) := by
      rw [harmonic_eq_sum_Icc]
      push_cast
      rw [Finset.mul_sum]
    _ ≤ (K : ℝ) ^ δ * (1 + Real.log (K : ℝ)) :=
      mul_le_mul_of_nonneg_left (harmonic_le_one_add_log K)
        (Real.rpow_nonneg (Nat.cast_nonneg _) _)

theorem sum_rpow_sub_one_le_card (S : Finset ℕ)
    (hS : ∀ n ∈ S, 0 < n) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    (∑ n ∈ S, (n : ℝ) ^ (δ - 1)) ≤
      (S.card : ℝ) ^ δ * (2 + Real.log (S.card : ℝ)) := by
  classical
  by_cases hK : S.card = 0
  · have hEmpty : S = ∅ := Finset.card_eq_zero.mp hK
    simp [hEmpty, Real.zero_rpow hδ0.ne']
  have hKpos : 0 < (S.card : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hK
  let T := S.filter fun n => n ≤ S.card
  let U := S.filter fun n => ¬ n ≤ S.card
  have hsmall : (∑ n ∈ T, (n : ℝ) ^ (δ - 1)) ≤
      (S.card : ℝ) ^ δ * (1 + Real.log (S.card : ℝ)) := by
    apply (Finset.sum_le_sum_of_subset_of_nonneg (s := T)
      (t := Finset.Icc 1 S.card) ?_ ?_).trans (sum_Icc_rpow_sub_one_le _ hδ0.le)
    · intro n hn
      have hn' := Finset.mem_filter.mp hn
      exact Finset.mem_Icc.mpr ⟨hS n hn'.1, hn'.2⟩
    · intro n _ _
      exact Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hlarge : (∑ n ∈ U, (n : ℝ) ^ (δ - 1)) ≤ (S.card : ℝ) ^ δ := by
    calc
      (∑ n ∈ U, (n : ℝ) ^ (δ - 1)) ≤
          ∑ _n ∈ U, (S.card : ℝ) ^ (δ - 1) := by
        apply Finset.sum_le_sum
        intro n hn
        have hKn : S.card ≤ n := by
          have := (Finset.mem_filter.mp hn).2
          omega
        exact Real.rpow_le_rpow_of_nonpos hKpos
          (by exact_mod_cast hKn) (sub_nonpos.mpr hδ1)
      _ = (U.card : ℝ) * (S.card : ℝ) ^ (δ - 1) := by simp
      _ ≤ (S.card : ℝ) * (S.card : ℝ) ^ (δ - 1) := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hKpos.le _)
        exact_mod_cast Finset.card_filter_le S (fun n => ¬ n ≤ S.card)
      _ = (S.card : ℝ) ^ δ := by
        rw [Real.rpow_sub_one hKpos.ne']
        field_simp
  calc
    (∑ n ∈ S, (n : ℝ) ^ (δ - 1)) =
        (∑ n ∈ T, (n : ℝ) ^ (δ - 1)) +
          ∑ n ∈ U, (n : ℝ) ^ (δ - 1) := by
      exact (Finset.sum_filter_add_sum_filter_not S
        (fun n => n ≤ S.card) (fun n => (n : ℝ) ^ (δ - 1))).symm
    _ ≤ (S.card : ℝ) ^ δ * (1 + Real.log (S.card : ℝ)) +
        (S.card : ℝ) ^ δ := add_le_add hsmall hlarge
    _ = (S.card : ℝ) ^ δ * (2 + Real.log (S.card : ℝ)) := by ring

end Pollack17
