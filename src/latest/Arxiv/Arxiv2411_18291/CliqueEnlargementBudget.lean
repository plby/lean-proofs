import Arxiv.Arxiv2411_18291.CliqueFamilyLowerDegrees

/-! # The common expectation budget for shared decoder regions -/

open Finset
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291

variable {I V : Type*} [Fintype I] [Fintype V] [DecidableEq V] {q r d : ℕ}

theorem sum_enlargement_face_budget (E : I → Block V q) (hrq : r ≤ q)
    {b : ℝ} (hb : 0 ≤ b) (hn : 0 < Fintype.card V)
    (hE : ∀ T : Block V r, (familyDegree E T.val : ℝ) ≤ b * Fintype.card V)
    (S : Block V r) :
    (∑ i, 2 * d.factorial / (Fintype.card V : ℝ) ^ (S.val \ (E i).val).card) ≤
      2 ^ (r + 1) * d.factorial * b * Fintype.card V := by
  classical
  have hN : (0 : ℝ) < Fintype.card V := by exact_mod_cast hn
  have hterm (i : I) :
      2 * d.factorial / (Fintype.card V : ℝ) ^ (S.val \ (E i).val).card ≤
        ∑ T ∈ S.val.powerset,
          if T ⊆ (E i).val then 2 * d.factorial / (Fintype.card V : ℝ) ^ (r - T.card)
          else 0 := by
    have hmem : S.val ∩ (E i).val ∈ S.val.powerset := mem_powerset.mpr inter_subset_left
    have hj : (S.val \ (E i).val).card = r - (S.val ∩ (E i).val).card := by
      have h := card_sdiff_add_card_inter S.val (E i).val
      rw [S.property] at h
      omega
    have hnonneg : ∀ T ∈ S.val.powerset,
        (0 : ℝ) ≤ if T ⊆ (E i).val then
          2 * d.factorial / (Fintype.card V : ℝ) ^ (r - T.card) else 0 := by
      intro T _
      split_ifs
      · positivity
      · exact le_rfl
    calc
      _ = if S.val ∩ (E i).val ⊆ (E i).val then
          2 * d.factorial / (Fintype.card V : ℝ) ^ (r - (S.val ∩ (E i).val).card)
          else 0 := by rw [if_pos inter_subset_right, hj]
      _ ≤ _ := single_le_sum hnonneg hmem
  have hdeg (T : Finset V) :
      (∑ i, if T ⊆ (E i).val then
        2 * d.factorial / (Fintype.card V : ℝ) ^ (r - T.card) else 0) =
        (2 * d.factorial / (Fintype.card V : ℝ) ^ (r - T.card)) * familyDegree E T := by
    simp only [familyDegree, ← sum_filter, sum_const, nsmul_eq_mul]
    ring
  calc
    _ ≤ ∑ i, ∑ T ∈ S.val.powerset,
        if T ⊆ (E i).val then 2 * d.factorial / (Fintype.card V : ℝ) ^ (r - T.card)
        else 0 := sum_le_sum fun i _ => hterm i
    _ = ∑ T ∈ S.val.powerset,
        (2 * d.factorial / (Fintype.card V : ℝ) ^ (r - T.card)) * familyDegree E T := by
      rw [sum_comm]
      exact sum_congr rfl fun T _ => hdeg T
    _ ≤ ∑ _T ∈ S.val.powerset, 2 * d.factorial * b * Fintype.card V := by
      apply sum_le_sum
      intro T hT
      have hTr : T.card ≤ r := (card_le_card (mem_powerset.mp hT)).trans S.property.le
      calc
        _ ≤ (2 * d.factorial / (Fintype.card V : ℝ) ^ (r - T.card)) *
            (b * (Fintype.card V : ℝ) ^ (r + 1 - T.card)) :=
          mul_le_mul_of_nonneg_left (familyDegree_le_of_face_bound E hrq hb hE T hTr)
            (by positivity)
        _ = _ := by
          rw [show r + 1 - T.card = (r - T.card) + 1 by omega, pow_succ]
          field_simp
    _ = _ := by
      simp only [sum_const, card_powerset, S.property, nsmul_eq_mul, Nat.cast_pow,
        Nat.cast_ofNat, pow_succ]
      ring

end Arxiv2411_18291
