/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.TwoSidedRandomRobustMatching
import ErdosProblems.Erdos207.FiniteSpanCounting

/-! # Size-sensitive counting of the actual small Hall obstructions -/

namespace Erdos207

open Finset
open scoped Classical NNReal

noncomputable section

theorem smallHall_size_pos
    {A B : Type*} [Fintype A] [DecidableEq A] [DecidableEq B]
    (o : SmallHallObstruction A B) : 0 < o.1.1.1.card := by
  have h := o.1.2
  omega

theorem smallHall_fixedSize_card_le
    {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] (s : ℕ) :
    (univ.filter (fun o : SmallHallObstruction A B ↦ o.1.1.1.card = s)).card ≤
      (2 * (Fintype.card A + 1) * (Fintype.card B + 1)) ^ s := by
  have hinject : (univ.filter (fun o : SmallHallObstruction A B ↦ o.1.1.1.card = s)).card ≤
      (((univ : Finset A).powersetCard s) ×ˢ (subsetsUpToCard (univ : Finset B) s)).card := by
    apply card_le_card_of_injOn (f := fun o : SmallHallObstruction A B ↦ o.1.1)
    · intro o ho
      have hs := (mem_filter.mp ho).2
      apply mem_product.mpr
      refine ⟨mem_powersetCard.mpr ⟨subset_univ _, hs⟩,
        mem_subsetsUpToCard_iff.mpr ⟨subset_univ _, ?_⟩⟩
      have hlt := o.1.2
      change o.1.1.2.card ≤ s
      omega
    · intro o _ p _ heq
      exact Subtype.ext (Subtype.ext heq)
  apply hinject.trans
  rw [card_product, card_powersetCard, card_univ]
  calc
    _ ≤ (Fintype.card A + 1) ^ s * ((s + 1) * (Fintype.card B + 1) ^ s) := by
      apply Nat.mul_le_mul
      · exact (Nat.choose_le_pow _ _).trans (pow_le_pow_left' (Nat.le_succ _) _)
      · simpa only [card_univ] using card_subsetsUpToCard_le (univ : Finset B) s
    _ ≤ (Fintype.card A + 1) ^ s * (2 ^ s * (Fintype.card B + 1) ^ s) := by
      gcongr
      exact Nat.succ_le_of_lt s.lt_two_pow_self
    _ = _ := by simp only [mul_pow]; ring

theorem smallHall_weighted_sum_le
    {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] (theta : ℝ≥0) :
    (∑ o : SmallHallObstruction A B, theta ^ o.1.1.1.card) ≤
      ∑ s ∈ Icc 1 (Fintype.card A),
        ((2 * (Fintype.card A + 1) * (Fintype.card B + 1) : ℕ) * theta : ℝ≥0) ^ s := by
  let size := fun o : SmallHallObstruction A B ↦ o.1.1.1.card
  have hmap : ∀ o ∈ (univ : Finset (SmallHallObstruction A B)), size o ∈ Icc 1 (Fintype.card A) := by
    intro o _
    exact mem_Icc.mpr ⟨smallHall_size_pos o, o.1.1.1.card_le_univ⟩
  calc
    _ = ∑ s ∈ Icc 1 (Fintype.card A), ∑ o ∈ univ with size o = s, theta ^ size o :=
      (sum_fiberwise_of_maps_to hmap (fun o ↦ theta ^ size o)).symm
    _ ≤ ∑ s ∈ Icc 1 (Fintype.card A),
        ((2 * (Fintype.card A + 1) * (Fintype.card B + 1) : ℕ) * theta : ℝ≥0) ^ s := by
      apply sum_le_sum
      intro s _
      calc
        _ = ((univ.filter (fun o : SmallHallObstruction A B ↦ size o = s)).card : ℝ≥0) * theta ^ s := by
          calc
            _ = ∑ _o ∈ univ with size _o = s, theta ^ s := by
              apply sum_congr rfl
              intro o ho
              rw [(mem_filter.mp ho).2]
            _ = _ := by simp only [sum_const, nsmul_eq_mul]
        _ ≤ (((2 * (Fintype.card A + 1) * (Fintype.card B + 1)) ^ s : ℕ) : ℝ≥0) * theta ^ s := by
          apply mul_le_mul_of_nonneg_right _ zero_le
          exact_mod_cast smallHall_fixedSize_card_le (A := A) (B := B) s
        _ = _ := by rw [Nat.cast_pow, mul_pow]

theorem orientedSmallHall_weighted_sum_le
    {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (hcard : Fintype.card A = Fintype.card B) (theta : ℝ≥0) :
    (∑ o : OrientedSmallHallObstruction A B, theta ^ orientedSmallHallSize o) ≤
      2 * ∑ s ∈ Icc 1 (Fintype.card A),
        ((2 * (Fintype.card A + 1) * (Fintype.card B + 1) : ℕ) * theta : ℝ≥0) ^ s := by
  rw [Fintype.sum_sum_type]
  have hl := smallHall_weighted_sum_le (A := A) (B := B) theta
  have hr := smallHall_weighted_sum_le (A := B) (B := A) theta
  have heq : 2 * (Fintype.card B + 1) * (Fintype.card A + 1) =
      2 * (Fintype.card A + 1) * (Fintype.card B + 1) := by ring
  have hsum : (∑ s ∈ Icc 1 (Fintype.card B),
      ((2 * (Fintype.card B + 1) * (Fintype.card A + 1) : ℕ) * theta : ℝ≥0) ^ s) =
      ∑ s ∈ Icc 1 (Fintype.card A),
        ((2 * (Fintype.card A + 1) * (Fintype.card B + 1) : ℕ) * theta : ℝ≥0) ^ s := by
    rw [heq, hcard]
  rw [hsum] at hr
  simpa only [orientedSmallHallSize, two_mul] using add_le_add hl hr

end

end Erdos207
