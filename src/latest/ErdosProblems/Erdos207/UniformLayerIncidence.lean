/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.FiveSetCorrection

/-! # Exact double counting between consecutive rooted clique layers -/

namespace Erdos207

open Finset

noncomputable section

theorem uniformLayer_incidence_sum
    {V : Type*} [DecidableEq V] (A B : Finset (Finset V)) (Q : Finset V) (k : ℕ)
    (hQ : Q.card ≤ k)
    (hA : ∀ S ∈ A, S.card = k ∧ Q ⊆ S)
    (hB : ∀ J ∈ B, J.card = k + 1 ∧ Q ⊆ J)
    (hfull : ∀ J ∈ B, ∀ S ⊆ J, S.card = k → Q ⊆ S → S ∈ A) :
    (∑ S ∈ A, (B.filter (S ⊆ ·)).card) = (k + 1 - Q.card) * B.card := by
  have hswap : (∑ S ∈ A, (B.filter (S ⊆ ·)).card) =
      ∑ J ∈ B, (A.filter (· ⊆ J)).card := by
    simp only [card_eq_sum_ones, sum_filter]
    rw [sum_comm]
  have hcount (J : Finset V) (hJB : J ∈ B) :
      (A.filter (· ⊆ J)).card = k + 1 - Q.card := by
    have heq : A.filter (· ⊆ J) = (J.powersetCard k).filter (Q ⊆ ·) := by
      ext S
      simp only [mem_filter, mem_powersetCard]
      constructor
      · exact fun h ↦ ⟨⟨h.2, (hA S h.1).1⟩, (hA S h.1).2⟩
      · exact fun h ↦ ⟨hfull J hJB S h.1.1 h.1.2 h.2, h.1.1⟩
    rw [heq, card_filter_powersetCard_subset Q J k (hB J hJB).2 hQ, (hB J hJB).1]
    have heq' : k + 1 - Q.card = (k - Q.card) + 1 := by omega
    rw [heq', Nat.choose_succ_self_right]
  rw [hswap]
  calc
    _ = ∑ _J ∈ B, (k + 1 - Q.card) := sum_congr rfl hcount
    _ = _ := by simp only [sum_const, nsmul_eq_mul]; exact Nat.mul_comm _ _

theorem uniformLayer_card_bounds
    {V : Type*} [DecidableEq V] (A B : Finset (Finset V)) (Q : Finset V) (k : ℕ)
    (hQ : Q.card ≤ k)
    (hA : ∀ S ∈ A, S.card = k ∧ Q ⊆ S)
    (hB : ∀ J ∈ B, J.card = k + 1 ∧ Q ⊆ J)
    (hfull : ∀ J ∈ B, ∀ S ⊆ J, S.card = k → Q ⊆ S → S ∈ A)
    (lo hi : ℝ)
    (hlo : ∀ S ∈ A, lo ≤ ((B.filter (S ⊆ ·)).card : ℝ))
    (hhi : ∀ S ∈ A, ((B.filter (S ⊆ ·)).card : ℝ) ≤ hi) :
    (A.card : ℝ) * lo ≤ (k + 1 - Q.card : ℕ) * (B.card : ℝ) ∧
      (k + 1 - Q.card : ℕ) * (B.card : ℝ) ≤ (A.card : ℝ) * hi := by
  have heq : (∑ S ∈ A, ((B.filter (S ⊆ ·)).card : ℝ)) =
      (k + 1 - Q.card : ℕ) * (B.card : ℝ) := by
    exact_mod_cast uniformLayer_incidence_sum A B Q k hQ hA hB hfull
  rw [← heq]
  constructor
  · simpa only [sum_const, nsmul_eq_mul] using sum_le_sum hlo
  · simpa only [sum_const, nsmul_eq_mul] using sum_le_sum hhi

end

end Erdos207
