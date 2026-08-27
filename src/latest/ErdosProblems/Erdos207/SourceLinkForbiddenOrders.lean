/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceLinkSampledForbiddenCount

/-! # Finite forbidden-order unions for sampled link degrees -/

namespace Erdos207

open Finset
open scoped Classical NNReal

noncomputable section

theorem sourceLinkForbiddenSamples_biUnion
    {J V : Type*} [DecidableEq J] [DecidableEq V]
    (orders : Finset J) (F : J → ForbiddenFamilyOn V) (I D Q : TripleSystemOn V) (e : Sym2 V) :
    sourceLinkForbiddenSamples (orders.biUnion F) I D Q e =
      orders.biUnion (fun j ↦ sourceLinkForbiddenSamples (F j) I D Q e) := by
  ext T
  simp only [sourceLinkForbiddenSamples, mem_filter, ParticipatesForbidden, mem_biUnion]
  aesop

theorem sourceLinkForbiddenSamples_biUnion_card_le
    {J V : Type*} [DecidableEq J] [DecidableEq V]
    (orders : Finset J) (F : J → ForbiddenFamilyOn V) (I D Q : TripleSystemOn V) (e : Sym2 V) :
    (sourceLinkForbiddenSamples (orders.biUnion F) I D Q e).card ≤
      ∑ j ∈ orders, (sourceLinkForbiddenSamples (F j) I D Q e).card := by
  rw [sourceLinkForbiddenSamples_biUnion]
  exact card_biUnion_le

theorem FiniteLaw.sourceLinkForbiddenOrders_probability_le
    {Ω J V : Type*} [Fintype Ω] [DecidableEq J] [DecidableEq V]
    (L : FiniteLaw Ω) (orders : Finset J) (F : J → ForbiddenFamilyOn V)
    (I D Q : Ω → TripleSystemOn V) (e : Sym2 V) (cutoff : J → ℕ) (error : J → ℝ≥0)
    (hbound : ∀ j ∈ orders, L.probability (fun ω ↦ cutoff j <
      (sourceLinkForbiddenSamples (F j) (I ω) (D ω) (Q ω) e).card) ≤ error j) :
    L.probability (fun ω ↦ (∑ j ∈ orders, cutoff j) <
      (sourceLinkForbiddenSamples (orders.biUnion F) (I ω) (D ω) (Q ω) e).card) ≤
        ∑ j ∈ orders, error j := by
  have hmono : L.probability (fun ω ↦ (∑ j ∈ orders, cutoff j) <
      (sourceLinkForbiddenSamples (orders.biUnion F) (I ω) (D ω) (Q ω) e).card) ≤
      L.probability (fun ω ↦ ∃ j ∈ orders, cutoff j <
        (sourceLinkForbiddenSamples (F j) (I ω) (D ω) (Q ω) e).card) := by
    apply L.probability_mono
    intro ω hbad
    by_contra hn
    have hupper : ∀ j ∈ orders, (sourceLinkForbiddenSamples (F j) (I ω) (D ω) (Q ω) e).card ≤ cutoff j := by
      intro j hj
      exact Nat.le_of_not_gt (fun hlarge ↦ hn ⟨j, hj, hlarge⟩)
    have hcard := (sourceLinkForbiddenSamples_biUnion_card_le orders F (I ω) (D ω) (Q ω) e).trans
      (sum_le_sum hupper)
    exact (Nat.not_lt_of_ge hcard) hbad
  exact (hmono.trans (L.probability_exists_le orders _)).trans (sum_le_sum hbound)

end

end Erdos207
