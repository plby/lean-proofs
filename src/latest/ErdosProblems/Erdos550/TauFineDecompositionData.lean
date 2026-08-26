import Mathlib
import ErdosProblems.Erdos550.TauFineEdgeClassification

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Complete combinatorial data of a τ-fine decomposition

This file bundles the separator size, component size, attachment size, and source
edge classification into one theorem shaped for the final regularity
instantiation.  It also gives vertex-indexed forms of the component and
attachment estimates, avoiding quotient bookkeeping downstream.
-/

open SimpleGraph Finset

namespace Erdos550

open Classical

variable {α : Type} [Fintype α] [DecidableEq α]

omit [Fintype α] [DecidableEq α] in
lemma seedComponent_card_le_of_all_components
    (T : SimpleGraph α) (S : Finset α) (B : ℝ)
    (hcomp : ∀ c : (seedDeleted T S).ConnectedComponent,
      (Nat.card c.supp : ℝ) ≤ B) (v : α) :
    (Nat.card (seedComponent T S v).supp : ℝ) ≤ B := by
      exact hcomp _

lemma seedComponent_attachment_bound_of_all_components
    (T : SimpleGraph α) (S : Finset α) (r : ℕ)
    (hatt : ∀ c : (seedDeleted T S).ConnectedComponent,
      (componentSeeds T S c).card ≤ r) (v : α) :
    (componentSeeds T S (seedComponent T S v)).card ≤ r := by
      exact hatt _

/-
**Fully bundled τ-fine decomposition interface.**  The chosen seed set is
small; every deleted component is small and has a bounded seed-attachment set;
and every original tree edge has the exact seed/internal/attachment
classification needed for gluing an embedding.
-/
theorem tree_tau_fine_decomposition_data
    (T : SimpleGraph α) [DecidableRel T.Adj] (hT : T.IsTree)
    (τ : ℝ) (hτ : 0 < τ)
    (hn : (1 : ℝ) ≤ τ * Fintype.card α) :
    ∃ S : Finset α,
      (S.card : ℝ) ≤ 1 / τ ∧
      (∀ c : (seedDeleted T S).ConnectedComponent,
        (Nat.card c.supp : ℝ) ≤ τ * Fintype.card α) ∧
      (∀ c : (seedDeleted T S).ConnectedComponent,
        (componentSeeds T S c).card ≤ Nat.floor (1 / τ)) ∧
      (∀ ⦃a b : α⦄, T.Adj a b →
        (a ∈ S ∧ b ∈ S) ∨
        (a ∉ S ∧ b ∉ S ∧ seedComponent T S a = seedComponent T S b) ∨
        (a ∈ S ∧ b ∉ S ∧
          a ∈ componentSeeds T S (seedComponent T S b)) ∨
        (a ∉ S ∧ b ∈ S ∧
          b ∈ componentSeeds T S (seedComponent T S a))) := by
            obtain ⟨ S, hS₁, hS₂, hS₃ ⟩ := tree_tau_fine_with_attachments T hT τ hτ hn;
            refine' ⟨ S, hS₁, hS₂, hS₃, _ ⟩;
            intro a b hab; have := tauFine_edge_classification T S hab; aesop;

/-
Vertex-indexed form of the bundled decomposition, convenient when shrub
vertices carry their component as `seedComponent T S v`.
-/
theorem tree_tau_fine_vertex_data
    (T : SimpleGraph α) [DecidableRel T.Adj] (hT : T.IsTree)
    (τ : ℝ) (hτ : 0 < τ)
    (hn : (1 : ℝ) ≤ τ * Fintype.card α) :
    ∃ S : Finset α,
      (S.card : ℝ) ≤ 1 / τ ∧
      (∀ v : α,
        (Nat.card (seedComponent T S v).supp : ℝ)
          ≤ τ * Fintype.card α) ∧
      (∀ v : α,
        (componentSeeds T S (seedComponent T S v)).card
          ≤ Nat.floor (1 / τ)) ∧
      (∀ ⦃a b : α⦄, T.Adj a b →
        (a ∈ S ∧ b ∈ S) ∨
        (a ∉ S ∧ b ∉ S ∧ seedComponent T S a = seedComponent T S b) ∨
        (a ∈ S ∧ b ∉ S ∧
          a ∈ componentSeeds T S (seedComponent T S b)) ∨
        (a ∉ S ∧ b ∈ S ∧
          b ∈ componentSeeds T S (seedComponent T S a))) := by
            obtain ⟨ S, hS₁, hS₂, hS₃, hS₄ ⟩ := tree_tau_fine_decomposition_data T hT τ hτ hn;
            exact ⟨ S, hS₁, fun v => hS₂ _, fun v => hS₃ _, hS₄ ⟩

end Erdos550
