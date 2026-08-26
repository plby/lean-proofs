import Mathlib
import ErdosProblems.Erdos550.TauFineAttachments

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Edge classification induced by a τ-fine separator

This module packages the exact trichotomy needed to reconstruct the original
tree from its seed skeleton and deleted components.  Every original edge is
either a seed--seed edge, an internal edge of one deleted component, or an
attachment edge recorded in that component's bounded seed set.
-/

open SimpleGraph Finset

namespace Erdos550

open Classical

variable {α : Type} [Fintype α] [DecidableEq α]

/-- The deleted-forest component containing a vertex. -/
noncomputable def seedComponent (T : SimpleGraph α) (S : Finset α) (v : α) :
    (seedDeleted T S).ConnectedComponent :=
  connectedComponentMk (seedDeleted T S) v

omit [Fintype α] [DecidableEq α] in
lemma mem_seedComponent_supp (T : SimpleGraph α) (S : Finset α) (v : α) :
    v ∈ (seedComponent T S v).supp := by
      -- By definition of `seedComponent`, the connected component of `v` in `seedDeleted T S` is the set of vertices reachable from `v` in `seedDeleted T S`.
      simp [seedComponent, SimpleGraph.ConnectedComponent.supp]

omit [Fintype α] [DecidableEq α] in
lemma seedComponent_eq_of_seedDeleted_adj (T : SimpleGraph α) (S : Finset α)
    {a b : α} (hab : (seedDeleted T S).Adj a b) :
    seedComponent T S a = seedComponent T S b := by
      convert! Quot.sound ?_;
      exact SimpleGraph.Adj.reachable hab

omit [Fintype α] [DecidableEq α] in
lemma seedComponent_eq_of_adj_of_nonseed (T : SimpleGraph α) (S : Finset α)
    {a b : α} (hab : T.Adj a b) (ha : a ∉ S) (hb : b ∉ S) :
    seedComponent T S a = seedComponent T S b := by
      apply seedComponent_eq_of_seedDeleted_adj;
      exact ⟨ hab, by aesop ⟩

lemma left_seed_recorded_of_adj (T : SimpleGraph α) (S : Finset α)
    {s x : α} (hs : s ∈ S) (hadj : T.Adj s x) :
    s ∈ componentSeeds T S (seedComponent T S x) := by
      -- Apply the lemma seed_mem_componentSeeds_of_adj with x. Its component support membership is mem_seedComponent_supp.
      apply seed_mem_componentSeeds_of_adj T S (seedComponent T S x) hs (mem_seedComponent_supp T S x) hadj

lemma right_seed_recorded_of_adj (T : SimpleGraph α) (S : Finset α)
    {x s : α} (hs : s ∈ S) (hadj : T.Adj x s) :
    s ∈ componentSeeds T S (seedComponent T S x) := by
      convert! left_seed_recorded_of_adj T S hs hadj.symm using 1

/-
Exact edge trichotomy for the seed/component decomposition.
-/
theorem tauFine_edge_classification (T : SimpleGraph α) (S : Finset α)
    {a b : α} (hab : T.Adj a b) :
    (a ∈ S ∧ b ∈ S) ∨
    (a ∉ S ∧ b ∉ S ∧ seedComponent T S a = seedComponent T S b) ∨
    (a ∈ S ∧ b ∉ S ∧
      a ∈ componentSeeds T S (seedComponent T S b)) ∨
    (a ∉ S ∧ b ∈ S ∧
      b ∈ componentSeeds T S (seedComponent T S a)) := by
        grind +suggestions

/-
The attachment set belonging to the component of a nonseed vertex inherits
the global separator-cardinality bound.
-/
lemma seedComponent_attachments_card_le (T : SimpleGraph α) (S : Finset α)
    (v : α) :
    (componentSeeds T S (seedComponent T S v)).card ≤ S.card := by
      exact Finset.card_le_card ( componentSeeds_subset _ _ _ )

/-
τ-fine specialization of the preceding attachment bound.
-/
lemma seedComponent_attachments_card_le_floor_inv
    (T : SimpleGraph α) (S : Finset α) (τ : ℝ)
    (hS : (S.card : ℝ) ≤ 1 / τ) (v : α) :
    (componentSeeds T S (seedComponent T S v)).card ≤ Nat.floor (1 / τ) := by
      convert! componentSeeds_card_le_floor_inv T S τ hS ( seedComponent T S v ) using 1

end Erdos550
