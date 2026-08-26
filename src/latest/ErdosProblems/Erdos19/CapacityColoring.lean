import ErdosProblems.Erdos76.HypergraphGreedyColoring
import Mathlib.Tactic

/-! # Capacity constraints enforced by augmented supports -/

namespace Erdos19

open Finset Erdos76 Erdos76.FiniteHypergraph

variable {V E A : Type*} [DecidableEq V] [Fintype E] [DecidableEq E]
  [DecidableEq A]

/-- Intersections of the supports of a matching consume at most the pool. -/
theorem matching_sum_inter_card_le (K : FiniteHypergraph V E) (S : Finset E)
    (hS : K.IsMatching S) (P : Finset V) :
    (∑ e ∈ S, (K.support e ∩ P).card) ≤ P.card := by
  classical
  have hdisjoint : (S : Set E).PairwiseDisjoint (fun e ↦ K.support e ∩ P) := by
    intro e he f hf hef
    exact (hS he hf hef).mono inter_subset_left inter_subset_left
  rw [← card_biUnion hdisjoint]
  apply card_le_card
  intro x hx
  obtain ⟨e, _, he⟩ := mem_biUnion.mp hx
  exact (mem_inter.mp he).2

theorem coloring_fiber_isMatching (K : FiniteHypergraph V E)
    (c : K.conflictGraph.Coloring A) (a : A) :
    K.IsMatching (univ.filter fun e ↦ c e = a) := by
  classical
  intro e he f hf hef
  by_contra hdisjoint
  exact c.valid ⟨hef, hdisjoint⟩ ((mem_filter.mp he).2.trans (mem_filter.mp hf).2.symm)

/-- A proper coloring of augmented supports is proper on the original
supports and does not change any color labels. -/
def coloringOfSupportExtension (H K : FiniteHypergraph V E)
    (hsub : ∀ e, H.support e ⊆ K.support e) (c : K.conflictGraph.Coloring A) :
    H.conflictGraph.Coloring A :=
  SimpleGraph.Coloring.mk c (by
    intro e f hef hsame
    apply c.valid ⟨hef.1, ?_⟩ hsame
    intro hdisjoint
    exact hef.2 (hdisjoint.mono (hsub e) (hsub f)))

/-- If each augmented edge consumes at least as many pool vertices as it
covers buffer vertices, each color covers at most the pool size in the buffer. -/
theorem coloring_covered_buffer_le_pool (H K : FiniteHypergraph V E)
    (B P : Finset V) (hdemand : ∀ e, (H.support e ∩ B).card ≤ (K.support e ∩ P).card)
    (c : K.conflictGraph.Coloring A) (a : A) :
    ((univ.filter fun e ↦ c e = a).biUnion fun e ↦ H.support e ∩ B).card ≤ P.card := by
  classical
  calc
    _ ≤ ∑ e ∈ univ.filter (fun e ↦ c e = a), (H.support e ∩ B).card := card_biUnion_le
    _ ≤ ∑ e ∈ univ.filter (fun e ↦ c e = a), (K.support e ∩ P).card :=
      sum_le_sum fun e _ ↦ hdemand e
    _ ≤ P.card := matching_sum_inter_card_le K _ (coloring_fiber_isMatching K c a) P

/-- The capacity constraint gives an explicit lower bound on the buffer
vertices left uncovered in every color. -/
theorem coloring_uncovered_buffer_ge (H K : FiniteHypergraph V E)
    (B P : Finset V) (hdemand : ∀ e, (H.support e ∩ B).card ≤ (K.support e ∩ P).card)
    (c : K.conflictGraph.Coloring A) (a : A) :
    B.card - P.card ≤
      (B \ ((univ.filter fun e ↦ c e = a).biUnion fun e ↦ H.support e ∩ B)).card := by
  classical
  have hsub : ((univ.filter fun e ↦ c e = a).biUnion fun e ↦ H.support e ∩ B) ⊆ B := by
    intro x hx
    obtain ⟨e, _, he⟩ := mem_biUnion.mp hx
    exact (mem_inter.mp he).2
  rw [card_sdiff_of_subset hsub]
  exact Nat.sub_le_sub_left (coloring_covered_buffer_le_pool H K B P hdemand c a) B.card

#print axioms coloringOfSupportExtension
#print axioms coloring_uncovered_buffer_ge

end Erdos19
