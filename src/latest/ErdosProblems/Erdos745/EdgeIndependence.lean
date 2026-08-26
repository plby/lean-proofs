import ErdosProblems.Erdos745.ComponentLaw

/-!
# Independence of disjoint edge-coordinate blocks

This extends the cylinder formulas to arbitrary events using only a specified
set of coordinates. It will isolate a first path edge from its continuation.
-/

open scoped BigOperators Sym2

namespace Erdos745

noncomputable section

attribute [local instance] Classical.propDecidable

theorem eventMass_disjoint_blocks {α : Type*} [Fintype α] [DecidableEq α]
    (p : ℝ) (S T : Finset α) (hST : Disjoint S T) (P Q : Finset α → Prop)
    (hP : ∀ A, P A ↔ P (A ∩ S)) (hQ : ∀ A, Q A ↔ Q (A ∩ T)) :
    Erdos746.BernoulliFinset.eventMass Finset.univ p (fun A ↦ P A ∧ Q A) =
      Erdos746.BernoulliFinset.eventMass Finset.univ p P *
        Erdos746.BernoulliFinset.eventMass Finset.univ p Q := by
  open Erdos746.BernoulliFinset in
  have h := eventMass_restrict (Finset.subset_univ (S ∪ T)) p
    (fun A ↦ P (A ∩ S) ∧ Q (A ∩ T))
  have hS (A : Finset α) : (A ∩ (S ∪ T)) ∩ S = A ∩ S := by
    rw [Finset.inter_assoc, Finset.inter_eq_right.mpr Finset.subset_union_left]
  have hT (A : Finset α) : (A ∩ (S ∪ T)) ∩ T = A ∩ T := by
    rw [Finset.inter_assoc, Finset.inter_eq_right.mpr Finset.subset_union_right]
  simp only [hS, hT] at h
  rw [Erdos746.BernoulliFinset.eventMass_inter_factor hST p P Q] at h
  rw [← Erdos746.BernoulliFinset.eventMass_restrict (Finset.subset_univ S) p P,
    ← Erdos746.BernoulliFinset.eventMass_restrict (Finset.subset_univ T) p Q] at h
  simpa only [← hP, ← hQ] using h

/-- The event is determined by its indicated finite edge block. -/
def EdgeLocal {n : ℕ} (S : Finset (Edge n)) (P : SimpleGraph (Fin n) → Prop) : Prop :=
  ∀ A, P (Erdos746.graphOfEdges A) ↔ P (Erdos746.graphOfEdges (A ∩ S))

theorem probability_disjoint_blocks (lam : ℝ) (n : ℕ)
    (S T : Finset (Edge n)) (hST : Disjoint S T)
    (P Q : SimpleGraph (Fin n) → Prop) (hP : EdgeLocal S P) (hQ : EdgeLocal T Q) :
    probability lam n (fun G ↦ P G ∧ Q G) = probability lam n P * probability lam n Q := by
  simp only [probability_eq_edgeEventMass]
  exact eventMass_disjoint_blocks _ S T hST _ _ hP hQ

/-- A single possible edge, with its proof of distinct endpoints. -/
def pairEdge {n : ℕ} (u v : Fin n) (huv : u ≠ v) : Edge n :=
  ⟨s(u, v), by simpa using huv⟩

theorem pairEdge_mem_coordinates {n : ℕ} (u v : Fin n) (huv : u ≠ v)
    (G : SimpleGraph (Fin n)) : pairEdge u v huv ∈ edgeCoordinates G ↔ G.Adj u v := by
  simp only [mem_edgeCoordinates, pairEdge, SimpleGraph.mem_edgeSet]

theorem pairEdge_mem_graphOfEdges {n : ℕ} (u v : Fin n) (huv : u ≠ v)
    (A : Finset (Edge n)) : (Erdos746.graphOfEdges A).Adj u v ↔ pairEdge u v huv ∈ A := by
  rw [← pairEdge_mem_coordinates u v huv, edgeCoordinates_graphOfEdges]

theorem edgeLocal_adj {n : ℕ} (u v : Fin n) (huv : u ≠ v) :
    EdgeLocal {pairEdge u v huv} (fun G ↦ G.Adj u v) := by
  intro A
  simp only [pairEdge_mem_graphOfEdges u v huv, Finset.mem_inter, Finset.mem_singleton,
    and_true]

theorem probability_adj (lam : ℝ) (n : ℕ) (u v : Fin n) (huv : u ≠ v) :
    probability lam n (fun G ↦ G.Adj u v) = (edgeProbability lam n : ℝ) := by
  have h := probability_edge_cylinder lam n {pairEdge u v huv} ∅ (by simp)
  simpa only [Finset.singleton_subset_iff, pairEdge_mem_coordinates,
    Finset.disjoint_empty_left, and_true, Finset.card_singleton, Finset.card_empty,
    pow_one, pow_zero, mul_one] using h

theorem internalEdge_restriction_adj {n : ℕ} (S : Finset (Fin n))
    (A : Finset (Edge n)) {u v : Fin n} (hu : u ∈ S) (hv : v ∈ S) :
    (Erdos746.graphOfEdges A).Adj u v ↔
      (Erdos746.graphOfEdges (A ∩ internalEdges S)).Adj u v := by
  by_cases huv : u = v
  · subst v
    simp
  · simp only [pairEdge_mem_graphOfEdges u v huv, Finset.mem_inter,
      mem_internalEdges_pair S (pairEdge u v huv) rfl, hu, hv, true_and, and_true]

theorem pairEdge_disjoint_internal_erase {n : ℕ} (S : Finset (Fin n))
    (r u : Fin n) (hru : r ≠ u) :
    Disjoint {pairEdge r u hru} (internalEdges (S.erase r)) := by
  rw [Finset.disjoint_singleton_left, mem_internalEdges_pair _ _ rfl]
  simp

end

end Erdos745
