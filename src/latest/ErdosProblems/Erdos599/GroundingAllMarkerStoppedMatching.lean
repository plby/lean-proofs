/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingAllMarkerStoppedRouteEdges

/-!
# The stopped matching and its free request ports

Stopped reference edges and uncut off-reference identities form a genuine
partial matching. All three sorts of requests have free receiving ports.
Restricting an origin record to the part before its departure point frees
the required sending port, including when the original record is a ray.
-/

namespace Erdos599.GroundingAllMarkerAuxiliary.Input

open Set DirectedPath Alternating GroundingAllMarkerPorts

universe u

variable {V I : Type u} {G : DWeb V} (L : Input G I)

def stoppedReferenceEdges (C : Set L.Vertex) : Set (V × V) :=
  {e | ∃ P ∈ L.cutFragments C, e ∈ (L.stoppedFragment C P).edgeSet}

theorem stoppedReferenceEdges_subset (C : Set L.Vertex) :
    L.stoppedReferenceEdges C ⊆ familyEdges L.reference.paths := by
  rintro e ⟨P, _, he⟩
  simp only [familyEdges, Set.mem_iUnion]
  exact ⟨P.parent, P.parent_mem, P.edges_subset (L.stoppedFragment_edgeSet_subset C P he)⟩

theorem stoppedReferenceEdges_disjoint_cut (C : Set L.Vertex) :
    Disjoint (L.stoppedReferenceEdges C) (L.cutEdges C) := by
  apply Set.disjoint_left.mpr
  rintro e ⟨P, hP, he⟩ heCut
  exact Set.disjoint_left.mp (L.cutFragment_edges_disjoint C hP)
    (L.stoppedFragment_edgeSet_subset C P he) heCut

def stoppedMatching (C : Set L.Vertex) (x y : V) : Prop :=
  (x, y) ∈ L.stoppedReferenceEdges C ∨
    (x = y ∧ x ∉ G.vertexSet L.reference.paths ∧ x ∉ L.cutOffVertices C)

theorem stoppedMatching_subset_residual (C : Set L.Vertex) {x y : V}
    (h : L.stoppedMatching C x y) : L.residualMatching C x y := by
  rcases h with he | ⟨hxy, hx, _⟩
  · exact Or.inl ⟨L.stoppedReferenceEdges_subset C he,
      Set.disjoint_left.mp (L.stoppedReferenceEdges_disjoint_cut C) he⟩
  · exact Or.inr ⟨hxy, hx⟩

theorem stoppedMatching_biUnique (C : Set L.Vertex) : Relator.BiUnique (L.stoppedMatching C) := by
  have hsub : ∀ {x y}, L.stoppedMatching C x y → referenceMatching L.reference.paths x y :=
    fun h ↦ L.residualMatching_subset_reference C (L.stoppedMatching_subset_residual C h)
  exact ⟨fun _ _ _ hx hy ↦
      (referenceMatching_biUnique L.reference.disjoint).1 (hsub hx) (hsub hy),
    fun _ _ _ hx hy ↦
      (referenceMatching_biUnique L.reference.disjoint).2 (hsub hx) (hsub hy)⟩

theorem stoppedMatching_tail_not_blockingSet (C : Set L.Vertex) {x y : V}
    (h : L.stoppedMatching C x y) : x ∉ L.blockingSet C := by
  rcases h with ⟨P, hP, he⟩ | ⟨_, hxRef, hxCut⟩
  · exact L.stoppedFragment_no_edge_from_blockingSet C hP he
  · rintro (hx | hx | hx)
    · exact hxCut hx
    · exact hxRef hx.1
    · exact hxRef hx.1

/-- A request is entered at a genuinely free receiving port; in particular
the final cut-edge gadget is not traversed backwards. -/
theorem stoppedMatching_request_unmatched (C : Set L.Vertex) (r : L.Request C) (x : V) :
    ¬ L.stoppedMatching C x (L.requestVertex r) := by
  intro h
  have hrecv := L.request_receiving r
  rcases L.request_cases r with ⟨y, hry⟩ | ⟨e, hre⟩ | ⟨z, hrz⟩
  · have hy : y.1 = L.requestVertex r :=
      Option.some.inj (by simpa only [hry, receiving] using hrecv)
    exact L.marker_receiving_unmatched y x (hy.symm ▸
      L.residualMatching_subset_reference C (L.stoppedMatching_subset_residual C h))
  · have he : e.1.2 = L.requestVertex r :=
      Option.some.inj (by simpa only [hre, receiving] using hrecv)
    exact L.residualMatching_noIncoming_cutHead C ⟨e.2, hre ▸ r.2.1⟩ x
      (he.symm ▸ L.stoppedMatching_subset_residual C h)
  · have hz : z.1 = L.requestVertex r :=
      Option.some.inj (by simpa only [hrz, receiving] using hrecv)
    rcases h with h | ⟨hx, _, hxCut⟩
    · have hzRef :=
        (familyEdges_subset_vertexSet_prod L.reference.paths
          (L.stoppedReferenceEdges_subset C h)).2
      exact z.2 (hz.symm ▸ hzRef)
    · apply hxCut
      have hxz : x = z.1 := hx.trans hz.symm
      exact hxz.symm ▸ (show z.1 ∈ L.cutOffVertices C from ⟨z.2, hrz ▸ r.2.1⟩)

/-- Truncate one origin at its departure point while leaving other
stopped matching pairs untouched. -/
def originStoppedMatching (C : Set L.Vertex) (i : I) (x : V) (a b : V) : Prop :=
  L.stoppedMatching C a b ∧ (a ∈ (L.record i).support → GroundingCut.Before (L.record i) a x)

theorem originStoppedMatching_biUnique (C : Set L.Vertex) (i : I) (x : V) :
    Relator.BiUnique (L.originStoppedMatching C i x) :=
  ⟨fun _ _ _ h h' ↦ (L.stoppedMatching_biUnique C).1 h.1 h'.1,
    fun _ _ _ h h' ↦ (L.stoppedMatching_biUnique C).2 h.1 h'.1⟩

theorem originStoppedMatching_source_unmatched (C : Set L.Vertex) (i : I) {x : V}
    (hx : x ∈ (L.record i).support) (y : V) : ¬ L.originStoppedMatching C i x x y :=
  fun h ↦ (h.2 hx).2 rfl

theorem originStoppedMatching_request_unmatched (C : Set L.Vertex)
    (i : I) (x : V) (r : L.Request C) (a : V) :
    ¬ L.originStoppedMatching C i x a (L.requestVertex r) :=
  fun h ↦ L.stoppedMatching_request_unmatched C r a h.1

#print axioms stoppedMatching_biUnique
#print axioms stoppedMatching_tail_not_blockingSet
#print axioms stoppedMatching_request_unmatched
#print axioms originStoppedMatching_source_unmatched
#print axioms originStoppedMatching_request_unmatched

end Erdos599.GroundingAllMarkerAuxiliary.Input
