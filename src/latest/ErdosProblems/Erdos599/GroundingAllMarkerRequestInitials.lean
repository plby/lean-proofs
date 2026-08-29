/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingAllMarkerFragmentTracks

/-!
# Reference requests begin genuine hanging fragments

A receiving request on the reference has no incoming surviving matching
pair. Fragment coverage therefore places it at the initial of its
fragment. Off-reference requests are precisely the ones with no fragment.
For the normalized source/marker profile, all request fragments are hanging.
-/

namespace Erdos599.GroundingAllMarkerAuxiliary.Input

open Set DirectedPath Alternating GroundingAllMarkerPorts

universe u

variable {V I : Type u} {G : DWeb V} (L : Input G I)

theorem request_residual_noIncoming_of_mem_reference (C : Set L.Vertex) (r : L.Request C)
    (hr : L.requestVertex r ∈ G.vertexSet L.reference.paths) (x : V) :
    ¬ L.residualMatching C x (L.requestVertex r) := by
  intro h
  have hrecv := L.request_receiving r
  rcases L.request_cases r with ⟨y, hry⟩ | ⟨e, hre⟩ | ⟨z, hrz⟩
  · have hy : y.1 = L.requestVertex r :=
      Option.some.inj (by simpa only [hry, receiving] using hrecv)
    exact L.marker_receiving_unmatched y x (hy.symm ▸ L.residualMatching_subset_reference C h)
  · have he : e.1.2 = L.requestVertex r :=
      Option.some.inj (by simpa only [hre, receiving] using hrecv)
    exact L.residualMatching_noIncoming_cutHead C ⟨e.2, hre ▸ r.2.1⟩ x (he.symm ▸ h)
  · have hz : z.1 = L.requestVertex r :=
      Option.some.inj (by simpa only [hrz, receiving] using hrecv)
    exact z.2 (hz.symm ▸ hr)

theorem cutFragment_initial_of_noIncoming (C : Set L.Vertex) {P : L.CutFragment}
    (hP : P ∈ L.cutFragments C) {x : V} (hx : x ∈ P.path.support)
    (hfree : ∀ y, ¬ L.residualMatching C y x) : P.path.initial = x := by
  by_contra hne
  obtain ⟨p, hps, hpf, hpE⟩ := GroundingCutDecoder.exists_forward_segment_of_before
    ⟨GroundingFragmentWarp.initial_beforeEq_of_mem hx, hne⟩
  have hnontrivial : p.finish ≠ p.start := by
    rw [hps, hpf]
    exact fun h ↦ hne h.symm
  obtain ⟨y, hy⟩ := FinitePath.exists_incoming_edge_of_mem_support_of_ne_start
    p p.finish_mem_support hnontrivial
  exact hfree y (hpf ▸ L.residualMatching_of_cutFragment_edge C hP (hpE hy))

/-- The existential fragment condition used by FragmentRequest is exactly
the geometric condition that the receiving vertex lies on the reference. -/
theorem requestFragment_exists_iff_mem_reference (C : Set L.Vertex) (r : L.Request C) :
    (∃ P : L.CutFragment, P ∈ L.cutFragments C ∧ P.path.initial = L.requestVertex r) ↔
      L.requestVertex r ∈ G.vertexSet L.reference.paths := by
  constructor
  · rintro ⟨P, _, hinit⟩
    exact ⟨P.parent, P.parent_mem, hinit ▸ P.support_subset P.path.initial_mem_support⟩
  · intro hr
    obtain ⟨p, hp, hpr⟩ := hr
    obtain ⟨P, _, hP, hrP⟩ := L.exists_cutFragment_containing C hp hpr
    exact ⟨P, hP, L.cutFragment_initial_of_noIncoming C hP hrP
      (L.request_residual_noIncoming_of_mem_reference C r ⟨p, hp, hpr⟩)⟩

theorem requestVertex_not_source_of_mem_reference (C : Set L.Vertex) (r : L.Request C)
    (hr : L.requestVertex r ∈ G.vertexSet L.reference.paths)
    (hNoEnter : G.NoEdgeEnters G.source) (hMarkers : Disjoint G.source L.markers) :
    L.requestVertex r ∉ G.source := by
  intro hsource
  have hrecv := L.request_receiving r
  rcases L.request_cases r with ⟨y, hry⟩ | ⟨e, hre⟩ | ⟨z, hrz⟩
  · have hy : y.1 = L.requestVertex r :=
      Option.some.inj (by simpa only [hry, receiving] using hrecv)
    exact Set.disjoint_left.mp hMarkers hsource (hy ▸ y.2)
  · have he : e.1.2 = L.requestVertex r :=
      Option.some.inj (by simpa only [hre, receiving] using hrecv)
    have hAdj : G.graph.Adj e.1.1 e.1.2 := familyEdges_subset_adj L.reference.paths e.2
    exact hNoEnter (he ▸ hAdj) hsource
  · have hz : z.1 = L.requestVertex r :=
      Option.some.inj (by simpa only [hrz, receiving] using hrecv)
    exact z.2 (hz.symm ▸ hr)

theorem requestFragment_not_grounded (C : Set L.Vertex) (r : L.Request C)
    (hNoEnter : G.NoEdgeEnters G.source) (hMarkers : Disjoint G.source L.markers)
    (P : L.CutFragment) (hinit : P.path.initial = L.requestVertex r) :
    ¬ L.CutFragmentGrounded P := by
  intro hgrounded
  exact L.requestVertex_not_source_of_mem_reference C r
    ⟨P.parent, P.parent_mem, hinit ▸ P.support_subset P.path.initial_mem_support⟩
    hNoEnter hMarkers (hinit ▸ hgrounded)

#print axioms request_residual_noIncoming_of_mem_reference
#print axioms requestFragment_exists_iff_mem_reference
#print axioms requestFragment_not_grounded

end Erdos599.GroundingAllMarkerAuxiliary.Input
