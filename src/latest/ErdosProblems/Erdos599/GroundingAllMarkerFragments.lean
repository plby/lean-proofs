/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingAllMarkerResidual
import ErdosProblems.Erdos599.GroundingSurvivingEdgeFragment

/-!
# Reusing literal deleted-fragment geometry for the all-marker cut

The older fragment library depends on its input only through the reference
warp and its represented edge cut. We supply exactly these two data and
prove that the represented edge cut equals the present physical cut.
The adapter has no proxies or finite sources because neither participates
in fragment geometry. Its auxiliary graph, target set, escape region and
parent-based grounding predicate are NOT identified with the new ones.
-/

namespace Erdos599.GroundingAllMarkerAuxiliary.Input

open Set DirectedPath Alternating GroundingAllMarkerPorts

universe u

variable {V I : Type u} {G : DWeb V} (L : Input G I)

/-- A geometry-only input for the existing deleted-fragment library. -/
def cutFragmentInput : PopularAuxiliary.Input G PEmpty.{u + 1} where
  ladder := L.reference
  finiteSource := ∅
  markerSet := L.markers
  proxyPath i := nomatch i
  proxy_isRay i := nomatch i

def cutFragmentTags (C : Set L.Vertex) : Set L.cutFragmentInput.LV
  | .edge x y => (x, y) ∈ L.cutEdges C
  | _ => False

theorem cutFragmentInput_familyEdges :
    L.cutFragmentInput.familyEdges = familyEdges L.reference.paths := by
  ext e
  simp only [PopularAuxiliary.Input.familyEdges, cutFragmentInput,
    familyEdges, Set.mem_iUnion, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨p, hp, he⟩
    exact ⟨p, hp, he⟩
  · rintro ⟨p, hp, he⟩
    exact ⟨p, hp, he⟩

/-- The adapter deletes exactly the physical reference edges, no more
and no fewer. This equality is independent of both auxiliary graphs. -/
theorem cutFragmentTags_CE (C : Set L.Vertex) :
    GroundingCut.CE L.cutFragmentInput (L.cutFragmentTags C) = L.cutEdges C := by
  ext e
  change (e ∈ L.cutEdges C ∧ e ∈ L.cutFragmentInput.familyEdges) ↔ e ∈ L.cutEdges C
  rw [L.cutFragmentInput_familyEdges]
  exact ⟨And.left, fun he ↦ ⟨he, L.cutEdges_subset_reference C he⟩⟩

abbrev CutFragment := L.cutFragmentInput.Fragment

def cutFragments (C : Set L.Vertex) : Set L.CutFragment :=
  GroundingCut.fragments L.cutFragmentInput (L.cutFragmentTags C)

theorem cutFragment_edges_disjoint (C : Set L.Vertex) {P : L.CutFragment}
    (hP : P ∈ L.cutFragments C) : Disjoint P.path.edgeSet (L.cutEdges C) := by
  simpa only [L.cutFragmentTags_CE C] using hP.1

/-- Coverage includes singleton pieces, finite pieces of rays, and ray
tails. The original existence proof uses only literal surviving edges. -/
theorem exists_cutFragment_containing (C : Set L.Vertex) {p : G.DPath}
    (hp : p ∈ L.reference.paths) {x : V} (hx : x ∈ p.support) :
    ∃ P : L.CutFragment, P.parent = p ∧ P ∈ L.cutFragments C ∧ x ∈ P.path.support :=
  GroundingFragmentPartition.exists_fragment_containing
    L.cutFragmentInput (L.cutFragmentTags C) hp hx

theorem cutFragment_parent_and_support_eq_of_common (C : Set L.Vertex)
    {P Q : L.CutFragment} (hP : P ∈ L.cutFragments C) (hQ : Q ∈ L.cutFragments C)
    {x : V} (hxP : x ∈ P.path.support) (hxQ : x ∈ Q.path.support) :
    P.parent = Q.parent ∧ P.path.support = Q.path.support :=
  GroundingFragmentUniqueness.parent_eq_and_support_eq_of_common hP hQ hxP hxQ

theorem survivingEdge_mem_cutFragment (C : Set L.Vertex) {P : L.CutFragment}
    (hP : P ∈ L.cutFragments C) {x y : V} (hx : x ∈ P.path.support)
    (hxy : (x, y) ∈ familyEdges L.reference.paths) (hnot : (x, y) ∉ L.cutEdges C) :
    (x, y) ∈ P.path.edgeSet := by
  apply GroundingSurvivingEdgeFragment.edge_mem_fragment L.cutFragmentInput P hP hx
  · simpa only [L.cutFragmentInput_familyEdges] using hxy
  · simpa only [L.cutFragmentTags_CE C] using hnot

theorem exists_cutFragment_containing_edge (C : Set L.Vertex) {e : V × V}
    (he : e ∈ familyEdges L.reference.paths) (hnot : e ∉ L.cutEdges C) :
    ∃ P : L.CutFragment, P ∈ L.cutFragments C ∧ e ∈ P.path.edgeSet := by
  apply GroundingSurvivingEdgeFragment.exists_fragment_containing_edge L.cutFragmentInput
  · simpa only [L.cutFragmentInput_familyEdges] using he
  · simpa only [L.cutFragmentTags_CE C] using hnot

#print axioms cutFragmentTags_CE
#print axioms exists_cutFragment_containing
#print axioms cutFragment_parent_and_support_eq_of_common
#print axioms exists_cutFragment_containing_edge

end Erdos599.GroundingAllMarkerAuxiliary.Input
