/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingAllMarkerBackwardWalk
import ErdosProblems.Erdos599.GroundingAllMarkerBlockedInitials
import ErdosProblems.Erdos599.PopularCutTrackPruning

/-!
# Actual cut-fragment tracks indexed by receiving requests

We choose one fragment at each represented cut entry. Shared-support
fragments have the same initial and edge set, so the choice does not lose
any edge gadgets. Distinct requests have distinct receiving coordinates,
giving disjoint countable tracks with actual backwards continuations.
-/

noncomputable section

namespace Erdos599.GroundingAllMarkerAuxiliary.Input

open Set Cardinal DirectedPath Alternating GroundingAllMarkerPorts

universe u

variable {V I : Type u} {G : DWeb V} (L : Input G I)

theorem cutFragment_initial_eq_of_common (C : Set L.Vertex)
    {P Q : L.CutFragment} (hP : P ∈ L.cutFragments C) (hQ : Q ∈ L.cutFragments C)
    {x : V} (hxP : x ∈ P.path.support) (hxQ : x ∈ Q.path.support) :
    P.path.initial = Q.path.initial := by
  obtain ⟨hparent, hsupport⟩ := L.cutFragment_parent_and_support_eq_of_common C hP hQ hxP hxQ
  have hPQ := GroundingFragmentUniqueness.beforeEq_parent P
    (GroundingFragmentWarp.initial_beforeEq_of_mem
      (hsupport.symm ▸ Q.path.initial_mem_support))
  have hQP := GroundingFragmentUniqueness.beforeEq_parent Q
    (GroundingFragmentWarp.initial_beforeEq_of_mem
      (hsupport ▸ P.path.initial_mem_support))
  exact GroundingCutDecoder.beforeEq_antisymm hPQ (hparent.symm ▸ hQP)

theorem cutFragment_edgeSet_eq_of_common (C : Set L.Vertex)
    {P Q : L.CutFragment} (hP : P ∈ L.cutFragments C) (hQ : Q ∈ L.cutFragments C)
    {x : V} (hxP : x ∈ P.path.support) (hxQ : x ∈ Q.path.support) :
    P.path.edgeSet = Q.path.edgeSet := by
  have hsupport := (L.cutFragment_parent_and_support_eq_of_common C hP hQ hxP hxQ).2
  have hsub {R T : L.CutFragment} (hR : R ∈ L.cutFragments C)
      (hT : T ∈ L.cutFragments C) (hRT : R.path.support = T.path.support) :
      R.path.edgeSet ⊆ T.path.edgeSet := by
    intro e he
    apply L.survivingEdge_mem_cutFragment C hT
      (hRT ▸ (R.path.edgeSet_subset_support_prod he).1)
    · simp only [familyEdges, Set.mem_iUnion]
      exact ⟨R.parent, R.parent_mem, R.edges_subset he⟩
    · exact fun heC ↦ Set.disjoint_left.mp (L.cutFragment_edges_disjoint C hR) he heC
  exact Set.Subset.antisymm (hsub hP hQ hsupport) (hsub hQ hP hsupport.symm)

theorem fragmentEdgeVertices_eq_of_common (C : Set L.Vertex)
    {P Q : L.CutFragment} (hP : P ∈ L.cutFragments C) (hQ : Q ∈ L.cutFragments C)
    {x : V} (hxP : x ∈ P.path.support) (hxQ : x ∈ Q.path.support) :
    L.fragmentEdgeVertices P = L.fragmentEdgeVertices Q := by
  have hEdges := L.cutFragment_edgeSet_eq_of_common C hP hQ hxP hxQ
  ext a
  cases a with
  | source i => rfl
  | marker y => rfl
  | off x => rfl
  | edge e =>
      change e.1 ∈ P.path.edgeSet ↔ e.1 ∈ Q.path.edgeSet
      rw [hEdges]

theorem fragmentEdgeVertices_countable (P : L.CutFragment) :
    (L.fragmentEdgeVertices P).Countable := by
  have hEdges : P.path.edgeSet.Countable :=
    (P.path.support_countable.prod P.path.support_countable).mono P.path.edgeSet_subset_support_prod
  let f (e : P.path.edgeSet) : L.Vertex := .edge ⟨e.1, by
    simp only [familyEdges, Set.mem_iUnion]
    exact ⟨P.parent, P.parent_mem, P.edges_subset e.2⟩⟩
  have hcarrier : L.fragmentEdgeVertices P = Set.range f := by
    ext a
    constructor
    · intro ha
      cases a with
      | source i => exact ha.elim
      | marker y => exact ha.elim
      | off x => exact ha.elim
      | edge e => exact ⟨⟨e.1, ha⟩, rfl⟩
    · rintro ⟨e, rfl⟩
      exact e.2
  have : Countable P.path.edgeSet := hEdges.to_subtype
  rw [hcarrier]
  exact Set.countable_range f

abbrev FragmentRequest (C : Set L.Vertex) :=
  {r : L.Request C // ∃ P : L.CutFragment,
    P ∈ L.cutFragments C ∧ P.path.initial = L.requestVertex r}

def requestFragment {C : Set L.Vertex} (j : L.FragmentRequest C) : L.CutFragment :=
  Classical.choose j.2

theorem requestFragment_mem {C : Set L.Vertex} (j : L.FragmentRequest C) :
    L.requestFragment j ∈ L.cutFragments C := (Classical.choose_spec j.2).1

theorem requestFragment_initial {C : Set L.Vertex} (j : L.FragmentRequest C) :
    (L.requestFragment j).path.initial = L.requestVertex j.1 := (Classical.choose_spec j.2).2

/-- All structure fields are proved for the actual fragment paths. -/
def fragmentTracks (C : Set L.Vertex) :
    Popular.CutTrackFamily L.web C (L.FragmentRequest C) where
  carrier j := L.fragmentEdgeVertices (L.requestFragment j)
  countable j := L.fragmentEdgeVertices_countable _
  disjoint := by
    intro j k hjk
    apply Set.disjoint_left.mpr
    intro a haj hak
    cases a with
    | source i => exact haj.elim
    | marker y => exact haj.elim
    | off x => exact haj.elim
    | edge e =>
        have hinit := L.cutFragment_initial_eq_of_common C
          (L.requestFragment_mem j) (L.requestFragment_mem k)
          ((L.requestFragment j).path.edgeSet_subset_support_prod haj).1
          ((L.requestFragment k).path.edgeSet_subset_support_prod hak).1
        apply hjk
        apply Subtype.ext
        apply L.requestVertex_injective C
        exact (L.requestFragment_initial j).symm.trans
          (hinit.trans (L.requestFragment_initial k))
  avoids_cut j := L.fragmentEdgeVertices_disjoint_cut C (L.requestFragment_mem j)
  endpoint j := j.1.1
  endpoint_mem j := j.1.2.1
  endpoint_injective := by
    intro j k hjk
    exact Subtype.ext (Subtype.ext hjk)
  continuation j a ha := L.fragmentEdgeVertices_continuation (L.requestFragment j)
    ((L.requestFragment_initial j).symm ▸ L.request_receiving j.1) ha

theorem exists_request_of_cutFragmentAttachable (C : Set L.Vertex) {P : L.CutFragment}
    (hP : L.CutFragmentAttachable C P) :
    ∃ r : L.Request C, P.path.initial = L.requestVertex r := by
  rcases hP with ⟨y, hyC, hy⟩ | ⟨e, heC, _heP, he⟩
  · let r : L.Request C := ⟨.marker y, hyC, by rintro ⟨i, hi⟩; cases hi⟩
    have hr : y.1 = L.requestVertex r := Option.some.inj (L.request_receiving r)
    exact ⟨r, hy.trans hr⟩
  · obtain ⟨heRef, heC⟩ := heC
    let r : L.Request C := ⟨.edge ⟨e, heRef⟩, heC, by rintro ⟨i, hi⟩; cases hi⟩
    have hr : e.2 = L.requestVertex r := Option.some.inj (L.request_receiving r)
    exact ⟨r, he.symm.trans hr⟩

/-- Every attachable fragment is represented, even if its path field is
not the particular concrete representative selected for its request. -/
theorem fragmentEdgeVertices_subset_tracks (C : Set L.Vertex) {P : L.CutFragment}
    (hP : P ∈ L.cutFragments C) (hAttach : L.CutFragmentAttachable C P) :
    L.fragmentEdgeVertices P ⊆ (L.fragmentTracks C).tracks := by
  obtain ⟨r, hr⟩ := L.exists_request_of_cutFragmentAttachable C hAttach
  let j : L.FragmentRequest C := ⟨r, P, hP, hr⟩
  have hinit : (L.requestFragment j).path.initial = P.path.initial :=
    (L.requestFragment_initial j).trans hr.symm
  have hcarriers := L.fragmentEdgeVertices_eq_of_common C hP (L.requestFragment_mem j)
    P.path.initial_mem_support (hinit ▸ (L.requestFragment j).path.initial_mem_support)
  intro a ha
  apply Set.mem_iUnion.mpr
  refine ⟨j, ?_⟩
  change a ∈ L.fragmentEdgeVertices (L.requestFragment j)
  exact hcarriers ▸ ha

#print axioms cutFragment_initial_eq_of_common
#print axioms fragmentEdgeVertices_eq_of_common
#print axioms fragmentTracks
#print axioms fragmentEdgeVertices_subset_tracks

end Erdos599.GroundingAllMarkerAuxiliary.Input
