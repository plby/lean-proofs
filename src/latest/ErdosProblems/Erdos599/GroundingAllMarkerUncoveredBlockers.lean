/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingAllMarkerLocalIndependence

/-!
# Blockers not covered by a local transaction have untouched grounded prefixes

Off-reference blockers have their own request. Every attachable blocked
fragment is selected by its request up to equality of support. A blocked
fragment meeting any transaction region has its blocker covered there.
Thus an uncovered blocker lies on a grounded fragment disjoint from all
transaction regions. These are the exact leftover components to retain.
-/

namespace Erdos599.GroundingAllMarkerAuxiliary.Input

open Set Cardinal DirectedPath Alternating GroundingAllMarkerPorts

universe u

variable {V I : Type u} {G : DWeb V} (L : Input G I) {kappa : Cardinal.{u}}
  {U : Popular.KappaIndexed L.web kappa} (S : Popular.PopularSeparator U)
  (hInitial : ∀ i, (L.record i).initial ∉ L.markers)

def locallyCoveredBlockers : Set V :=
  ⋃ r : L.Request S.cut, (L.independentPortAugmentation S hInitial r).localBlockingSet L

theorem locallyCoveredBlockers_subset :
    L.locallyCoveredBlockers S hInitial ⊆ L.blockingSet S.cut := by
  intro x hx
  obtain ⟨r, hr⟩ := Set.mem_iUnion.mp hx
  exact hr.1

theorem cutOffVertices_subset_locallyCovered :
    L.cutOffVertices S.cut ⊆ L.locallyCoveredBlockers S hInitial := by
  rintro x ⟨hxRef, hxCut⟩
  let r : L.Request S.cut := ⟨.off ⟨x, hxRef⟩, hxCut, by rintro ⟨i, hi⟩; cases hi⟩
  have hx : x = L.requestVertex r := Option.some.inj (L.request_receiving r)
  exact Set.mem_iUnion.mpr ⟨r, Or.inl ⟨hxRef, hxCut⟩, Or.inl hx⟩

theorem attachable_blocker_locallyCovered {P : L.CutFragment}
    (hP : P ∈ L.blockedFragments S.cut) (hAttach : L.CutFragmentAttachable S.cut P) :
    L.fragmentBlockingPoint S.cut P ∈ L.locallyCoveredBlockers S hInitial := by
  obtain ⟨r, hinit⟩ := L.exists_request_of_cutFragmentAttachable S.cut hAttach
  have hrRef : L.requestVertex r ∈ G.vertexSet L.reference.paths :=
    ⟨P.parent, P.parent_mem, hinit ▸ P.support_subset P.path.initial_mem_support⟩
  obtain ⟨Q, hQ⟩ := L.selectedRequestFragments_nonempty S.cut r hrRef
  have hQs := L.selectedRequestFragments_spec S.cut r hQ
  have hcommon : P.path.initial ∈ Q.path.support :=
    (hQs.2.trans hinit.symm) ▸ Q.path.initial_mem_support
  have heq := (L.cutFragment_parent_and_support_eq_of_common S.cut hP.1 hQs.1
    P.path.initial_mem_support hcommon).2
  have hb := L.fragmentBlockingPoint_mem S.cut hP
  exact Set.mem_iUnion.mpr ⟨r, hb.2, Or.inr ⟨Q, Or.inr hQ, heq ▸ hb.1⟩⟩

theorem blockedFragment_contact_locallyCovered {P : L.CutFragment}
    (hP : P ∈ L.blockedFragments S.cut) (r : L.Request S.cut) {x : V}
    (hxP : x ∈ P.path.support)
    (hx : x ∈ (L.independentPortAugmentation S hInitial r).localRegion L) :
    L.fragmentBlockingPoint S.cut P ∈ L.locallyCoveredBlockers S hInitial := by
  let D := L.independentPortAugmentation S hInitial r
  rcases hx with (hOrigin | ⟨Q, hQ, hxQ⟩) | ⟨hxOff, _⟩
  · have heq := DWeb.IsWarp.eq_of_mem_support L.reference.disjoint
      P.parent_mem (L.record_mem D.origin) (P.support_subset hxP) hOrigin
    exact (L.blockedFragment_parent_ne_goodRecord S.cut S.separates hP D.origin_good heq).elim
  · have heq := (L.cutFragment_parent_and_support_eq_of_common S.cut hP.1
      (L.localFragments_mem S.cut _ r hQ) hxP hxQ).2
    have hb := L.fragmentBlockingPoint_mem S.cut hP
    exact Set.mem_iUnion.mpr ⟨r, hb.2, Or.inr ⟨Q, hQ, heq ▸ hb.1⟩⟩
  · exact (hxOff ⟨P.parent, P.parent_mem, P.support_subset hxP⟩).elim

variable (hInitials : G.initialSet L.reference.paths ⊆ G.source ∪ L.markers)

include hInitials in
theorem uncovered_blocker_fragment {b : V}
    (hb : b ∈ L.blockingSet S.cut) (hnot : b ∉ L.locallyCoveredBlockers S hInitial) :
    ∃ P : L.CutFragment, P ∈ L.blockedFragments S.cut ∧ L.CutFragmentGrounded P ∧
      L.fragmentBlockingPoint S.cut P = b ∧
      ∀ r : L.Request S.cut,
        Disjoint P.path.support ((L.independentPortAugmentation S hInitial r).localRegion L) := by
  rw [L.blockingSet_eq_cutOff_union_fragmentBlockingPoints S.cut] at hb
  rcases hb with hb | ⟨P, hP, hPb⟩
  · exact (hnot (L.cutOffVertices_subset_locallyCovered S hInitial hb)).elim
  · refine ⟨P, hP, ?_, hPb, ?_⟩
    · rcases L.blockedFragment_grounded_or_attachable S.cut hInitials hP with hg | ha
      · exact hg
      · exact (hnot (hPb ▸ L.attachable_blocker_locallyCovered S hInitial hP ha)).elim
    · intro r
      apply Set.disjoint_left.mpr
      intro x hxP hx
      exact hnot (hPb ▸ L.blockedFragment_contact_locallyCovered S hInitial hP r hxP hx)

#print axioms cutOffVertices_subset_locallyCovered
#print axioms attachable_blocker_locallyCovered
#print axioms blockedFragment_contact_locallyCovered
#print axioms uncovered_blocker_fragment

end Erdos599.GroundingAllMarkerAuxiliary.Input
