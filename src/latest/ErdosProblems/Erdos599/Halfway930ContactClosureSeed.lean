/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.Halfway930ReferenceAvoidance

/-!
# The source-free closure seed for Assertion 9.30

The ambient source of the normalized web can be larger than `kappa`, so a
public half-way transaction cannot close around the complete selected
reference.  Only two parts of that reference must be registered before the
coupled transaction:

* every marker-starting component, whose carrier has size at most `kappa`;
* every reference component meeting the current blueprint, whose carrier
  also has size at most `kappa` by warp disjointness.

Together with the preceding closed set and the current blueprint carrier,
these form the honest source-free initial seed for the global simultaneous
assignment.  This file packages its cardinal and roof facts without any
bound on the ambient source.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace Blueprint
namespace LinkageBlueprint

open DirectedPath Alternating Ladder

universe u

variable {V : Type u}
variable {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}

/-- The closure seed relevant to a coupled 9.30 replacement.  The complete
carrier of the source-starting reference is deliberately absent. -/
def continuation930ContactSeed
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (W : LinkageBlueprint Gamma C.selectedReference kappa) : Set V :=
  ((C.before ∪ W.vertexSet) ∪
      Gamma.vertexSet
        (ladderReference.markerStarting
          (Gamma := Gamma) (L := C.ladder) (a := C.newStage))) ∪
    meetingVertices Gamma C.selectedReference W.vertexSet

/-- The part of the closure seed which a newly selected hammock member must
avoid.  The preceding closed set is omitted because contacts with it are the
intended cut points of the transaction. -/
def continuation930ContactReserved
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (W : LinkageBlueprint Gamma C.selectedReference kappa) : Set V :=
  (W.vertexSet ∪
      Gamma.vertexSet
        (ladderReference.markerStarting
          (Gamma := Gamma) (L := C.ladder) (a := C.newStage))) ∪
    meetingVertices Gamma C.selectedReference W.vertexSet

/-- The request-specific seed after a hammock member has been selected.
Closing around its complete carrier is what lets the later simultaneous
assignment replace every contact at once, instead of treating literal
safeness as a switching certificate. -/
def continuation930SelectedSeed
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (W : LinkageBlueprint Gamma C.selectedReference kappa)
    (Q : AltPath Gamma.graph) : Set V :=
  continuation930ContactSeed C W ∪ Q.vertexSet

namespace continuation930ContactSeed

variable (C : ClubStageGeometry Gamma Y kappa (succ kappa))
variable (W : LinkageBlueprint Gamma C.selectedReference kappa)

/-- The coupled contact seed has size at most `kappa`, independently of the
cardinality of `Gamma.source`. -/
theorem mk_le
    (hW : W.IsLinkageBlueprint C.newSlice C.closedSet C.persistent) :
    #(continuation930ContactSeed C W) ≤ kappa := by
  have hWvertices : #W.vertexSet ≤ kappa :=
    W.mk_vertexSet_le_of_mk_paths_le C.capacity_infinite hW.card_paths
  have hmarker :
      #(Gamma.vertexSet
          (ladderReference.markerStarting
            (Gamma := Gamma) (L := C.ladder) (a := C.newStage))) ≤
        kappa :=
    ladderReference.mk_markerStarting_vertices_le C.legal
      C.capacity_infinite C.newStage
  have hcontact :
      #(meetingVertices Gamma C.selectedReference W.vertexSet) ≤ kappa :=
    mk_blueprintMeetingReferenceVertices_le C W hW
  have hbeforeW : #(C.before ∪ W.vertexSet : Set V) ≤ kappa :=
    (Cardinal.mk_union_le _ _).trans
      (Cardinal.add_le_of_le C.capacity_infinite C.before_card hWvertices)
  have hbeforeWMarker :
      #(((C.before ∪ W.vertexSet) ∪
          Gamma.vertexSet
            (ladderReference.markerStarting
              (Gamma := Gamma) (L := C.ladder) (a := C.newStage))) : Set V) ≤
        kappa :=
    (Cardinal.mk_union_le _ _).trans
      (Cardinal.add_le_of_le C.capacity_infinite hbeforeW hmarker)
  exact (Cardinal.mk_union_le _ _).trans
    (Cardinal.add_le_of_le C.capacity_infinite hbeforeWMarker hcontact)

/-- The preceding closed set is registered in the contact seed. -/
theorem before_subset : C.before ⊆ continuation930ContactSeed C W := by
  intro x hx
  exact Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _ hx))

/-- The whole current blueprint carrier is registered in the contact seed. -/
theorem blueprint_subset : W.vertexSet ⊆ continuation930ContactSeed C W := by
  intro x hx
  exact Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_right _ hx))

/-- Every marker-starting reference component is swallowed by the seed. -/
theorem markerVertices_subset :
    Gamma.vertexSet
        (ladderReference.markerStarting
          (Gamma := Gamma) (L := C.ladder) (a := C.newStage)) ⊆
      continuation930ContactSeed C W := by
  intro x hx
  exact Set.mem_union_left _ (Set.mem_union_right _ hx)

/-- In particular all marker-starting initials are swallowed by the seed,
which is the exact hypothesis of `MarkerAbsorbedMacroSeed`. -/
theorem markerInitials_subset :
    Gamma.initialSet
        (ladderReference.markerStarting
          (Gamma := Gamma) (L := C.ladder) (a := C.newStage)) ⊆
      continuation930ContactSeed C W := by
  rintro x ⟨p, hp, rfl⟩
  apply markerVertices_subset C W
  exact ⟨p, hp, p.initial_mem_support⟩

/-- Every complete selected-reference component which meets the current
blueprint is registered in the seed. -/
theorem meetingReference_subset :
    meetingVertices Gamma C.selectedReference W.vertexSet ⊆
      continuation930ContactSeed C W := by
  intro x hx
  exact Set.mem_union_right _ hx

/-- The contact-reserved carrier is literally part of the closure seed. -/
theorem reserved_subset_seed :
    continuation930ContactReserved C W ⊆
      continuation930ContactSeed C W := by
  intro x hx
  rcases hx with (hxW | hxMarker) | hxContact
  · exact blueprint_subset C W hxW
  · exact markerVertices_subset C W hxMarker
  · exact meetingReference_subset C W hxContact

/-- The whole contact-reserved carrier is small, with no ambient-source
cardinality premise. -/
theorem reserved_mk_le
    (hW : W.IsLinkageBlueprint C.newSlice C.closedSet C.persistent) :
    #(continuation930ContactReserved C W) ≤ kappa := by
  exact (Cardinal.mk_subtype_mono (reserved_subset_seed C W)).trans
    (mk_le C W hW)

/-- Adding the selected finite or infinite alternating member preserves the
`kappa` bound, because every alternating trace has countable carrier. -/
theorem selected_mk_le
    (Q : AltPath Gamma.graph)
    (hW : W.IsLinkageBlueprint C.newSlice C.closedSet C.persistent) :
    #(continuation930SelectedSeed C W Q) ≤ kappa := by
  exact (Cardinal.mk_union_le _ _).trans
    (Cardinal.add_le_of_le C.capacity_infinite (mk_le C W hW)
      ((altPath_vertexSet_countable Q).le_aleph0.trans C.capacity_infinite))

/-- The request-specific seed retains all contact bookkeeping. -/
theorem contactSeed_subset_selected (Q : AltPath Gamma.graph) :
    continuation930ContactSeed C W ⊆
      continuation930SelectedSeed C W Q :=
  Set.subset_union_left

/-- The selected hammock carrier is explicitly registered for closing. -/
theorem selectedPath_subset (Q : AltPath Gamma.graph) :
    Q.vertexSet ⊆ continuation930SelectedSeed C W Q :=
  Set.subset_union_right

/-- Roof containment follows from the public blueprint geometry and the
selected-reference self-roofing fact.  Only the preceding closed set needs
to be supplied by the club selector. -/
theorem subset_outerRoof
    (hW : W.IsLinkageBlueprint C.newSlice C.closedSet C.persistent)
    (hbefore : C.before ⊆ C.outerRoof)
    (href : ∀ p ∈ C.selectedReference, p.support ⊆ C.outerRoof) :
    continuation930ContactSeed C W ⊆ C.outerRoof := by
  intro x hx
  rcases hx with ((hxBefore | hxW) | hxMarker) | hxContact
  · exact hbefore hxBefore
  · exact hW.vertices_roofed hxW
  · obtain ⟨p, hp, hxp⟩ := hxMarker
    exact href p hp.1 hxp
  · exact meetingVertices_subset_roof Gamma C.selectedReference
      W.vertexSet C.outerRoof href hxContact

/-- The request-specific seed is roofed whenever the selected hammock is
roofed by the public eligibility theorem. -/
theorem selected_subset_outerRoof
    (Q : AltPath Gamma.graph)
    (hW : W.IsLinkageBlueprint C.newSlice C.closedSet C.persistent)
    (hbefore : C.before ⊆ C.outerRoof)
    (href : ∀ p ∈ C.selectedReference, p.support ⊆ C.outerRoof)
    (hQ : Q.vertexSet ⊆ C.outerRoof) :
    continuation930SelectedSeed C W Q ⊆ C.outerRoof :=
  Set.union_subset (subset_outerRoof C W hW hbefore href) hQ

/-- Public terminal-outside selection for the coupled 9.30 transaction.
The chosen infinite member avoids the blueprint, all marker components, and
every complete reference component meeting the blueprint, simultaneously. -/
theorem exists_terminalOutside_member_avoiding_reserved
    {u : V}
    (hW : W.IsLinkageBlueprint C.newSlice C.closedSet C.persistent)
    (hpersistent : C.persistent ⊆ C.newSlice)
    (huterminal : u ∈ W.terminalSet) (huSlice : u ∉ C.newSlice) :
    ∃ Q : AltPath Gamma.graph,
      IsSafe C.selectedReference Q ∧ Q.initial = u ∧ Q.IsInfinite ∧
        Disjoint (Q.vertexSet \ {u})
          (continuation930ContactReserved C W) := by
  have hhammock : HasHammockCard Gamma C.selectedReference u .infinity
      (succ kappa) :=
    terminal_outside_slice_has_infinite_hammock hW hpersistent
      huterminal huSlice
  exact exists_safe_infinite_hammock_path_avoiding hhammock
    (reserved_mk_le C W hW)

/-- Public imaginary-successor selection with the same simultaneous
contact-reserved avoidance certificate. -/
theorem exists_imaginarySuccessor_member_avoiding_reserved
    {u v : V}
    (hW : W.IsLinkageBlueprint C.newSlice C.closedSet C.persistent)
    (himaginary : IsImaginaryEdge Gamma C.selectedReference kappa u v) :
    ∃ Q : AltPath Gamma.graph,
      IsSafe C.selectedReference Q ∧ Q.initial = u ∧
        HasEnd Q (.vertex v) ∧
        Disjoint (hammockInterior u (.vertex v) Q)
          (continuation930ContactReserved C W) := by
  exact exists_hammock_path_disjoint_of_mk_le himaginary
    (reserved_mk_le C W hW)

end continuation930ContactSeed

end LinkageBlueprint
end Blueprint
end Erdos599
