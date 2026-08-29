/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.Halfway930IntervalSeed

/-!
# The prior-stage form of the Assertion 9.30 request

The incoming blueprint in the 9.30--9.31 composition lives at the old club
frontier.  Its 9.30 continuation first reaches that frontier; the interval
transaction then advances from the old frontier to the new one.  In
particular it is an indexing error to assume that the incoming blueprint is
already certified at `C.newSlice`.

This file proves that the public contact request and its full closure seed do
not need that erroneous indexing.  A blueprint at `C.oldSlice` still has a
`kappa`-small carrier, and legal frontier chronology puts its old roof inside
the new roof.  Thus the same unconditional hammock choice is available, with
no bound on the ambient source.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace Blueprint
namespace LinkageBlueprint

open DirectedPath _root_.Erdos599.Alternating Ladder

universe u

variable {V : Type u}
variable {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}

private theorem deferred_strictRoof_frontier_mono
    {L : Gamma.KappaLadder (succ kappa)}
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    {a b : Ladder.Stage (succ kappa)} (hab : a ≤ b) :
    Gamma.strictRoof (L.frontier a) ⊆
      Gamma.strictRoof (L.frontier b) := by
  rcases hab.lt_or_eq with hab | rfl
  · intro x hx
    refine ⟨Gamma.roof_cut (hL.frontierChronology hab) hx.1, ?_⟩
    intro hxEssential
    have hxFrontier : x ∈ L.frontier b := by
      rw [← hL.frontiersEssential b]
      exact hxEssential
    exact Set.disjoint_left.1 (hL.strictFrontierChronology hab)
      hx hxFrontier
  · exact fun _ hx ↦ hx

namespace ClubStageGeometry

/-- The closed carrier available causally at the incoming club stage. -/
abbrev oldClosedSet
    (C : ClubStageGeometry Gamma Y kappa (succ kappa)) : Set V :=
  C.closedStage C.oldStage

/-- The old closed carrier is part of the cumulative seed before the later
club stage. -/
theorem oldClosedSet_subset_before
    (C : ClubStageGeometry Gamma Y kappa (succ kappa)) :
    C.oldClosedSet ⊆ C.before := by
  intro x hx
  exact ⟨C.oldStage, C.old_lt_new, hx⟩

end ClubStageGeometry

namespace continuation930ContactSeed

variable (C : ClubStageGeometry Gamma Y kappa (succ kappa))
variable (W : LinkageBlueprint Gamma C.selectedReference kappa)

/-- The contact-reserved carrier is small for an incoming blueprint at the
old frontier.  The proof uses only the blueprint path-cardinality field, not
the particular slice at which the blueprint is certified. -/
theorem reserved_mk_le_of_oldStageBlueprint
    (hW : W.IsLinkageBlueprint C.oldSlice C.oldClosedSet C.persistent) :
    #(continuation930ContactReserved C W) ≤ kappa := by
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
    mk_meetingVertices_le Gamma C.selectedReference W.vertexSet
      C.selectedReference_isWarp C.capacity_infinite hWvertices
  have hleft :
      #((W.vertexSet ∪
          Gamma.vertexSet
            (ladderReference.markerStarting
              (Gamma := Gamma) (L := C.ladder) (a := C.newStage))) : Set V) ≤
        kappa :=
    (Cardinal.mk_union_le _ _).trans
      (Cardinal.add_le_of_le C.capacity_infinite hWvertices hmarker)
  exact (Cardinal.mk_union_le _ _).trans
    (Cardinal.add_le_of_le C.capacity_infinite hleft hcontact)

/-- The complete source-free contact seed is small for an incoming old-stage
blueprint. -/
theorem mk_le_of_oldStageBlueprint
    (hW : W.IsLinkageBlueprint C.oldSlice C.oldClosedSet C.persistent) :
    #(continuation930ContactSeed C W) ≤ kappa := by
  have hbeforeW : #(C.before ∪ W.vertexSet : Set V) ≤ kappa :=
    (Cardinal.mk_union_le _ _).trans
      (Cardinal.add_le_of_le C.capacity_infinite C.before_card
        (W.mk_vertexSet_le_of_mk_paths_le C.capacity_infinite
          hW.card_paths))
  have hmarker :
      #(Gamma.vertexSet
          (ladderReference.markerStarting
            (Gamma := Gamma) (L := C.ladder) (a := C.newStage))) ≤
        kappa :=
    ladderReference.mk_markerStarting_vertices_le C.legal
      C.capacity_infinite C.newStage
  have hcontact :
      #(meetingVertices Gamma C.selectedReference W.vertexSet) ≤ kappa :=
    mk_meetingVertices_le Gamma C.selectedReference W.vertexSet
      C.selectedReference_isWarp C.capacity_infinite
      (W.mk_vertexSet_le_of_mk_paths_le C.capacity_infinite hW.card_paths)
  have hleft :
      #(((C.before ∪ W.vertexSet) ∪
          Gamma.vertexSet
            (ladderReference.markerStarting
              (Gamma := Gamma) (L := C.ladder) (a := C.newStage))) : Set V) ≤
        kappa :=
    (Cardinal.mk_union_le _ _).trans
      (Cardinal.add_le_of_le C.capacity_infinite hbeforeW hmarker)
  exact (Cardinal.mk_union_le _ _).trans
    (Cardinal.add_le_of_le C.capacity_infinite hleft hcontact)

/-- Adding the selected alternating member preserves the bound in the
prior-stage form as well. -/
theorem selected_mk_le_of_oldStageBlueprint
    (Q : AltPath Gamma.graph)
    (hW : W.IsLinkageBlueprint C.oldSlice C.oldClosedSet C.persistent) :
    #(continuation930SelectedSeed C W Q) ≤ kappa := by
  exact (Cardinal.mk_union_le _ _).trans
    (Cardinal.add_le_of_le C.capacity_infinite
      (mk_le_of_oldStageBlueprint C W hW)
      ((altPath_vertexSet_countable Q).le_aleph0.trans
        C.capacity_infinite))

/-- Legal frontier chronology transports the incoming blueprint carrier
from the old roof into the roof of the transaction's later frontier. -/
theorem subset_outerRoof_of_oldStageBlueprint
    (hW : W.IsLinkageBlueprint C.oldSlice C.oldClosedSet C.persistent)
    (hbefore : C.before ⊆ C.outerRoof)
    (href : ∀ p ∈ C.selectedReference, p.support ⊆ C.outerRoof) :
    continuation930ContactSeed C W ⊆ C.outerRoof := by
  intro x hx
  rcases hx with ((hxBefore | hxW) | hxMarker) | hxContact
  · exact hbefore hxBefore
  · exact Gamma.roof_cut (C.legal.frontierChronology C.old_lt_new)
      (hW.vertices_roofed hxW)
  · obtain ⟨p, hp, hxp⟩ := hxMarker
    exact href p hp.1 hxp
  · exact meetingVertices_subset_roof Gamma C.selectedReference
      W.vertexSet C.outerRoof href hxContact

end continuation930ContactSeed

/-- The branch output with its boundary indexed at the incoming, old club
frontier.  Keeping this as a separate type prevents an old-slice witness
from being silently used as a new-slice witness. -/
inductive PriorContact930Request
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (W : LinkageBlueprint Gamma C.selectedReference kappa)
    (u : V) : Type u
  | identity
      (at_oldSlice : u ∈ C.oldSlice)
  | terminalOutside
      (whole_terminal : u ∈ W.terminalSet)
      (outside_oldSlice : u ∉ C.oldSlice)
      (path : AltPath Gamma.graph)
      (safe : IsSafe C.selectedReference path)
      (starts : path.initial = u)
      (infinite : path.IsInfinite)
      (avoids : Disjoint (path.vertexSet \ {u})
        (continuation930ContactReserved C W))
  | imaginarySuccessor
      (outside_oldSlice : u ∉ C.oldSlice)
      (v : V)
      (edge_mem : (u, v) ∈ W.edgeSet)
      (imaginary : IsImaginaryEdge Gamma C.selectedReference kappa u v)
      (path : AltPath Gamma.graph)
      (safe : IsSafe C.selectedReference path)
      (starts : path.initial = u)
      (ends : HasEnd path (.vertex v))
      (avoids : Disjoint (hammockInterior u (.vertex v) path)
        (continuation930ContactReserved C W))

namespace PriorContact930Request

variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
variable {W : LinkageBlueprint Gamma C.selectedReference kappa}
variable {u : V}

/-- The exact source-free closure seed of a prior-stage request. -/
def seed (R : PriorContact930Request C W u) : Set V :=
  match R with
  | .identity .. => continuation930ContactSeed C W
  | .terminalOutside _ _ Q .. => continuation930SelectedSeed C W Q
  | .imaginarySuccessor _ _ _ _ Q .. => continuation930SelectedSeed C W Q

/-- Endpoint eligibility needed to roof a nontrivial selected hammock. -/
def IsClubEligible (R : PriorContact930Request C W u) : Prop :=
  match R with
  | .identity .. => True
  | .terminalOutside .. =>
      HammockEligible C.before C.innerRoof C.outerRoof u .infinity
  | .imaginarySuccessor _ v .. =>
      HammockEligible C.before C.innerRoof C.outerRoof u (.vertex v)

/-- The base public contact bookkeeping is retained in every branch. -/
theorem contactSeed_subset (R : PriorContact930Request C W u) :
    continuation930ContactSeed C W ⊆ R.seed := by
  cases R <;> simp only [seed, continuation930SelectedSeed]
  · exact Set.Subset.rfl
  · exact Set.subset_union_left
  · exact Set.subset_union_left

/-- Branch-uniform cardinality of the selected 9.30 seed when the incoming
blueprint lives at the old club frontier. -/
theorem seed_mk_le
    (R : PriorContact930Request C W u)
    (hW : W.IsLinkageBlueprint C.oldSlice C.oldClosedSet C.persistent) :
    #R.seed ≤ kappa := by
  cases R with
  | identity =>
      exact continuation930ContactSeed.mk_le_of_oldStageBlueprint C W hW
  | terminalOutside _ _ Q =>
      exact continuation930ContactSeed.selected_mk_le_of_oldStageBlueprint
        C W Q hW
  | imaginarySuccessor _ _ _ _ Q =>
      exact continuation930ContactSeed.selected_mk_le_of_oldStageBlueprint
        C W Q hW

/-- Eligibility roofs the selected hammock while chronology roofs the old
blueprint.  Hence every branch seed is contained in the later roof. -/
theorem seed_subset_outerRoof
    (R : PriorContact930Request C W u)
    (hW : W.IsLinkageBlueprint C.oldSlice C.oldClosedSet C.persistent)
    (hbefore : C.before ⊆ C.outerRoof)
    (href : ∀ p ∈ C.selectedReference, p.support ⊆ C.outerRoof)
    (hSafeRoof : EligibleHammocksContainedInRoof Gamma C.selectedReference
      C.before C.innerRoof C.outerRoof)
    (heligible : R.IsClubEligible) :
    R.seed ⊆ C.outerRoof := by
  cases R with
  | identity =>
      exact continuation930ContactSeed.subset_outerRoof_of_oldStageBlueprint
        C W hW hbefore href
  | terminalOutside _ _ Q hsafe hstart hinfinite =>
      exact Set.union_subset
        (continuation930ContactSeed.subset_outerRoof_of_oldStageBlueprint
          C W hW hbefore href)
        (hSafeRoof Q hsafe)
  | imaginarySuccessor _ v _ _ Q hsafe hstart hend =>
      exact Set.union_subset
        (continuation930ContactSeed.subset_outerRoof_of_oldStageBlueprint
          C W hW hbefore href)
        (hSafeRoof Q hsafe)

end PriorContact930Request

/-- The public 9.30 branch selection with the incoming blueprint at the old
club frontier.  This is the indexing needed before an old-to-new interval
transaction can be attached. -/
theorem exists_contact930Request_of_oldStageBlueprint
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (W : LinkageBlueprint Gamma C.selectedReference kappa)
    {u : V}
    (hW : W.IsLinkageBlueprint C.oldSlice C.oldClosedSet C.persistent)
    (hpersistent : C.persistent ⊆ C.oldSlice)
    (hu : u ∈ W.realPart.terminals) :
    Nonempty (PriorContact930Request C W u) := by
  by_cases huSlice : u ∈ C.oldSlice
  · exact ⟨PriorContact930Request.identity huSlice⟩
  · rcases real_terminal_is_terminal_or_has_imaginary_edge_mem hu with
        huterminal | ⟨v, huv, himaginary⟩
    · have hhammock : HasHammockCard Gamma C.selectedReference u .infinity
          (succ kappa) :=
        terminal_outside_slice_has_infinite_hammock hW hpersistent
          huterminal huSlice
      obtain ⟨Q, hsafe, hstart, hinfinite, havoid⟩ :=
        exists_safe_infinite_hammock_path_avoiding hhammock
          (continuation930ContactSeed.reserved_mk_le_of_oldStageBlueprint
            C W hW)
      exact ⟨PriorContact930Request.terminalOutside huterminal huSlice Q
        hsafe hstart hinfinite havoid⟩
    · obtain ⟨Q, hsafe, hstart, hend, havoid⟩ :=
        exists_hammock_path_disjoint_of_mk_le himaginary
          (continuation930ContactSeed.reserved_mk_le_of_oldStageBlueprint
            C W hW)
      exact ⟨PriorContact930Request.imaginarySuccessor huSlice v huv himaginary Q
        hsafe hstart hend havoid⟩

/-- The causal old-stage invariant supplies the complete club eligibility
certificate.  No separate endpoint-location callback is needed: the old
closed carrier is part of `before`, and a scheduled vertex genuinely outside
the old frontier lies in its strict roof and hence in the later strict roof. -/
theorem exists_clubEligibleContact930Request_of_oldStageBlueprint
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (W : LinkageBlueprint Gamma C.selectedReference kappa)
    {u : V}
    (hW : W.IsLinkageBlueprint C.oldSlice C.oldClosedSet C.persistent)
    (hpersistent : C.persistent ⊆ C.oldSlice)
    (hu : u ∈ W.realPart.terminals) :
    ∃ R : PriorContact930Request C W u, R.IsClubEligible := by
  obtain ⟨R⟩ := exists_contact930Request_of_oldStageBlueprint
    C W hW hpersistent hu
  refine ⟨R, ?_⟩
  cases R with
  | identity => trivial
  | terminalOutside huterminal huSlice Q hsafe hstart hinfinite havoid =>
      have huBefore : u ∈ C.before :=
        C.oldClosedSet_subset_before (hW.vertices_closed hu.1)
      have huStrictOld : u ∈ Gamma.strictRoof C.oldSlice := by
        refine ⟨hW.vertices_roofed hu.1, ?_⟩
        simpa only [C.legal.frontiersEssential C.oldStage] using huSlice
      exact ⟨⟨huBefore,
        deferred_strictRoof_frontier_mono C.legal
          C.old_lt_new.le huStrictOld⟩,
          trivial⟩
  | imaginarySuccessor huOutside v huv himaginary Q hsafe hstart hend havoid =>
      have huBefore : u ∈ C.before :=
        C.oldClosedSet_subset_before (hW.vertices_closed hu.1)
      have huStrictOld : u ∈ Gamma.strictRoof C.oldSlice := by
        refine ⟨hW.vertices_roofed hu.1, ?_⟩
        simpa only [C.legal.frontiersEssential C.oldStage] using huOutside
      have hvW : v ∈ W.vertexSet := by
        rcases Set.mem_iUnion.1 huv with ⟨p, huv⟩
        rcases Set.mem_iUnion.1 huv with ⟨hpW, hpedge⟩
        exact ⟨p, hpW, (p.edgeSet_subset_support_prod hpedge).2⟩
      have hvBefore : v ∈ C.before :=
        C.oldClosedSet_subset_before (hW.vertices_closed hvW)
      have hvOuter : v ∈ C.outerRoof :=
        Gamma.roof_cut (C.legal.frontierChronology C.old_lt_new)
          (hW.vertices_roofed hvW)
      exact ⟨⟨huBefore,
        deferred_strictRoof_frontier_mono C.legal
          C.old_lt_new.le huStrictOld⟩,
          hvBefore, hvOuter⟩

end LinkageBlueprint
end Blueprint
end Erdos599
