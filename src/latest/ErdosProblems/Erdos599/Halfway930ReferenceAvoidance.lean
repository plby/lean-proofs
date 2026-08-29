/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayLadderReference
import ErdosProblems.Erdos599.HalfwayContinuationRepair

/-!
# Small-reference avoidance for Assertion 9.30

At a stage of the successor-cardinal ladder the selected reference has two
parts.  The marker-starting part has cardinal at most `kappa` by the hanging
vertex estimate, while the source-starting part injects into the ambient
source because the reference is a warp.  Consequently its whole carrier is
small.  A member of a `kappa^+` hammock can therefore be selected away from
both the current blueprint and the complete reference carrier.

This is the contact-safe selection needed before applying any of the checked
global switching/orientation machinery: avoiding only the current blueprint
does not rule out unrecorded forward contacts with the reference warp.
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

/-- An infinite safe alternating path must use a nontrivial backward
reference fragment away from its initial vertex.  Thus it cannot have its
whole noninitial carrier disjoint from the reference warp. -/
theorem IsSafe.not_infinite_of_noninitial_disjoint_reference
    {Q : AltPath Gamma.graph} {u : V}
    (hsafe : IsSafe Y Q) (hinitial : Q.initial = u)
    (hdisjoint : Disjoint (Q.vertexSet \ {u}) (Gamma.vertexSet Y)) :
    ¬Q.IsInfinite := by
  classical
  intro hinfinite
  cases Q with
  | trivial x => simp [AltPath.IsInfinite] at hinfinite
  | finite F => simp [AltPath.IsInfinite] at hinfinite
  | infinite R =>
      let i : Nat := if (R.link 0).direction = .backward then 0 else 1
      have hidir : (R.link i).direction = .backward := by
        dsimp [i]
        split
        next h => exact h
        next h =>
          have halt := R.alternates 0
          cases hzero : (R.link 0).direction with
          | backward => exact False.elim (h hzero)
          | forward =>
              cases hone : (R.link 1).direction with
              | forward => exact False.elim (halt (hzero.trans hone.symm))
              | backward => exact rfl
      have hlink : R.link i ∈ (AltPath.infinite R).links := by
        exact ⟨i, rfl⟩
      obtain ⟨p, hpY, hsub⟩ :=
        hsafe.isAlternating.2.1 (R.link i) hlink hidir
      let x : V := if (R.link i).path.start = u then
        (R.link i).path.finish else (R.link i).path.start
      have hxu : x ≠ u := by
        dsimp [x]
        split
        next hstart =>
          intro hfinish
          exact (R.link i).nontrivial (hstart.trans hfinish.symm)
        next hstart => exact hstart
      have hxlink : x ∈ (R.link i).path.support := by
        dsimp [x]
        split
        · exact (R.link i).path.finish_mem_support
        · exact (R.link i).path.start_mem_support
      have hxQ : x ∈ (AltPath.infinite R).vertexSet := by
        exact Set.mem_iUnion.2 ⟨i, hxlink⟩
      have hxY : x ∈ Gamma.vertexSet Y := by
        exact ⟨p, hpY, hsub.1 hxlink⟩
      exact Set.disjoint_left.1 hdisjoint
        ⟨hxQ, by simpa [hammockEndpoints] using hxu⟩ hxY

namespace ladderReference

variable {L : Gamma.KappaLadder (succ kappa)}
variable {a : Ladder.Stage (succ kappa)}

/-- The selected reference is the union of its source-starting and
marker-starting parts. -/
theorem sourceStarting_union_markerStarting :
    sourceStarting (Gamma := Gamma) (L := L) (a := a) ∪
        markerStarting (Gamma := Gamma) (L := L) (a := a) =
      ladderReference L a := by
  ext p
  simp only [sourceStarting, markerStarting, Set.mem_union,
    Set.mem_ofPred_eq]
  constructor
  · rintro (hp | hp) <;> exact hp.1
  · intro hp
    by_cases hs : p.initial ∈ Gamma.source
    · exact Or.inl ⟨hp, hs⟩
    · exact Or.inr ⟨hp, hs⟩

/-- Source-starting reference members inject into the ambient source by
their initial vertex. -/
theorem mk_sourceStarting_le_source
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L) :
    #(sourceStarting (Gamma := Gamma) (L := L) (a := a)) ≤
      #Gamma.source := by
  let f : sourceStarting (Gamma := Gamma) (L := L) (a := a) →
      Gamma.source := fun p ↦ ⟨p.1.initial, p.2.2⟩
  apply Cardinal.mk_le_of_injective (f := f)
  intro p q hpq
  apply Subtype.ext
  apply DWeb.IsWarp.eq_of_mem_support (isWarp hL) p.2.1 q.2.1
  · exact p.1.initial_mem_support
  · have hinitial : p.1.initial = q.1.initial :=
      congrArg Subtype.val hpq
    rw [hinitial]
    exact q.1.initial_mem_support

/-- The full selected reference has cardinal at most `kappa` whenever the
ambient source does. -/
theorem mk_ladderReference_le
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    (hkappa : aleph0 ≤ kappa)
    (hsource : #Gamma.source ≤ kappa) :
    #(ladderReference L a) ≤ kappa := by
  rw [← sourceStarting_union_markerStarting]
  exact (Cardinal.mk_union_le _ _).trans
    (Cardinal.add_le_of_le hkappa
      ((mk_sourceStarting_le_source hL).trans hsource)
      (mk_markerStarting_le hL a))

/-- The whole vertex carrier of the selected reference is small as well. -/
theorem mk_ladderReference_vertexSet_le
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    (hkappa : aleph0 ≤ kappa)
    (hsource : #Gamma.source ≤ kappa) :
    #(Gamma.vertexSet (ladderReference L a)) ≤ kappa := by
  exact CardinalInduction.HalfwayFrontierHeight.mk_vertexSet_le_of_mk_family_le
    hkappa (ladderReference L a)
      (mk_ladderReference_le hL hkappa hsource)

end ladderReference

namespace ClubStageGeometry

variable (C : ClubStageGeometry Gamma Y kappa (succ kappa))

/-- Stage-specialized cardinal bound for the selected reference carrier. -/
theorem mk_selectedReference_vertexSet_le
    (hsource : #Gamma.source ≤ kappa) :
    #(Gamma.vertexSet C.selectedReference) ≤ kappa := by
  exact ladderReference.mk_ladderReference_vertexSet_le C.legal
    C.capacity_infinite hsource

end ClubStageGeometry

/-- An infinity-hammock member avoiding both the current blueprint and the
entire selected reference carrier. -/
theorem exists_safe_infinite_hammock_path_avoiding_blueprint_reference
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (W : LinkageBlueprint Gamma C.selectedReference kappa)
    {u : V}
    (hsource : #Gamma.source ≤ kappa)
    (hW : W.IsLinkageBlueprint C.newSlice C.closedSet C.persistent)
    (hhammock : HasHammockCard Gamma C.selectedReference u .infinity
      (succ kappa)) :
    ∃ Q : AltPath Gamma.graph,
      IsSafe C.selectedReference Q ∧ Q.initial = u ∧ Q.IsInfinite ∧
        Disjoint (Q.vertexSet \ {u}) W.vertexSet ∧
        Disjoint (Q.vertexSet \ {u})
          (Gamma.vertexSet C.selectedReference) := by
  have hWvertices : #W.vertexSet ≤ kappa :=
    W.mk_vertexSet_le_of_mk_paths_le C.capacity_infinite
      hW.card_paths
  have hrefVertices : #(Gamma.vertexSet C.selectedReference) ≤ kappa :=
    C.mk_selectedReference_vertexSet_le hsource
  let reserved : Set V :=
    W.vertexSet ∪ (Gamma.vertexSet C.selectedReference)
  have hunion : #reserved ≤ kappa :=
    (Cardinal.mk_union_le _ _).trans
      (Cardinal.add_le_of_le C.capacity_infinite hWvertices hrefVertices)
  obtain ⟨Q, hsafe, hinitial, hinfinite, havoid⟩ :=
    exists_safe_infinite_hammock_path_avoiding hhammock hunion
  refine ⟨Q, hsafe, hinitial, hinfinite, ?_, ?_⟩
  · exact havoid.mono_right (by
      intro x hx
      exact Set.mem_union_left _ hx)
  · exact havoid.mono_right (by
      intro x hx
      exact Set.mem_union_right _ hx)

/-- Finite-endpoint version of the same contact-safe selection. -/
theorem exists_hammock_path_avoiding_blueprint_reference
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (W : LinkageBlueprint Gamma C.selectedReference kappa)
    {u v : V}
    (hsource : #Gamma.source ≤ kappa)
    (hW : W.IsLinkageBlueprint C.newSlice C.closedSet C.persistent)
    (hhammock : HasHammockCard Gamma C.selectedReference u (.vertex v)
      (succ kappa)) :
    ∃ Q : AltPath Gamma.graph,
      IsSafe C.selectedReference Q ∧ Q.initial = u ∧
        HasEnd Q (.vertex v) ∧
        Disjoint (hammockInterior u (.vertex v) Q) W.vertexSet ∧
        Disjoint (hammockInterior u (.vertex v) Q)
          (Gamma.vertexSet C.selectedReference) := by
  have hWvertices : #W.vertexSet ≤ kappa :=
    W.mk_vertexSet_le_of_mk_paths_le C.capacity_infinite hW.card_paths
  have hrefVertices : #(Gamma.vertexSet C.selectedReference) ≤ kappa :=
    C.mk_selectedReference_vertexSet_le hsource
  let reserved : Set V :=
    W.vertexSet ∪ (Gamma.vertexSet C.selectedReference)
  have hunion : #reserved ≤ kappa :=
    (Cardinal.mk_union_le _ _).trans
      (Cardinal.add_le_of_le C.capacity_infinite hWvertices hrefVertices)
  obtain ⟨Q, hsafe, hinitial, hend, havoid⟩ :=
    exists_hammock_path_disjoint_of_mk_le hhammock hunion
  refine ⟨Q, hsafe, hinitial, hend, ?_, ?_⟩
  · exact havoid.mono_right (by
      intro x hx
      exact Set.mem_union_left _ hx)
  · exact havoid.mono_right (by
      intro x hx
      exact Set.mem_union_right _ hx)

/-- A strong finite-endpoint hammock has a nondegenerate member with the
same simultaneous avoidance certificate. -/
theorem exists_nondegenerate_hammock_path_avoiding_blueprint_reference
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (W : LinkageBlueprint Gamma C.selectedReference kappa)
    {u v : V}
    (hsource : #Gamma.source ≤ kappa)
    (hW : W.IsLinkageBlueprint C.newSlice C.closedSet C.persistent)
    (hhammock : HasNondegenerateHammockCard Gamma C.selectedReference
      u (.vertex v) (succ kappa)) :
    ∃ H : Set (AltPath Gamma.graph), ∃ Q : AltPath Gamma.graph,
      NondegenerateHammock Gamma C.selectedReference u (.vertex v) H ∧
        #H = succ kappa ∧ Q ∈ H ∧
        IsSafe C.selectedReference Q ∧ Q.initial = u ∧
        HasEnd Q (.vertex v) ∧
        ¬IsDegenerate C.selectedReference Q (.vertex v) ∧
        Disjoint (hammockInterior u (.vertex v) Q) W.vertexSet ∧
        Disjoint (hammockInterior u (.vertex v) Q)
          (Gamma.vertexSet C.selectedReference) := by
  have hWvertices : #W.vertexSet ≤ kappa :=
    W.mk_vertexSet_le_of_mk_paths_le C.capacity_infinite hW.card_paths
  have hrefVertices : #(Gamma.vertexSet C.selectedReference) ≤ kappa :=
    C.mk_selectedReference_vertexSet_le hsource
  let reserved : Set V :=
    W.vertexSet ∪ (Gamma.vertexSet C.selectedReference)
  have hunion : #reserved ≤ kappa :=
    (Cardinal.mk_union_le _ _).trans
      (Cardinal.add_le_of_le C.capacity_infinite hWvertices hrefVertices)
  obtain ⟨H, Q, hH, hHcard, hQH, hsafe, hinitial, hend,
      hnondegenerate, havoid⟩ :=
    exists_nondegenerate_hammock_path_disjoint_of_mk_le hhammock hunion
  refine ⟨H, Q, hH, hHcard, hQH, hsafe, hinitial, hend,
    hnondegenerate, ?_, ?_⟩
  · exact havoid.mono_right (by
      intro x hx
      exact Set.mem_union_left _ hx)
  · exact havoid.mono_right (by
      intro x hx
      exact Set.mem_union_right _ hx)

/-! ## Public contact-carrier avoidance

The ambient source can be larger than `kappa`, so the complete selected
reference need not be small.  The part relevant to a coupled replacement is
smaller: since the selected reference is a warp, all reference components
which touch a `kappa`-sized blueprint inject into its carrier.  Their complete
vertex union therefore still has cardinal at most `kappa`. -/

/-- The carrier of all selected-reference components which touch the current
blueprint has cardinal at most `kappa`.  This statement has no cardinal bound
on the ambient source. -/
theorem mk_blueprintMeetingReferenceVertices_le
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (W : LinkageBlueprint Gamma C.selectedReference kappa)
    (hW : W.IsLinkageBlueprint C.newSlice C.closedSet C.persistent) :
    #(meetingVertices Gamma C.selectedReference W.vertexSet) ≤ kappa := by
  exact mk_meetingVertices_le Gamma C.selectedReference W.vertexSet
    C.selectedReference_isWarp C.capacity_infinite
      (W.mk_vertexSet_le_of_mk_paths_le C.capacity_infinite hW.card_paths)

/-- A finite hammock member avoiding both the blueprint and every complete
reference component which meets it.  Unlike complete-reference avoidance,
this is available in the public half-way context with an arbitrarily large
ambient source. -/
theorem exists_hammock_path_avoiding_blueprint_contactReference
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (W : LinkageBlueprint Gamma C.selectedReference kappa)
    {u v : V}
    (hW : W.IsLinkageBlueprint C.newSlice C.closedSet C.persistent)
    (hhammock : HasHammockCard Gamma C.selectedReference u (.vertex v)
      (succ kappa)) :
    ∃ Q : AltPath Gamma.graph,
      IsSafe C.selectedReference Q ∧ Q.initial = u ∧
        HasEnd Q (.vertex v) ∧
        Disjoint (hammockInterior u (.vertex v) Q) W.vertexSet ∧
        Disjoint (hammockInterior u (.vertex v) Q)
          (meetingVertices Gamma C.selectedReference W.vertexSet) := by
  let reserved : Set V := W.vertexSet ∪
    meetingVertices Gamma C.selectedReference W.vertexSet
  have hWvertices : #W.vertexSet ≤ kappa :=
    W.mk_vertexSet_le_of_mk_paths_le C.capacity_infinite hW.card_paths
  have hcontact :
      #(meetingVertices Gamma C.selectedReference W.vertexSet) ≤ kappa :=
    mk_blueprintMeetingReferenceVertices_le C W hW
  have hreserved : #reserved ≤ kappa :=
    (Cardinal.mk_union_le _ _).trans
      (Cardinal.add_le_of_le C.capacity_infinite hWvertices hcontact)
  obtain ⟨Q, hsafe, hinitial, hend, havoid⟩ :=
    exists_hammock_path_disjoint_of_mk_le hhammock hreserved
  refine ⟨Q, hsafe, hinitial, hend, ?_, ?_⟩
  · exact havoid.mono_right (by
      intro x hx
      exact Set.mem_union_left _ hx)
  · exact havoid.mono_right (by
      intro x hx
      exact Set.mem_union_right _ hx)

/-- Infinity-endpoint form of public contact-carrier avoidance. -/
theorem exists_safe_infinite_hammock_path_avoiding_blueprint_contactReference
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (W : LinkageBlueprint Gamma C.selectedReference kappa)
    {u : V}
    (hW : W.IsLinkageBlueprint C.newSlice C.closedSet C.persistent)
    (hhammock : HasHammockCard Gamma C.selectedReference u .infinity
      (succ kappa)) :
    ∃ Q : AltPath Gamma.graph,
      IsSafe C.selectedReference Q ∧ Q.initial = u ∧ Q.IsInfinite ∧
        Disjoint (Q.vertexSet \ {u}) W.vertexSet ∧
        Disjoint (Q.vertexSet \ {u})
          (meetingVertices Gamma C.selectedReference W.vertexSet) := by
  let reserved : Set V := W.vertexSet ∪
    meetingVertices Gamma C.selectedReference W.vertexSet
  have hWvertices : #W.vertexSet ≤ kappa :=
    W.mk_vertexSet_le_of_mk_paths_le C.capacity_infinite hW.card_paths
  have hcontact :
      #(meetingVertices Gamma C.selectedReference W.vertexSet) ≤ kappa :=
    mk_blueprintMeetingReferenceVertices_le C W hW
  have hreserved : #reserved ≤ kappa :=
    (Cardinal.mk_union_le _ _).trans
      (Cardinal.add_le_of_le C.capacity_infinite hWvertices hcontact)
  obtain ⟨Q, hsafe, hinitial, hinfinite, havoid⟩ :=
    exists_safe_infinite_hammock_path_avoiding hhammock hreserved
  refine ⟨Q, hsafe, hinitial, hinfinite, ?_, ?_⟩
  · exact havoid.mono_right (by
      intro x hx
      exact Set.mem_union_left _ hx)
  · exact havoid.mono_right (by
      intro x hx
      exact Set.mem_union_right _ hx)

/-- The public terminal-outside branch of Assertion 9.30, through the last
step that precedes the coupled whole-family replacement.  Blueprint condition
(6) constructs the required large hammock; the preceding theorem performs
the sound simultaneous avoidance selection. -/
theorem exists_terminalOutside_contactSafeHammockMember
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (W : LinkageBlueprint Gamma C.selectedReference kappa)
    {u : V}
    (hW : W.IsLinkageBlueprint C.newSlice C.closedSet C.persistent)
    (hpersistent : C.persistent ⊆ C.newSlice)
    (huterminal : u ∈ W.terminalSet) (huSlice : u ∉ C.newSlice) :
    ∃ Q : AltPath Gamma.graph,
      IsSafe C.selectedReference Q ∧ Q.initial = u ∧ Q.IsInfinite ∧
        Disjoint (Q.vertexSet \ {u}) W.vertexSet ∧
        Disjoint (Q.vertexSet \ {u})
          (meetingVertices Gamma C.selectedReference W.vertexSet) := by
  exact exists_safe_infinite_hammock_path_avoiding_blueprint_contactReference
    C W hW (terminal_outside_slice_has_infinite_hammock hW hpersistent
      huterminal huSlice)

/-- The public imaginary-successor branch of Assertion 9.30, again retaining
the stronger contact-carrier avoidance needed by a whole-family compiler. -/
theorem exists_imaginarySuccessor_contactSafeHammockMember
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (W : LinkageBlueprint Gamma C.selectedReference kappa)
    {u v : V}
    (hW : W.IsLinkageBlueprint C.newSlice C.closedSet C.persistent)
    (himaginary : IsImaginaryEdge Gamma C.selectedReference kappa u v) :
    ∃ Q : AltPath Gamma.graph,
      IsSafe C.selectedReference Q ∧ Q.initial = u ∧
        HasEnd Q (.vertex v) ∧
        Disjoint (hammockInterior u (.vertex v) Q) W.vertexSet ∧
        Disjoint (hammockInterior u (.vertex v) Q)
          (meetingVertices Gamma C.selectedReference W.vertexSet) := by
  exact exists_hammock_path_avoiding_blueprint_contactReference
    C W hW himaginary

/-- With the actual small selected reference, condition (6) cannot leave a
whole-blueprint terminal outside the current slice: its required infinity
hammock would have a member avoiding the reference carrier, contradicting
the preceding structural fact about infinite alternating paths. -/
theorem terminal_mem_newSlice_of_selectedReference_small
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (W : LinkageBlueprint Gamma C.selectedReference kappa)
    {u : V}
    (hsource : #Gamma.source ≤ kappa)
    (hW : W.IsLinkageBlueprint C.newSlice C.closedSet C.persistent)
    (hpersistent : C.persistent ⊆ C.newSlice)
    (huterminal : u ∈ W.terminalSet) :
    u ∈ C.newSlice := by
  by_contra huSlice
  have hhammock : HasHammockCard Gamma C.selectedReference u .infinity
      (succ kappa) :=
    terminal_outside_slice_has_infinite_hammock hW hpersistent
      huterminal huSlice
  obtain ⟨Q, hsafe, hinitial, hinfinite, _hWavoid, hrefAvoid⟩ :=
    exists_safe_infinite_hammock_path_avoiding_blueprint_reference
      C W hsource hW hhammock
  exact IsSafe.not_infinite_of_noninitial_disjoint_reference hsafe hinitial
    hrefAvoid hinfinite

/-- The terminal branch of Assertion 9.30 is therefore always the identity
branch for the actual selected reference. -/
theorem continuation930_of_selectedReference_terminal
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (W : LinkageBlueprint Gamma C.selectedReference kappa)
    {u : V}
    (hsource : #Gamma.source ≤ kappa)
    (hW : W.IsLinkageBlueprint C.newSlice C.closedSet C.persistent)
    (hpersistent : C.persistent ⊆ C.newSlice)
    (hureal : u ∈ W.realPart.terminals)
    (huterminal : u ∈ W.terminalSet) :
    Continuation930 W W W u u C.newSlice Gamma.target := by
  exact continuation930_of_terminal_mem_slice hureal huterminal
    (terminal_mem_newSlice_of_selectedReference_small C W hsource hW
      hpersistent huterminal)

/-- The actual terminal-outside compiler required by Assertion 9.30.

For the selected ladder reference its antecedent is contradictory: condition
(6) supplies an infinity hammock, while small-reference avoidance supplies an
infinite safe member disjoint from the reference carrier.  Thus this is a
genuine construction of the compiler proposition, with no replacement oracle
or switching hypothesis. -/
theorem terminalOutsideHammockReplacementCompiler_selectedReference
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (hsource : #Gamma.source ≤ kappa) :
    TerminalOutsideHammockReplacementCompiler
      (Gamma := Gamma) (Y := C.selectedReference) (kappa := kappa)
      C.newSlice C.closedSet C.persistent := by
  intro W u Q hW hpersistent _hureal huterminal huSlice
    _hsafe _hinitial _hinfinite _havoid
  exact False.elim <|
    huSlice (terminal_mem_newSlice_of_selectedReference_small C W hsource
      hW hpersistent huterminal)

end LinkageBlueprint
end Blueprint
end Erdos599
