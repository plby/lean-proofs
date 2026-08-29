/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.DeferredGroundingSelectedStartingLastContact
import ErdosProblems.Erdos599.TerminalContactSwitchGeometry
import ErdosProblems.Erdos599.TerminalContactSwitchInfinite
import ErdosProblems.Erdos599.TerminalContactSwitchRooting
import ErdosProblems.Erdos599.DeferredGroundingReservedSourceFirst
import ErdosProblems.Erdos599.GroundingDynamicComponentExchange

/-!
# Truncating the selected starting record at its final contact

The last-contact repair becomes an actual reference warp by replacing the
selected starting record with its retained finite source prefix.  This keeps
the initial set unchanged, makes the normalized selected suffix start at a
literal reference terminal, and preserves all its backward links.  The last
fact uses the no-return certificate: a nontrivial backward link cannot be a
fragment of the removed record.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace DWeb
namespace KappaLadder
namespace Deferred

open _root_.Erdos599.DirectedPath
open Alternating PopularAuxiliary.Input
open PopularGroundingBridge GroundingSimultaneousDecode GroundingErasedDecode

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}
variable {L : Gamma.KappaLadder kappa} {hL : IsKappaHindrance L}
variable {S : Popular.PopularSeparator (popularAuxiliaryIndexed L hL)}

local notation "J" => popularAuxiliaryInput L hL.legal
local notation "U" => popularAuxiliaryIndexed L hL
local notation "K" => reservedGroundedCarrierControls L hL S

namespace ReservedStrongSelectedStartingLastContact

variable {r : Request (popularAuxiliaryInput L hL.legal) S.cut}

/-- Replace the selected starting record by its retained prefix through the
final selected-route contact. -/
def truncatedWarp
    (X : ReservedStrongSelectedStartingLastContact
      (L := L) (hL := hL) (S := S) r) : Set Gamma.DPath :=
  insert (.inl X.oldPrefix : Gamma.DPath)
    (L.limitWarp \ {(reservedStrongSelectedStartingRecord r).record})

/-- The literal prefix replacement remains a warp. -/
theorem truncatedWarp_isWarp
    (X : ReservedStrongSelectedStartingLastContact
      (L := L) (hL := hL) (S := S) r) :
    Gamma.IsWarp X.truncatedWarp := by
  let record := (reservedStrongSelectedStartingRecord r).record
  have hwarp : Gamma.IsWarp L.limitWarp := by
    simpa only [popularAuxiliaryInput, limitWarp] using
      (popularAuxiliaryInput L hL.legal).ladder.disjoint
  have hrecord : record ∈ L.limitWarp :=
    (reservedStrongSelectedStartingRecord r).record_mem_ladder
  apply DWeb.IsWarp.insert_finite_of_disjoint Gamma
    (DWeb.IsWarp.sdiff_singleton Gamma hwarp record) X.oldPrefix
  rw [Set.disjoint_left]
  intro x hxPrefix hxRest
  obtain ⟨p, hpRest, hxp⟩ := hxRest
  have hne : record ≠ p := by
    intro hrp
    subst p
    exact hpRest.2 (Set.mem_singleton record)
  exact Set.disjoint_left.mp (hwarp hrecord hpRest.1 hne)
    (X.oldPrefix_support hxPrefix) hxp

/-- Truncation keeps exactly the old limiting-warp initial set. -/
theorem truncatedWarp_initialSet
    (X : ReservedStrongSelectedStartingLastContact
      (L := L) (hL := hL) (S := S) r) :
    Gamma.initialSet X.truncatedWarp = Gamma.initialSet L.limitWarp := by
  let record := (reservedStrongSelectedStartingRecord r).record
  have hwarp : Gamma.IsWarp L.limitWarp := by
    simpa only [popularAuxiliaryInput, limitWarp] using
      (popularAuxiliaryInput L hL.legal).ladder.disjoint
  have hrecord : record ∈ L.limitWarp :=
    (reservedStrongSelectedStartingRecord r).record_mem_ladder
  change Gamma.initialSet
      (insert (.inl X.oldPrefix : Gamma.DPath)
        (L.limitWarp \ {record})) = _
  rw [Gamma.initialSet_insert_finite,
    DWeb.IsWarp.initialSet_sdiff_singleton Gamma hwarp hrecord,
    X.oldPrefix_start]
  ext x
  simp only [Set.mem_insert_iff, Set.mem_diff, Set.mem_singleton_iff]
  constructor
  · rintro (rfl | hx)
    · exact ⟨record, hrecord, rfl⟩
    · exact hx.1
  · intro hx
    by_cases hxeq : x = record.initial
    · exact Or.inl hxeq
    · exact Or.inr ⟨hx, hxeq⟩

/-- The splice point is a literal terminal of the truncated warp and is the
initial vertex of the normalized selected suffix. -/
theorem normalizedSuffix_initial_mem_terminalFrontier
    (X : ReservedStrongSelectedStartingLastContact
      (L := L) (hL := hL) (S := S) r) :
    X.normalizedSuffix.path.initial ∈
      Gamma.terminalFrontier X.truncatedWarp := by
  rw [X.normalizedSuffix_initial]
  exact ⟨.inl X.oldPrefix, Set.mem_insert _ _,
    congrArg some X.oldPrefix_finish⟩

/-- Every backward link of the normalized suffix remains a fragment of the
truncated reference warp.  A backward link owned by the removed record would
have two distinct vertices on that record after the final contact, contrary
to no-return. -/
theorem normalizedSuffix_backwardLinksOn_truncatedWarp
    (X : ReservedStrongSelectedStartingLastContact
      (L := L) (hL := hL) (S := S) r) :
    BackwardLinksOn X.truncatedWarp X.normalizedSuffix.path := by
  let trace := selectedRequestTrace U S K r
  let erased := trace.erasedRoute
  have hwarp : Gamma.IsWarp L.limitWarp := by
    simpa only [popularAuxiliaryInput, limitWarp] using
      (popularAuxiliaryInput L hL.legal).ladder.disjoint
  have hback : BackwardLinksOn L.limitWarp X.normalizedSuffix.path := by
    apply (erased.suffixFrom X.lastContact.vertex
      X.lastContact.vertex_mem_chain).compressionOfValid_backwardLinksOn
    · intro s hs
      exact trace.valid s (erased.steps_sublist.subset
        (erased.suffixFrom_steps_subset
          X.lastContact.vertex X.lastContact.vertex_mem_chain hs))
    · exact hwarp
    · intro s hs hdir
      have he := trace.backward_on_ladder s
        (erased.steps_sublist.subset
          (erased.suffixFrom_steps_subset
            X.lastContact.vertex X.lastContact.vertex_mem_chain hs)) hdir
      rw [PopularAuxiliary.Input.familyEdges] at he
      obtain ⟨p, hp, hep⟩ := he
      exact Set.mem_iUnion.2 ⟨p, Set.mem_iUnion.2 ⟨by
        simpa only [popularAuxiliaryInput, limitWarp] using hp, hep⟩⟩
  intro l hl hdir
  obtain ⟨p, hp, hlp⟩ := hback l hl hdir
  have hpne : p ≠ (reservedStrongSelectedStartingRecord r).record := by
    intro hpeq
    subst p
    have hstartSuffix : l.path.start ∈ X.normalizedSuffix.path.vertexSet :=
      X.normalizedSuffix.path.link_support_subset_vertexSet
        hl l.path.start_mem_support
    have hfinishSuffix : l.path.finish ∈ X.normalizedSuffix.path.vertexSet :=
      X.normalizedSuffix.path.link_support_subset_vertexSet
        hl l.path.finish_mem_support
    have hstartRecord : l.path.start ∈
        (reservedStrongSelectedStartingRecord r).record.support :=
      hlp.1 l.path.start_mem_support
    have hfinishRecord : l.path.finish ∈
        (reservedStrongSelectedStartingRecord r).record.support :=
      hlp.1 l.path.finish_mem_support
    have hstart := X.normalizedSuffix_meets_record_only_at_contact
      hstartSuffix hstartRecord
    have hfinish := X.normalizedSuffix_meets_record_only_at_contact
      hfinishSuffix hfinishRecord
    exact l.nontrivial (hstart.trans hfinish.symm)
  exact ⟨p, Set.mem_insert_of_mem _ ⟨hp, by
    simpa only [Set.mem_singleton_iff] using hpne⟩, hlp⟩

/-- Any untouched limiting component remains a member of the truncated
warp. -/
theorem mem_truncatedWarp_of_mem_limitWarp_of_ne_record
    (X : ReservedStrongSelectedStartingLastContact
      (L := L) (hL := hL) (S := S) r)
    {Z : Gamma.DPath} (hZ : Z ∈ L.limitWarp)
    (hne : Z ≠ (reservedStrongSelectedStartingRecord r).record) :
    Z ∈ X.truncatedWarp := by
  exact Set.mem_insert_of_mem _ ⟨hZ, by
    simpa only [Set.mem_singleton_iff] using hne⟩

/-- If the selected terminal component differs from the starting record,
its initial vertex remains an initial of the truncated warp. -/
theorem terminalOwner_initial_mem_truncatedWarp
    (X : ReservedStrongSelectedStartingLastContact
      (L := L) (hL := hL) (S := S) r)
    {Z : Gamma.DPath} (hZ : Z ∈ L.limitWarp)
    (hne : Z ≠ (reservedStrongSelectedStartingRecord r).record) :
    Z.initial ∈ Gamma.initialSet X.truncatedWarp :=
  ⟨Z, X.mem_truncatedWarp_of_mem_limitWarp_of_ne_record hZ hne, rfl⟩

/-- Unless the splice point is already the request exit, the normalized
suffix is a genuine finite alternating trace with its exact endpoints. -/
theorem exists_finite_normalizedSuffix_of_contact_ne_exit
    (X : ReservedStrongSelectedStartingLastContact
      (L := L) (hL := hL) (S := S) r)
    (hne : X.lastContact.vertex ≠ requestExit r) :
    ∃ Q : FiniteTrace Gamma.graph,
      X.normalizedSuffix.path = .finite Q ∧
        Q.initial = X.lastContact.vertex ∧
        Q.terminal = requestExit r := by
  have hinitial := X.normalizedSuffix_initial
  have hterminal := X.normalizedSuffix_terminal
  cases hpath : X.normalizedSuffix.path with
  | trivial x =>
      have hxContact : x = X.lastContact.vertex := by
        simpa only [hpath, AltPath.initial] using hinitial
      have hxExit : x = requestExit r := by
        exact Option.some.inj (by
          simpa only [hpath, AltPath.terminal?] using hterminal)
      exact False.elim (hne (hxContact.symm.trans hxExit))
  | finite Q =>
      refine ⟨Q, rfl, ?_, ?_⟩
      · simpa only [hpath, AltPath.initial] using hinitial
      · exact Option.some.inj (by
          simpa only [hpath, AltPath.terminal?] using hterminal)
  | infinite ray =>
      have hfalse : (none : Option V) = some (requestExit r) := by
        simpa only [hpath, AltPath.terminal?] using hterminal
      cases hfalse

/-- The actual own-start repair reduces every route ending at the initial
of an essential limiting component to the genuine terminal-contact
trichotomy on the truncated warp.  The old starting record has already been
removed, its source prefix retained, and all backward links transferred. -/
theorem terminalContactGeometryOutcome_on_truncatedWarp
    (X : ReservedStrongSelectedStartingLastContact
      (L := L) (hL := hL) (S := S) r)
    (Z : Gamma.DPath) (hZ : Z ∈
      (popularAuxiliaryInput L hL.legal).essentialLadder)
    (hexit : requestExit r = Z.initial)
    (hne : X.lastContact.vertex ≠ requestExit r) :
    ∃ Q : FiniteTrace Gamma.graph,
      X.normalizedSuffix.path = .finite Q ∧
        Q.initial = X.lastContact.vertex ∧
        Q.terminal = requestExit r ∧
        TerminalContactGeometryOutcome X.truncatedWarp Q (requestExit r) := by
  obtain ⟨Q, hQ, hQInitial, hQTerminal⟩ :=
    X.exists_finite_normalizedSuffix_of_contact_ne_exit hne
  have hZEssential : Z ∈ Gamma.essentialWarpPart L.limitWarp := by
    simpa only [popularAuxiliaryInput,
      PopularAuxiliary.Input.essentialLadder, limitWarp] using hZ
  have hZNe : Z ≠ (reservedStrongSelectedStartingRecord r).record := by
    intro hEq
    subst Z
    exact (reservedStrongSelectedStartingRecord r).limit_inessential.2
      hZEssential
  have hZInitial : requestExit r ∈ Gamma.initialSet X.truncatedWarp := by
    rw [hexit]
    exact X.terminalOwner_initial_mem_truncatedWarp hZEssential.1 hZNe
  have hQInitialCarrier : Q.initial ∈ Gamma.vertexSet X.truncatedWarp := by
    have hcontactCarrier : X.lastContact.vertex ∈
        Gamma.vertexSet X.truncatedWarp := by
      rw [← X.normalizedSuffix_initial]
      exact terminalFrontier_subset_vertexSet _
        X.normalizedSuffix_initial_mem_terminalFrontier
    rw [hQInitial]
    exact hcontactCarrier
  have hback : BackwardLinksOn X.truncatedWarp (.finite Q) := by
    have h := X.normalizedSuffix_backwardLinksOn_truncatedWarp
    rw [hQ] at h
    exact h
  have hnoForward : ∀ z,
      (requestExit r, z) ∉
        (AltPath.finite Q).directionEdges .forward := by
    intro z hz
    have hno := selectedErasedCompression_noOutgoing_forward_at_requestExit
      U S K r
    apply hno
    refine ⟨z, ?_⟩
    apply X.normalizedSuffix_directionEdges_subset_selected .forward
    rw [hQ]
    exact hz
  have hout := finiteSourceTerminalOutcome_of_geometry
    X.truncatedWarp_isWarp hback hQInitialCarrier hZInitial
      (by simpa only [hQInitial] using hne) hQTerminal hnoForward
  exact ⟨Q, hQ, hQInitial, hQTerminal, hout⟩

/-- Deleting the temporary splice terminal from the truncated warp leaves
exactly the frontier of the old limit warp with the starting record removed.
No other old terminal can equal the splice contact, by warp disjointness. -/
theorem terminalFrontier_truncatedWarp_sdiff_contact
    (X : ReservedStrongSelectedStartingLastContact
      (L := L) (hL := hL) (S := S) r) :
    Gamma.terminalFrontier X.truncatedWarp \ {X.lastContact.vertex} =
      Gamma.terminalFrontier
        (L.limitWarp \ {(reservedStrongSelectedStartingRecord r).record}) := by
  let record := (reservedStrongSelectedStartingRecord r).record
  let rest := L.limitWarp \ {record}
  have hwarp : Gamma.IsWarp L.limitWarp := by
    simpa only [popularAuxiliaryInput, limitWarp] using
      (popularAuxiliaryInput L hL.legal).ladder.disjoint
  have hrecord : record ∈ L.limitWarp :=
    (reservedStrongSelectedStartingRecord r).record_mem_ladder
  have hcontactNotRest : X.lastContact.vertex ∉
      Gamma.terminalFrontier rest := by
    rintro ⟨p, hpRest, hpTerminal⟩
    have hpne : record ≠ p := by
      intro hEq
      subst p
      exact hpRest.2 (Set.mem_singleton record)
    exact Set.disjoint_left.mp (hwarp hrecord hpRest.1 hpne)
      X.lastContact.vertex_mem
      (Gamma.terminal_mem_support hpTerminal)
  change Gamma.terminalFrontier
      (insert (.inl X.oldPrefix : Gamma.DPath) rest) \
        {X.lastContact.vertex} = Gamma.terminalFrontier rest
  rw [Gamma.terminalFrontier_insert_finite, X.oldPrefix_finish]
  ext x
  simp only [Set.mem_diff, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hx | hx, hxne⟩
    · exact False.elim (hxne hx)
    · exact hx
  · intro hx
    exact ⟨Or.inr hx, fun hEq ↦ hcontactNotRest (hEq ▸ hx)⟩

/-- The successful terminal-contact branch is a genuine whole-owner warp
transaction.  It consumes the displayed terminal-owner initial and removes
only the selected starting record's old frontier contribution. -/
theorem exists_terminalContactSwitchWarp
    (X : ReservedStrongSelectedStartingLastContact
      (L := L) (hL := hL) (S := S) r)
    (Q : FiniteTrace Gamma.graph)
    (hQInitial : Q.initial = X.lastContact.vertex)
    (hswitch : IsTerminalContactSwitching
      X.truncatedWarp Q (requestExit r)) :
    ∃ W : Set Gamma.DPath,
      Gamma.IsWarp W ∧
        Gamma.initialSet W =
          Gamma.initialSet L.limitWarp \ {requestExit r} ∧
        Gamma.terminalFrontier W = Gamma.terminalFrontier
          (L.limitWarp \
            {(reservedStrongSelectedStartingRecord r).record}) := by
  have hcontactTerminal : X.lastContact.vertex ∈
      Gamma.terminalFrontier X.truncatedWarp := by
    rw [← X.normalizedSuffix_initial]
    exact X.normalizedSuffix_initial_mem_terminalFrontier
  obtain ⟨W, hW, hWInitial, hWTerminal⟩ :=
    TerminalContactSwitch.exists_terminalContactSwitch_anyWarp
      X.truncatedWarp Q (requestExit r) X.lastContact.vertex
        hswitch hcontactTerminal hQInitial
  refine ⟨W, hW, ?_, ?_⟩
  · rw [hWInitial, X.truncatedWarp_initialSet]
  · rw [hWTerminal, X.terminalFrontier_truncatedWarp_sdiff_contact]

/-- The successful canonical transaction roots every untouched old terminal
from an unconsumed old initial in the *literal* switched relation.  This is
the signed-boundary content of the whole-owner splice, not merely existence
of an abstract switched warp. -/
theorem terminalContactSwitch_roots_untouchedFrontier
    (X : ReservedStrongSelectedStartingLastContact
      (L := L) (hL := hL) (S := S) r)
    (Q : FiniteTrace Gamma.graph)
    (hQInitial : Q.initial = X.lastContact.vertex)
    (hswitch : IsTerminalContactSwitching
      X.truncatedWarp Q (requestExit r)) :
    ∀ t ∈ Gamma.terminalFrontier
        (L.limitWarp \
          {(reservedStrongSelectedStartingRecord r).record}),
      ∃ a ∈ Gamma.initialSet L.limitWarp \ {requestExit r},
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈
            switchedEdges X.truncatedWarp (.finite Q)) a t := by
  intro t ht
  have hcontact : X.lastContact.vertex ∈
      Gamma.terminalFrontier X.truncatedWarp := by
    rw [← X.normalizedSuffix_initial]
    exact X.normalizedSuffix_initial_mem_terminalFrontier
  have ht' : t ∈ Gamma.terminalFrontier X.truncatedWarp \
      {X.lastContact.vertex} := by
    rw [X.terminalFrontier_truncatedWarp_sdiff_contact]
    exact ht
  obtain ⟨a, ha, hreach⟩ :=
    TerminalContactSwitch.IsTerminalContactSwitching.oldTerminal_rooted
      hswitch hcontact hQInitial ht'
  refine ⟨a, ?_, hreach⟩
  rw [X.truncatedWarp_initialSet] at ha
  exact ha

/-- Feed a literal deferred source-first prefix into the successful
whole-owner transaction.  The resulting dynamic exchange makes the chosen
source-first point an actual terminal and records the exact old sink traded
away (or that no finite old sink was removed).  All source-prefix and
component ancestry is retained in the statement. -/
theorem exists_terminalContact_sourceFirstExchangeWarp
    (X : ReservedStrongSelectedStartingLastContact
      (L := L) (hL := hL) (S := S) r)
    (Q : FiniteTrace Gamma.graph)
    (hQInitial : Q.initial = X.lastContact.vertex)
    (hswitch : IsTerminalContactSwitching
      X.truncatedWarp Q (requestExit r))
    (hexitNotSource : requestExit r ∉ Gamma.source)
    {b : V}
    (hb : b ∈ reservedStrongSelectedSourceFirstBB
      (L := L) (hL := hL) (S := S)) :
    ∃ (R q : FinitePath Gamma.graph)
        (W W' : Set Gamma.DPath),
      R.start ∈ Gamma.source ∧ R.finish = b ∧
        R.support ⊆ (popularAuxiliaryInput L hL.legal).roofRegion ∧
        (∀ x ∈ R.walk.support.dropLast,
          x ∉ reservedStrongSelectedRelevantBB
            (L := L) (hL := hL) (S := S)) ∧
        Gamma.IsWarp W ∧
        Gamma.initialSet W =
          Gamma.initialSet L.limitWarp \ {requestExit r} ∧
        Gamma.terminalFrontier W = Gamma.terminalFrontier
          (L.limitWarp \
            {(reservedStrongSelectedStartingRecord r).record}) ∧
        Gamma.IsWarp W' ∧
        Gamma.initialSet W' =
          Gamma.initialSet L.limitWarp \ {requestExit r} ∧
        (Sum.inl q : Gamma.DPath) ∈ W' ∧
        q.start ∈ Gamma.initialSet L.limitWarp \ {requestExit r} ∧
        q.finish = b ∧
        q.edgeSet ⊆ Alternating.familyEdges W ∪ R.edgeSet ∧
        b ∈ Gamma.terminalFrontier W' ∧
        ((∃ (old : FinitePath Gamma.graph) (contact : V),
            (Sum.inl old : Gamma.DPath) ∈ W ∧
            contact ∈ old.support ∧ contact ∈ R.support ∧
            old.start ∈
              Gamma.initialSet L.limitWarp \ {requestExit r} ∧
            old.finish ∈ Gamma.terminalFrontier
              (L.limitWarp \
                {(reservedStrongSelectedStartingRecord r).record}) ∧
            Gamma.terminalFrontier W' = insert b
              (Gamma.terminalFrontier
                (L.limitWarp \
                  {(reservedStrongSelectedStartingRecord r).record}) \
                {old.finish})) ∨
          Gamma.terminalFrontier W' = insert b
            (Gamma.terminalFrontier
              (L.limitWarp \
                {(reservedStrongSelectedStartingRecord r).record}))) := by
  obtain ⟨R, hRSource, hRFinish, hRRoof, _hbRelevant, hRFirst⟩ :=
    exists_reservedStrongSelected_sourceFirstPrefix hb
  obtain ⟨W, hW, hWInitial, hWTerminal⟩ :=
    X.exists_terminalContactSwitchWarp Q hQInitial hswitch
  have hRStartLimit : R.start ∈ Gamma.initialSet L.limitWarp := by
    exact popularAuxiliary_sourceCovered L hL.legal hRSource
  have hRStartAllowed : R.start ∈
      Gamma.initialSet L.limitWarp \ {requestExit r} := by
    refine ⟨hRStartLimit, ?_⟩
    intro heq
    exact hexitNotSource (Set.mem_singleton_iff.mp heq ▸ hRSource)
  have hRStartW : R.start ∈ Gamma.vertexSet W := by
    apply Alternating.initialSet_subset_vertexSet W
    rw [hWInitial]
    exact hRStartAllowed
  obtain ⟨W', q, hW', hW'Initial, hqW', hqStart,
      hqFinish, hqEdges, hqTerminal, hterminalUpdate⟩ :=
    GroundingDynamicComponentExchange.exists_exchangeWarp_of_segment_with_terminalUpdate
      W hW R hRStartW
  refine ⟨R, q, W, W', hRSource, hRFinish, hRRoof, hRFirst,
    hW, hWInitial, hWTerminal, hW', ?_, hqW', ?_, ?_, hqEdges, ?_, ?_⟩
  · rw [hW'Initial, hWInitial]
  · rw [hWInitial] at hqStart
    exact hqStart
  · exact hqFinish.trans hRFinish
  · exact hRFinish ▸ hqTerminal
  · rcases hterminalUpdate with hremoved | hnone
    · left
      obtain ⟨old, contact, holdW, hcontactOld, hcontactR,
        holdStart, holdFinish, hupdate⟩ := hremoved
      refine ⟨old, contact, holdW, hcontactOld, hcontactR, ?_, ?_, ?_⟩
      · rw [hWInitial] at holdStart
        exact holdStart
      · rw [hWTerminal] at holdFinish
        exact holdFinish
      · rw [hRFinish] at hupdate
        rw [hWTerminal] at hupdate
        exact hupdate
    · right
      rw [hRFinish] at hnone
      rw [hWTerminal] at hnone
      exact hnone

/-- If the source-first exchange trades away a finite old sink, the named
contact immediately supplies a new ambient source path to that displaced
sink.  This is the concrete continuation datum for an augmenting chain:
the traded obligation is not lost or replaced by a bare cardinal count. -/
theorem exists_sourcePath_to_displacedFiniteSink
    (R old : FinitePath Gamma.graph) (contact : V)
    (hRSource : R.start ∈ Gamma.source)
    (hcontactR : contact ∈ R.support)
    (hcontactOld : contact ∈ old.support) :
    ∃ p : FinitePath Gamma.graph,
      p.start = R.start ∧ p.start ∈ Gamma.source ∧
        p.finish = old.finish ∧
        p.support ⊆ R.support ∪ old.support := by
  obtain ⟨front, hfrontStart, hfrontFinish, hfrontSupport, _hfrontEdges⟩ :=
    GroundingPathPrefix.exists_initialFinitePrefix (.inl R : Gamma.DPath)
      hcontactR
  let tail := old.suffixFrom contact hcontactOld
  have hjoin : tail.start = front.finish := by
    rw [FinitePath.suffixFrom_start, hfrontFinish]
  let tailWalk : Walk Gamma.graph front.finish old.finish :=
    RelationalRoof.castStart Gamma.graph.Adj hjoin tail.walk
  let joined : Walk Gamma.graph front.start old.finish :=
    front.walk.append tailWalk
  obtain ⟨q, hqSupport⟩ :=
    RelationalRoof.exists_pathTo_support_subset
      (R := Gamma.graph.Adj) joined
  let p : FinitePath Gamma.graph :=
    { start := front.start
      finish := old.finish
      walk := q.1
      isPath := q.2 }
  refine ⟨p, ?_, ?_, rfl, ?_⟩
  · exact hfrontStart
  · change front.start ∈ Gamma.source
    rw [hfrontStart]
    exact hRSource
  · intro x hxp
    have hxJoined : x ∈ joined.support := hqSupport hxp
    rw [Walk.support_append] at hxJoined
    rcases List.mem_append.mp hxJoined with hxFront | hxTail
    · exact Or.inl (hfrontSupport hxFront)
    · right
      have hxTailWalk : x ∈ tailWalk.support :=
        List.mem_of_mem_tail hxTail
      have hxTail : x ∈ tail.support := by
        change x ∈
          (RelationalRoof.castStart Gamma.graph.Adj hjoin tail.walk).support
          at hxTailWalk
        rw [RelationalRoof.support_castStart] at hxTailWalk
        exact hxTailWalk
      exact old.suffixFrom_support_subset contact hcontactOld hxTail

/-- Every truncated-warp component contacted by the normalized selected
suffix has one of the three usable roles in the whole-owner transaction:
it is source-grounded, it is the displayed terminal component, or it was
already inessential in the old limit warp.  The newly inserted prefix is
handled by its literal source; all other components are classified by the
canonical deferred collision theorem. -/
theorem canonicalDeferredLadder_truncatedOwner_grounded_or_terminal_or_inessential
    (preferred : Ladder.Stage kappa → Option V)
    (hkappa : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (hNoEnter : Gamma.NoEdgeEnters Gamma.source)
    (hL : IsKappaHindrance
      (canonicalDeferredLadder Gamma kappa preferred))
    (S : Popular.PopularSeparator
      (popularAuxiliaryIndexed
        (canonicalDeferredLadder Gamma kappa preferred) hL))
    (r : Request
      (popularAuxiliaryInput
        (canonicalDeferredLadder Gamma kappa preferred) hL.legal) S.cut)
    (X : ReservedStrongSelectedStartingLastContact
      (L := canonicalDeferredLadder Gamma kappa preferred)
      (hL := hL) (S := S) r)
    (Z : Gamma.DPath)
    (hZ : Z ∈ (canonicalDeferredLadder Gamma kappa preferred).limitWarp)
    (hexit : requestExit r = Z.initial)
    (Y : Gamma.DPath) (hY : Y ∈ X.truncatedWarp)
    {x : V} (hxSuffix : x ∈ X.normalizedSuffix.path.vertexSet)
    (hxY : x ∈ Y.support) :
    Y.initial ∈ Gamma.source ∨ Y = Z ∨
      Y ∈ Gamma.inessentialPaths
        (canonicalDeferredLadder Gamma kappa preferred).limitWarp := by
  let lad := canonicalDeferredLadder Gamma kappa preferred
  have hYCases : Y = (.inl X.oldPrefix : Gamma.DPath) ∨
      Y ∈ lad.limitWarp \
        {(reservedStrongSelectedStartingRecord r).record} := by
    simpa only [ReservedStrongSelectedStartingLastContact.truncatedWarp,
      Set.mem_insert_iff] using hY
  rcases hYCases with hPrefix | hOld
  · subst Y
    exact Or.inl X.oldPrefix_source
  · by_cases hessential : Y ∈ Gamma.essentialWarpPart lad.limitWarp
    · have hYEssential : Y ∈
          (popularAuxiliaryInput lad hL.legal).essentialLadder := by
        simpa only [popularAuxiliaryInput,
          PopularAuxiliary.Input.essentialLadder, limitWarp] using hessential
      rcases
          canonicalDeferredLadder_startingLastContact_essentialOwner_grounded_or_terminal
            preferred hkappa huncountable hNoEnter hL S r X Z hZ hexit
              Y hYEssential hxSuffix hxY with hgrounded | hterminal
      · exact Or.inl hgrounded
      · exact Or.inr (Or.inl hterminal)
    · exact Or.inr (Or.inr ⟨hOld.1, hessential⟩)

/-- A failure of `ForwardLinksOff` for the actual truncated reference warp
has a literal selected-suffix edge and a literal truncated-warp owner.  The
owner is immediately classified by the canonical deferred geometry; in
particular, replacing the starting record by its source prefix does not
create an unclassified reference-edge failure. -/
theorem canonicalDeferredLadder_truncatedForwardReferenceOwner_exists
    (preferred : Ladder.Stage kappa → Option V)
    (hkappa : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (hNoEnter : Gamma.NoEdgeEnters Gamma.source)
    (hL : IsKappaHindrance
      (canonicalDeferredLadder Gamma kappa preferred))
    (S : Popular.PopularSeparator
      (popularAuxiliaryIndexed
        (canonicalDeferredLadder Gamma kappa preferred) hL))
    (r : Request
      (popularAuxiliaryInput
        (canonicalDeferredLadder Gamma kappa preferred) hL.legal) S.cut)
    (X : ReservedStrongSelectedStartingLastContact
      (L := canonicalDeferredLadder Gamma kappa preferred)
      (hL := hL) (S := S) r)
    (Z : Gamma.DPath)
    (hZ : Z ∈ (canonicalDeferredLadder Gamma kappa preferred).limitWarp)
    (hexit : requestExit r = Z.initial)
    (hnot : ¬ ForwardLinksOff X.truncatedWarp X.normalizedSuffix.path) :
    ∃ e : V × V, ∃ Y : Gamma.DPath,
      e ∈ X.normalizedSuffix.path.directionEdges .forward ∧
        Y ∈ X.truncatedWarp ∧ e ∈ Y.edgeSet ∧
        (Y.initial ∈ Gamma.source ∨ Y = Z ∨
          Y ∈ Gamma.inessentialPaths
            (canonicalDeferredLadder Gamma kappa preferred).limitWarp) := by
  simp only [ForwardLinksOff, not_forall] at hnot
  obtain ⟨l, hl, hldir, hnotDisjoint⟩ := hnot
  obtain ⟨e, hel, heFamily⟩ := Set.not_disjoint_iff.1 hnotDisjoint
  simp only [Alternating.familyEdges, Set.mem_iUnion] at heFamily
  obtain ⟨Y, hY, heY⟩ := heFamily
  have heEnds := l.path.edgeSet_subset_support_prod hel
  have heTailSuffix : e.1 ∈ X.normalizedSuffix.path.vertexSet :=
    X.normalizedSuffix.path.link_support_subset_vertexSet hl heEnds.1
  have heTailY : e.1 ∈ Y.support :=
    (Y.edgeSet_subset_support_prod heY).1
  have howner :=
    canonicalDeferredLadder_truncatedOwner_grounded_or_terminal_or_inessential
      preferred hkappa huncountable hNoEnter hL S r X Z hZ hexit
        Y hY heTailSuffix heTailY
  refine ⟨e, Y, ?_, hY, heY, howner⟩
  simp only [AltPath.directionEdges, Set.mem_iUnion]
  exact ⟨l, hl, hldir, hel⟩

/-- A nonterminal forward contact left uncovered by the actual truncated
reference warp likewise has a literal owner with the same three canonical
roles.  The non-backward and nonterminal certificates are retained for the
next component transaction. -/
theorem canonicalDeferredLadder_truncatedUncoveredForwardOwner_exists
    (preferred : Ladder.Stage kappa → Option V)
    (hkappa : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (hNoEnter : Gamma.NoEdgeEnters Gamma.source)
    (hL : IsKappaHindrance
      (canonicalDeferredLadder Gamma kappa preferred))
    (S : Popular.PopularSeparator
      (popularAuxiliaryIndexed
        (canonicalDeferredLadder Gamma kappa preferred) hL))
    (r : Request
      (popularAuxiliaryInput
        (canonicalDeferredLadder Gamma kappa preferred) hL.legal) S.cut)
    (X : ReservedStrongSelectedStartingLastContact
      (L := canonicalDeferredLadder Gamma kappa preferred)
      (hL := hL) (S := S) r)
    (Z : Gamma.DPath)
    (hZ : Z ∈ (canonicalDeferredLadder Gamma kappa preferred).limitWarp)
    (hexit : requestExit r = Z.initial)
    (hnot : ¬ ForwardVertexContactsCoveredAtTerminal
      Gamma X.truncatedWarp X.normalizedSuffix.path) :
    ∃ x : V, ∃ Y : Gamma.DPath,
      x ∈ X.normalizedSuffix.path.directionVertices .forward ∧
        Y ∈ X.truncatedWarp ∧ x ∈ Y.support ∧
        x ∉ X.normalizedSuffix.path.directionVertices .backward ∧
        X.normalizedSuffix.path.terminal? ≠ some x ∧
        (Y.initial ∈ Gamma.source ∨ Y = Z ∨
          Y ∈ Gamma.inessentialPaths
            (canonicalDeferredLadder Gamma kappa preferred).limitWarp) := by
  simp only [ForwardVertexContactsCoveredAtTerminal, not_forall,
    not_or] at hnot
  obtain ⟨x, hxForward, hxWarp, hxNotBackward, hxNotTerminal⟩ := hnot
  obtain ⟨Y, hY, hxY⟩ := hxWarp
  have hxSuffix : x ∈ X.normalizedSuffix.path.vertexSet := by
    simp only [AltPath.directionVertices, Set.mem_iUnion] at hxForward
    obtain ⟨l, hl, _hldir, hxl⟩ := hxForward
    exact X.normalizedSuffix.path.link_support_subset_vertexSet hl hxl
  have howner :=
    canonicalDeferredLadder_truncatedOwner_grounded_or_terminal_or_inessential
      preferred hkappa huncountable hNoEnter hL S r X Z hZ hexit
        Y hY hxSuffix hxY
  exact ⟨x, Y, hxForward, hY, hxY, hxNotBackward, hxNotTerminal, howner⟩

end ReservedStrongSelectedStartingLastContact

end Deferred
end KappaLadder
end DWeb
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.Deferred.ReservedStrongSelectedStartingLastContact.truncatedWarp_isWarp
#print axioms
  Erdos599.DWeb.KappaLadder.Deferred.ReservedStrongSelectedStartingLastContact.normalizedSuffix_backwardLinksOn_truncatedWarp
#print axioms
  Erdos599.DWeb.KappaLadder.Deferred.ReservedStrongSelectedStartingLastContact.terminalContactGeometryOutcome_on_truncatedWarp
#print axioms
  Erdos599.DWeb.KappaLadder.Deferred.ReservedStrongSelectedStartingLastContact.exists_terminalContactSwitchWarp
#print axioms
  Erdos599.DWeb.KappaLadder.Deferred.ReservedStrongSelectedStartingLastContact.terminalContactSwitch_roots_untouchedFrontier
#print axioms
  Erdos599.DWeb.KappaLadder.Deferred.ReservedStrongSelectedStartingLastContact.exists_terminalContact_sourceFirstExchangeWarp
#print axioms
  Erdos599.DWeb.KappaLadder.Deferred.ReservedStrongSelectedStartingLastContact.exists_sourcePath_to_displacedFiniteSink
#print axioms
  Erdos599.DWeb.KappaLadder.Deferred.ReservedStrongSelectedStartingLastContact.canonicalDeferredLadder_truncatedOwner_grounded_or_terminal_or_inessential
#print axioms
  Erdos599.DWeb.KappaLadder.Deferred.ReservedStrongSelectedStartingLastContact.canonicalDeferredLadder_truncatedForwardReferenceOwner_exists
#print axioms
  Erdos599.DWeb.KappaLadder.Deferred.ReservedStrongSelectedStartingLastContact.canonicalDeferredLadder_truncatedUncoveredForwardOwner_exists
