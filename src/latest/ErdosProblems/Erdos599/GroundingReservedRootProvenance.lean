/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingReservedBackwardOwner
import ErdosProblems.Erdos599.GroundingActiveRequestRootTransfer
import ErdosProblems.Erdos599.GroundingInactiveControlRootTransfer
import ErdosProblems.Erdos599.GroundingReservedFrontierOutput
import ErdosProblems.Erdos599.GroundingPathPrefix
import ErdosProblems.Erdos599.GroundingFiniteSourceRootAt

/-!
# Source provenance for refined grounding controls

The source-provenance calculation for a selected erased request depends on
only two properties of the control package: the selected auxiliary path has
a grounded source index, and its source is different from the auxiliary
source representing the reserved record.  This module states the calculation
with those two hypotheses, so that adding further local-fan avoidance
conditions does not require copying the finite-source/proxy case split.

The resulting finite prefix is an original-ladder path, not automatically a
path in the final switched relation.  The last theorem records the exact
edge-survival premise which turns it into the source-root reachability anchor
used by the active-request transfer.
-/

noncomputable section

open Set

namespace Erdos599
namespace DWeb.KappaLadder

open _root_.Erdos599.DirectedPath PopularGroundingBridge
open GroundingSimultaneousDecode GroundingErasedDecode

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}
variable {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
variable {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}

/-- An arbitrary control refinement preserves the decoded initial vertex of
an old auxiliary source. -/
theorem selectedRequestTrace_initial_of_start_old_withControls
    (K : GroundingSelection.Controls S)
    (r : Request (L.popularAuxiliaryInput hL.legal) S.cut) (x : V)
    (hstart : (strongSelectedPath (L.popularAuxiliaryIndexed hL) S K r).start =
      .old x) :
    (selectedRequestTrace (L.popularAuxiliaryIndexed hL) S K r).initial = x := by
  let J := L.popularAuxiliaryInput hL.legal
  let U := L.popularAuxiliaryIndexed hL
  let p := strongSelectedPath U S K r
  have hp : p ∈ (strongSelectedWarp U S K).paths := ⟨r, rfl⟩
  have hpSource : p.start ∈ J.lambda.source :=
    (strongSelectedWarp U S K).starts_in_source hp
  cases r with
  | inl y =>
      change (J.decodeFinitePathToExit p hpSource y.1 _).initial = x
      apply J.decodeFinitePathToExit_initial_of_start_old
      exact hstart
  | inr e =>
      change (J.decodeFinitePathToEdgeEntry p hpSource e.1.1 e.1.2 _).initial = x
      apply J.decodeFinitePathToEdgeEntry_initial_of_start_old
      exact hstart

/-- The proxy-source counterpart of
`selectedRequestTrace_initial_of_start_old_withControls`. -/
theorem selectedRequestTrace_initial_mem_proxy_withControls
    (K : GroundingSelection.Controls S)
    (r : Request (L.popularAuxiliaryInput hL.legal) S.cut)
    (i : L.groundedInfiniteRecords)
    (hstart : (strongSelectedPath (L.popularAuxiliaryIndexed hL) S K r).start =
      .proxy i) :
    (selectedRequestTrace (L.popularAuxiliaryIndexed hL) S K r).initial ∈
      i.1.support := by
  let J := L.popularAuxiliaryInput hL.legal
  let U := L.popularAuxiliaryIndexed hL
  let p := strongSelectedPath U S K r
  have hp : p ∈ (strongSelectedWarp U S K).paths := ⟨r, rfl⟩
  have hpSource : p.start ∈ J.lambda.source :=
    (strongSelectedWarp U S K).starts_in_source hp
  cases r with
  | inl y =>
      change (J.decodeFinitePathToExit p hpSource y.1 _).initial ∈
        (J.proxyPath i).support
      apply J.decodeFinitePathToExit_initial_mem_proxyPath_of_start_proxy
      exact hstart
  | inr e =>
      change (J.decodeFinitePathToEdgeEntry p hpSource e.1.1 e.1.2 _).initial ∈
        (J.proxyPath i).support
      apply J.decodeFinitePathToEdgeEntry_initial_mem_proxyPath_of_start_proxy
      exact hstart

/-- Generic source provenance and finite root prefix for a refined control
package.  The two hypotheses are precisely what a refinement of
`groundedConcreteControls` has to preserve. -/
theorem UnusedGroundedRecord.exists_selectedRequest_rootPrefix_withControls
    (R : L.UnusedGroundedRecord hL S)
    (K : GroundingSelection.Controls S)
    (r : Request (L.popularAuxiliaryInput hL.legal) S.cut)
    (hground : strongSelectedPath (L.popularAuxiliaryIndexed hL) S K r ∈
      L.groundedSourcePaths hL)
    (hsourceNe :
      (strongSelectedPath (L.popularAuxiliaryIndexed hL) S K r).start ≠
        R.auxiliarySource.1) :
    ∃ (parent : Gamma.DPath)
        (q : _root_.Erdos599.DirectedPath.FinitePath Gamma.graph),
      parent ∈ Gamma.inessentialPaths L.limitWarp ∧
        q.start ∈ Gamma.source \ {R.record.initial} ∧
        q.finish =
          (selectedRequestTrace (L.popularAuxiliaryIndexed hL) S K r).initial ∧
        q.support ⊆ parent.support ∧ q.edgeSet ⊆ parent.edgeSet := by
  let J := L.popularAuxiliaryInput hL.legal
  let U := L.popularAuxiliaryIndexed hL
  let p := strongSelectedPath U S K r
  let T := selectedRequestTrace U S K r
  have hp : p ∈ (strongSelectedWarp U S K).paths := ⟨r, rfl⟩
  have hpSelectedSource : p.start ∈ J.lambda.source :=
    (strongSelectedWarp U S K).starts_in_source hp
  obtain ⟨hpSource, _haGround⟩ := hground
  let source : J.lambda.source := ⟨p.start, hpSelectedSource⟩
  have hsourceNe' : source ≠ R.auxiliarySource := by
    intro hEq
    apply hsourceNe
    exact congrArg Subtype.val hEq
  rcases J.start_of_mem_lambda_source p hpSource with
      ⟨x, hxFinite, hstart⟩ | ⟨i, hstart⟩
  · let xs : L.groundedFiniteTerminalSet := ⟨x, hxFinite⟩
    have hindex : U.f source = L.finiteTerminalIndex xs := by
      have hs : source =
          ⟨.old xs.1, (J.mem_lambda_source_old xs.1).2 xs.2⟩ := by
        exact Subtype.ext hstart
      rw [congrArg U.f hs]
      rfl
    have ha : L.finiteTerminalIndex xs ∈ L.phiGround :=
      L.finiteTerminalStage_mem_phiGround hL.legal xs
    let xs' : L.finiteTerminalSet :=
      ⟨xs.1, L.groundedFiniteTerminalSet_subset_finiteTerminalSet xs.2⟩
    obtain ⟨_hfinite, parent, hchosen, hterminal⟩ :=
      L.finiteTerminalStage_spec xs'
    have hstage : L.finiteTerminalStage xs' = L.finiteTerminalIndex xs := rfl
    rw [hstage] at hchosen
    have hparentSource : parent.initial ∈ Gamma.source := by
      obtain ⟨q, hq, hqSource⟩ := ha
      have hpq : parent = q := Option.some.inj (hchosen.symm.trans hq)
      exact hpq ▸ hqSource
    have hTinitial : T.initial = x :=
      selectedRequestTrace_initial_of_start_old_withControls K r x hstart
    have hparentInessential :
        parent ∈ Gamma.inessentialPaths L.limitWarp :=
      L.recorded_mem_limitWarp_inessential_sourceGeometry hL.legal hchosen
    have hrootNe : R.record.initial ≠ parent.initial :=
      R.record_initial_ne_parent_initial_of_auxiliarySource_ne source
        (L.finiteTerminalIndex xs) parent hsourceNe' hindex hchosen
          hparentInessential.1
    have htrace : T.initial ∈ parent.support := by
      rw [hTinitial]
      exact Gamma.terminal_mem_support hterminal
    obtain ⟨q, hqStart, hqFinish, hqSupport, hqEdges⟩ :=
      GroundingPathPrefix.exists_initialFinitePrefix parent htrace
    refine ⟨parent, q, hparentInessential, ?_, hqFinish, hqSupport, hqEdges⟩
    rw [hqStart]
    exact ⟨hparentSource, fun heq =>
      hrootNe (Set.mem_singleton_iff.mp heq).symm⟩
  · have hindex : U.f source = L.groundedInfiniteStage i := by
      have hs : source = ⟨.proxy i, J.mem_lambda_source_proxy i⟩ := by
        exact Subtype.ext hstart
      rw [congrArg U.f hs]
      rfl
    have ha : L.groundedInfiniteStage i ∈ L.phiGround :=
      (L.groundedInfiniteStage_spec i).1.1
    have hchosen := (L.groundedInfiniteStage_spec i).2
    have hparentSource : i.1.initial ∈ Gamma.source := by
      obtain ⟨q, hq, hqSource⟩ := ha
      have hiq : i.1 = q := Option.some.inj (hchosen.symm.trans hq)
      exact hiq ▸ hqSource
    have htrace : T.initial ∈ i.1.support :=
      selectedRequestTrace_initial_mem_proxy_withControls K r i hstart
    have hparentInessential :
        i.1 ∈ Gamma.inessentialPaths L.limitWarp :=
      L.recorded_mem_limitWarp_inessential_sourceGeometry hL.legal hchosen
    have hrootNe : R.record.initial ≠ i.1.initial :=
      R.record_initial_ne_parent_initial_of_auxiliarySource_ne source
        (L.groundedInfiniteStage i) i.1 hsourceNe' hindex hchosen
          hparentInessential.1
    obtain ⟨q, hqStart, hqFinish, hqSupport, hqEdges⟩ :=
      GroundingPathPrefix.exists_initialFinitePrefix i.1 htrace
    refine ⟨i.1, q, hparentInessential, ?_, hqFinish, hqSupport, hqEdges⟩
    rw [hqStart]
    exact ⟨hparentSource, fun heq =>
      hrootNe (Set.mem_singleton_iff.mp heq).symm⟩

/-- Root-prefix provenance specialized to the controls which reserve `R`.
This is a reusable alias whose proof goes through the arbitrary-control
theorem above. -/
theorem UnusedGroundedRecord.exists_reservedSelectedRequest_rootPrefix_generic
    (R : L.UnusedGroundedRecord hL S)
    (r : Request (L.popularAuxiliaryInput hL.legal) S.cut) :
    ∃ (parent : Gamma.DPath)
        (q : _root_.Erdos599.DirectedPath.FinitePath Gamma.graph),
      parent ∈ Gamma.inessentialPaths L.limitWarp ∧
        q.start ∈ Gamma.source \ {R.record.initial} ∧
        q.finish =
          (selectedRequestTrace (L.popularAuxiliaryIndexed hL) S
            (L.reservedGroundedControls hL S R) r).initial ∧
        q.support ⊆ parent.support ∧ q.edgeSet ⊆ parent.edgeSet := by
  apply R.exists_selectedRequest_rootPrefix_withControls
  · exact strongSelectedPath_mem_groundedSourcePaths_reserved R r
  · exact strongSelectedPath_start_ne_reservedAuxiliarySource R r

/-- If the finite original-ladder root prefix survives in a relation `E`,
the decoded initial anchor is genuinely reachable from an allowed source.
This deliberately exposes edge survival: source provenance alone cannot
prove it after a simultaneous switch. -/
theorem UnusedGroundedRecord.selectedRequest_initial_rooted_withControls
    (R : L.UnusedGroundedRecord hL S)
    (K : GroundingSelection.Controls S)
    (r : Request (L.popularAuxiliaryInput hL.legal) S.cut)
    (hground : strongSelectedPath (L.popularAuxiliaryIndexed hL) S K r ∈
      L.groundedSourcePaths hL)
    (hsourceNe :
      (strongSelectedPath (L.popularAuxiliaryIndexed hL) S K r).start ≠
        R.auxiliarySource.1)
    (E : Set (V × V))
    (hsurvives : ∀ (parent : Gamma.DPath)
        (q : _root_.Erdos599.DirectedPath.FinitePath Gamma.graph),
      parent ∈ Gamma.inessentialPaths L.limitWarp →
      q.start ∈ Gamma.source \ {R.record.initial} →
      q.finish =
          (selectedRequestTrace (L.popularAuxiliaryIndexed hL) S K r).initial →
      q.support ⊆ parent.support → q.edgeSet ⊆ parent.edgeSet →
      q.edgeSet ⊆ E) :
    ∃ a ∈ Gamma.source \ {R.record.initial},
      Relation.ReflTransGen (fun x y ↦ (x, y) ∈ E) a
        (selectedRequestTrace (L.popularAuxiliaryIndexed hL) S K r).initial := by
  obtain ⟨parent, q, hparent, hqStart, hqFinish, hqSupport, hqEdges⟩ :=
    R.exists_selectedRequest_rootPrefix_withControls K r hground hsourceNe
  refine ⟨q.start, hqStart, ?_⟩
  have hreach : Relation.ReflTransGen (fun x y ↦ (x, y) ∈ E)
      q.start q.finish :=
    Relation.ReflTransGen.mono
      (r := fun x y ↦ (x, y) ∈ q.edgeSet)
      (p := fun x y ↦ (x, y) ∈ E)
      (fun _ _ h ↦ hsurvives parent q hparent hqStart hqFinish
        hqSupport hqEdges h) _ _
      (_root_.Erdos599.Alternating.Walk.reflTransGen_edgeSet q.walk)
  exact hqFinish ▸ hreach

/-- Exact deleted-head reduction for the grounded selected-source prefix,
uniformly in the controls and stopping frontier.  The four callbacks are the
complete list of reasons why the final edge entering the surviving suffix
can be absent from the frontier-stopped switch. -/
theorem UnusedGroundedRecord.selectedRequest_initial_rootedAt_of_lastDeletedHead_cases
    (R : L.UnusedGroundedRecord hL S)
    (K : GroundingSelection.Controls S) (T : Set V)
    (r : Request (L.popularAuxiliaryInput hL.legal) S.cut)
    (hground : strongSelectedPath (L.popularAuxiliaryIndexed hL) S K r ∈
      L.groundedSourcePaths hL)
    (hsourceNe :
      (strongSelectedPath (L.popularAuxiliaryIndexed hL) S K r).start ≠
        R.auxiliarySource.1)
    (hCE : ∀ (parent : Gamma.DPath)
      (q : _root_.Erdos599.DirectedPath.FinitePath Gamma.graph),
      parent ∈ Gamma.inessentialPaths L.limitWarp →
      q.start ∈ Gamma.source \ {R.record.initial} →
      q.finish =
          (selectedRequestTrace (L.popularAuxiliaryIndexed hL) S K r).initial →
      q.support ⊆ parent.support → q.edgeSet ⊆ parent.edgeSet →
      ∀ (D : LastDeletedHead q
          (erasedSelectedSwitchedEdgesAt
            (L.popularAuxiliaryIndexed hL) S K T)) u,
        (u, D.head) ∈ q.edgeSet →
        (u, D.head) ∈ GroundingCut.CE
          (L.popularAuxiliaryInput hL.legal) S.cut →
        ∃ a ∈ Gamma.source \ {R.record.initial},
          Relation.ReflTransGen
            (fun x y ↦ (x, y) ∈ erasedSelectedSwitchedEdgesAt
              (L.popularAuxiliaryIndexed hL) S K T) a D.head)
    (hbackward : ∀ (parent : Gamma.DPath)
      (q : _root_.Erdos599.DirectedPath.FinitePath Gamma.graph),
      parent ∈ Gamma.inessentialPaths L.limitWarp →
      q.start ∈ Gamma.source \ {R.record.initial} →
      q.finish =
          (selectedRequestTrace (L.popularAuxiliaryIndexed hL) S K r).initial →
      q.support ⊆ parent.support → q.edgeSet ⊆ parent.edgeSet →
      ∀ (D : LastDeletedHead q
          (erasedSelectedSwitchedEdgesAt
            (L.popularAuxiliaryIndexed hL) S K T)) u,
        (u, D.head) ∈ q.edgeSet →
        (u, D.head) ∈ erasedSelectedDirectionEdgesAt
          (L.popularAuxiliaryIndexed hL) S K T .backward →
        ∃ a ∈ Gamma.source \ {R.record.initial},
          Relation.ReflTransGen
            (fun x y ↦ (x, y) ∈ erasedSelectedSwitchedEdgesAt
              (L.popularAuxiliaryIndexed hL) S K T) a D.head)
    (hconflict : ∀ (parent : Gamma.DPath)
      (q : _root_.Erdos599.DirectedPath.FinitePath Gamma.graph),
      parent ∈ Gamma.inessentialPaths L.limitWarp →
      q.start ∈ Gamma.source \ {R.record.initial} →
      q.finish =
          (selectedRequestTrace (L.popularAuxiliaryIndexed hL) S K r).initial →
      q.support ⊆ parent.support → q.edgeSet ⊆ parent.edgeSet →
      ∀ (D : LastDeletedHead q
          (erasedSelectedSwitchedEdgesAt
            (L.popularAuxiliaryIndexed hL) S K T)) u,
        (u, D.head) ∈ q.edgeSet →
        (u, D.head) ∈ forwardConflictCutEdgesAt
          (L.popularAuxiliaryIndexed hL) S K T →
        ∃ a ∈ Gamma.source \ {R.record.initial},
          Relation.ReflTransGen
            (fun x y ↦ (x, y) ∈ erasedSelectedSwitchedEdgesAt
              (L.popularAuxiliaryIndexed hL) S K T) a D.head)
    (hboundary : ∀ (parent : Gamma.DPath)
      (q : _root_.Erdos599.DirectedPath.FinitePath Gamma.graph),
      parent ∈ Gamma.inessentialPaths L.limitWarp →
      q.start ∈ Gamma.source \ {R.record.initial} →
      q.finish =
          (selectedRequestTrace (L.popularAuxiliaryIndexed hL) S K r).initial →
      q.support ⊆ parent.support → q.edgeSet ⊆ parent.edgeSet →
      ∀ (D : LastDeletedHead q
          (erasedSelectedSwitchedEdgesAt
            (L.popularAuxiliaryIndexed hL) S K T)) u,
        (u, D.head) ∈ q.edgeSet →
        (u, D.head) ∈ residualLadderEdges
          (L.popularAuxiliaryIndexed hL) S → u ∈ T →
        ∃ a ∈ Gamma.source \ {R.record.initial},
          Relation.ReflTransGen
            (fun x y ↦ (x, y) ∈ erasedSelectedSwitchedEdgesAt
              (L.popularAuxiliaryIndexed hL) S K T) a D.head) :
    ∃ a ∈ Gamma.source \ {R.record.initial},
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ erasedSelectedSwitchedEdgesAt
          (L.popularAuxiliaryIndexed hL) S K T) a
        (selectedRequestTrace (L.popularAuxiliaryIndexed hL) S K r).initial := by
  obtain ⟨parent, q, hparent, hqStart, hqFinish, hqSupport, hqEdges⟩ :=
    R.exists_selectedRequest_rootPrefix_withControls K r hground hsourceNe
  have hqFamily : q.edgeSet ⊆
      (L.popularAuxiliaryInput hL.legal).familyEdges := by
    intro e he
    exact ⟨parent, hparent.1, hqEdges he⟩
  have hstart : ∃ a ∈ Gamma.source \ {R.record.initial},
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ erasedSelectedSwitchedEdgesAt
          (L.popularAuxiliaryIndexed hL) S K T) a q.start :=
    ⟨q.start, hqStart, .refl⟩
  obtain ⟨a, ha, hareach⟩ :=
    exists_root_reaching_finishAt_of_lastDeletedHead_cases K T
      (Gamma.source \ {R.record.initial}) q hqFamily hstart
      (hCE parent q hparent hqStart hqFinish hqSupport hqEdges)
      (hbackward parent q hparent hqStart hqFinish hqSupport hqEdges)
      (hconflict parent q hparent hqStart hqFinish hqSupport hqEdges)
      (hboundary parent q hparent hqStart hqFinish hqSupport hqEdges)
  exact ⟨a, ha, hqFinish ▸ hareach⟩

/-- Reserved-control specialization of the exact four-case deleted-head
reduction. -/
theorem UnusedGroundedRecord.reservedSelectedRequest_initial_rootedAt_of_lastDeletedHead_cases
    (R : L.UnusedGroundedRecord hL S) (T : Set V)
    (r : Request (L.popularAuxiliaryInput hL.legal) S.cut)
    (hCE : ∀ (parent : Gamma.DPath)
      (q : _root_.Erdos599.DirectedPath.FinitePath Gamma.graph),
      parent ∈ Gamma.inessentialPaths L.limitWarp →
      q.start ∈ Gamma.source \ {R.record.initial} →
      q.finish = (selectedRequestTrace (L.popularAuxiliaryIndexed hL) S
        (L.reservedGroundedControls hL S R) r).initial →
      q.support ⊆ parent.support → q.edgeSet ⊆ parent.edgeSet →
      ∀ (D : LastDeletedHead q
          (L.assertion822ReservedSwitchedEdgesAt hL S R T)) u,
        (u, D.head) ∈ q.edgeSet →
        (u, D.head) ∈ GroundingCut.CE
          (L.popularAuxiliaryInput hL.legal) S.cut →
        ∃ a ∈ Gamma.source \ {R.record.initial},
          Relation.ReflTransGen (fun x y ↦ (x, y) ∈
            L.assertion822ReservedSwitchedEdgesAt hL S R T) a D.head)
    (hbackward : ∀ (parent : Gamma.DPath)
      (q : _root_.Erdos599.DirectedPath.FinitePath Gamma.graph),
      parent ∈ Gamma.inessentialPaths L.limitWarp →
      q.start ∈ Gamma.source \ {R.record.initial} →
      q.finish = (selectedRequestTrace (L.popularAuxiliaryIndexed hL) S
        (L.reservedGroundedControls hL S R) r).initial →
      q.support ⊆ parent.support → q.edgeSet ⊆ parent.edgeSet →
      ∀ (D : LastDeletedHead q
          (L.assertion822ReservedSwitchedEdgesAt hL S R T)) u,
        (u, D.head) ∈ q.edgeSet →
        (u, D.head) ∈ erasedSelectedDirectionEdgesAt
          (L.popularAuxiliaryIndexed hL) S
            (L.reservedGroundedControls hL S R) T .backward →
        ∃ a ∈ Gamma.source \ {R.record.initial},
          Relation.ReflTransGen (fun x y ↦ (x, y) ∈
            L.assertion822ReservedSwitchedEdgesAt hL S R T) a D.head)
    (hconflict : ∀ (parent : Gamma.DPath)
      (q : _root_.Erdos599.DirectedPath.FinitePath Gamma.graph),
      parent ∈ Gamma.inessentialPaths L.limitWarp →
      q.start ∈ Gamma.source \ {R.record.initial} →
      q.finish = (selectedRequestTrace (L.popularAuxiliaryIndexed hL) S
        (L.reservedGroundedControls hL S R) r).initial →
      q.support ⊆ parent.support → q.edgeSet ⊆ parent.edgeSet →
      ∀ (D : LastDeletedHead q
          (L.assertion822ReservedSwitchedEdgesAt hL S R T)) u,
        (u, D.head) ∈ q.edgeSet →
        (u, D.head) ∈ forwardConflictCutEdgesAt
          (L.popularAuxiliaryIndexed hL) S
            (L.reservedGroundedControls hL S R) T →
        ∃ a ∈ Gamma.source \ {R.record.initial},
          Relation.ReflTransGen (fun x y ↦ (x, y) ∈
            L.assertion822ReservedSwitchedEdgesAt hL S R T) a D.head)
    (hboundary : ∀ (parent : Gamma.DPath)
      (q : _root_.Erdos599.DirectedPath.FinitePath Gamma.graph),
      parent ∈ Gamma.inessentialPaths L.limitWarp →
      q.start ∈ Gamma.source \ {R.record.initial} →
      q.finish = (selectedRequestTrace (L.popularAuxiliaryIndexed hL) S
        (L.reservedGroundedControls hL S R) r).initial →
      q.support ⊆ parent.support → q.edgeSet ⊆ parent.edgeSet →
      ∀ (D : LastDeletedHead q
          (L.assertion822ReservedSwitchedEdgesAt hL S R T)) u,
        (u, D.head) ∈ q.edgeSet →
        (u, D.head) ∈ residualLadderEdges
          (L.popularAuxiliaryIndexed hL) S → u ∈ T →
        ∃ a ∈ Gamma.source \ {R.record.initial},
          Relation.ReflTransGen (fun x y ↦ (x, y) ∈
            L.assertion822ReservedSwitchedEdgesAt hL S R T) a D.head) :
    ∃ a ∈ Gamma.source \ {R.record.initial},
      Relation.ReflTransGen (fun x y ↦ (x, y) ∈
        L.assertion822ReservedSwitchedEdgesAt hL S R T) a
        (selectedRequestTrace (L.popularAuxiliaryIndexed hL) S
          (L.reservedGroundedControls hL S R) r).initial := by
  apply R.selectedRequest_initial_rootedAt_of_lastDeletedHead_cases
  · exact strongSelectedPath_mem_groundedSourcePaths_reserved R r
  · exact strongSelectedPath_start_ne_reservedAuxiliarySource R r
  · exact hCE
  · exact hbackward
  · exact hconflict
  · exact hboundary

/-- Reserved-control specialization of
`selectedRequest_initial_rooted_withControls` for the frontier-stopped
switch. -/
theorem UnusedGroundedRecord.reservedSelectedRequest_initial_rootedAt
    (R : L.UnusedGroundedRecord hL S) (T : Set V)
    (r : Request (L.popularAuxiliaryInput hL.legal) S.cut)
    (hsurvives : ∀ (parent : Gamma.DPath)
        (q : _root_.Erdos599.DirectedPath.FinitePath Gamma.graph),
      parent ∈ Gamma.inessentialPaths L.limitWarp →
      q.start ∈ Gamma.source \ {R.record.initial} →
      q.finish =
          (selectedRequestTrace (L.popularAuxiliaryIndexed hL) S
            (L.reservedGroundedControls hL S R) r).initial →
      q.support ⊆ parent.support → q.edgeSet ⊆ parent.edgeSet →
      q.edgeSet ⊆ L.assertion822ReservedSwitchedEdgesAt hL S R T) :
    ∃ a ∈ Gamma.source \ {R.record.initial},
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈
          L.assertion822ReservedSwitchedEdgesAt hL S R T) a
        (selectedRequestTrace (L.popularAuxiliaryIndexed hL) S
          (L.reservedGroundedControls hL S R) r).initial := by
  apply R.selectedRequest_initial_rooted_withControls
  · exact strongSelectedPath_mem_groundedSourcePaths_reserved R r
  · exact strongSelectedPath_start_ne_reservedAuxiliarySource R r
  · exact hsurvives

/-- Every retained forward contact of an active reserved request is rooted
once grounded prefixes of selected sources and all nonreserved ladder-owner
anchors are rooted.  Reserved-record avoidance discharges the only owner
exclusion needed by the alternating transfer. -/
theorem UnusedGroundedRecord.reservedActiveRequestAt_retainedVertex_rooted
    (R : L.UnusedGroundedRecord hL S) (T : Set V)
    (c : ActiveControlRequestAt (L.popularAuxiliaryIndexed hL) S
      (L.reservedGroundedControls hL S R) T)
    (hprefix : ∀ (parent : Gamma.DPath)
        (q : _root_.Erdos599.DirectedPath.FinitePath Gamma.graph),
      parent ∈ Gamma.inessentialPaths L.limitWarp →
      q.start ∈ Gamma.source \ {R.record.initial} →
      q.finish =
          (selectedRequestTrace (L.popularAuxiliaryIndexed hL) S
            (L.reservedGroundedControls hL S R)
              (chosenRequest c.1)).initial →
      q.support ⊆ parent.support → q.edgeSet ⊆ parent.edgeSet →
      q.edgeSet ⊆ L.assertion822ReservedSwitchedEdgesAt hL S R T)
    (hparentRoot : ∀ (parent : Gamma.DPath), parent ∈ L.limitWarp →
      parent ≠ R.record → ∀ x ∈ parent.support,
        ∃ a ∈ Gamma.source \ {R.record.initial},
          Relation.ReflTransGen
            (fun u v ↦ (u, v) ∈
              L.assertion822ReservedSwitchedEdgesAt hL S R T) a x)
    {x : V}
    (hx : x ∈ retainedForwardVerticesAt T
      (selectedErasedCompression (L.popularAuxiliaryIndexed hL) S
        (L.reservedGroundedControls hL S R)
          (chosenRequest c.1)).path) :
    ∃ a ∈ Gamma.source \ {R.record.initial},
      Relation.ReflTransGen
        (fun u v ↦ (u, v) ∈
          L.assertion822ReservedSwitchedEdgesAt hL S R T) a x := by
  apply activeRequestAt_retainedForwardVertex_rooted_of_anchor_reachability
    (L.popularAuxiliaryIndexed hL) S
      (L.reservedGroundedControls hL S R) T c
  · exact R.reservedSelectedRequest_initial_rootedAt T
      (chosenRequest c.1) hprefix
  · intro l hl hldir parent hparent hsub
    have hparent' : parent ∈ L.limitWarp := hparent
    have hne : parent ≠ R.record :=
      R.backwardLink_parent_ne_record (chosenRequest c.1) l hl hldir
        parent hparent' hsub
    exact hparentRoot parent hparent' hne l.path.start
      (hsub.1 l.path.start_mem_support)
  · exact hx

/-- The inactive-control transfer with the reserved source and the actual
frontier-stopped relation filled in.  Its final premise is intentionally the
literal surviving suffix required by the generic transfer; minimality of a
separator does not imply this premise. -/
theorem UnusedGroundedRecord.reservedInactiveControlAt_rooted
    (R : L.UnusedGroundedRecord hL S) (T : Set V)
    (c : ControlRequest (L.popularAuxiliaryInput hL.legal) S.cut)
    (hc : ¬ IsActiveControlAt (L.popularAuxiliaryIndexed hL) S
      (L.reservedGroundedControls hL S R) T c)
    (hprefix : ∀
      (r : Request (L.popularAuxiliaryInput hL.legal) S.cut)
      (parent : Gamma.DPath)
      (q : _root_.Erdos599.DirectedPath.FinitePath Gamma.graph),
      parent ∈ Gamma.inessentialPaths L.limitWarp →
      q.start ∈ Gamma.source \ {R.record.initial} →
      q.finish =
          (selectedRequestTrace (L.popularAuxiliaryIndexed hL) S
            (L.reservedGroundedControls hL S R) r).initial →
      q.support ⊆ parent.support → q.edgeSet ⊆ parent.edgeSet →
      q.edgeSet ⊆ L.assertion822ReservedSwitchedEdgesAt hL S R T)
    (hparentRoot : ∀ (parent : Gamma.DPath), parent ∈ L.limitWarp →
      parent ≠ R.record → ∀ x ∈ parent.support,
        ∃ a ∈ Gamma.source \ {R.record.initial},
          Relation.ReflTransGen
            (fun u v ↦ (u, v) ∈
              L.assertion822ReservedSwitchedEdgesAt hL S R T) a x)
    (hsegmentSurvives : ∀
      (d : ActiveControlRequestAt (L.popularAuxiliaryIndexed hL) S
        (L.reservedGroundedControls hL S R) T)
      (Y : Gamma.DPath),
      Y ∈ exposedLadderPaths (L.popularAuxiliaryInput hL.legal)
        (strongSelectedPath (L.popularAuxiliaryIndexed hL) S
          (L.reservedGroundedControls hL S R) (chosenRequest d.1)) →
      ∀ x,
      x ∈ retainedForwardVerticesAt T
          (selectedErasedCompression (L.popularAuxiliaryIndexed hL) S
            (L.reservedGroundedControls hL S R)
              (chosenRequest d.1)).path →
      x ∈ Y.support → GroundingCut.BeforeEq Y x c.1 →
      ∀ p : _root_.Erdos599.DirectedPath.FinitePath Gamma.graph,
        p.start = x → p.finish = c.1 → p.edgeSet ⊆ Y.edgeSet →
          p.edgeSet ⊆ L.assertion822ReservedSwitchedEdgesAt hL S R T) :
    ∃ a ∈ Gamma.source \ {R.record.initial},
      Relation.ReflTransGen
        (fun u v ↦ (u, v) ∈
          L.assertion822ReservedSwitchedEdgesAt hL S R T) a c.1 := by
  apply inactiveControlAt_rooted_of_retainedContact
    (L.popularAuxiliaryIndexed hL) S
      (L.reservedGroundedControls hL S R) T
      (L.assertion822ReservedSwitchedEdgesAt hL S R T)
      (Gamma.source \ {R.record.initial}) c hc
  · intro d x hx
    apply R.reservedActiveRequestAt_retainedVertex_rooted T d
    · exact hprefix (chosenRequest d.1)
    · exact hparentRoot
    · exact hx
  · exact hsegmentSurvives

/-- Assemble pointwise source-rootedness of an arbitrary selected
subfrontier from the three literal classes in `BB`.  The old-request class
is phrased through untagged controls so that the active/inactive transfer
above can be used directly. -/
theorem UnusedGroundedRecord.reservedFrontier_rootedAt_of_cases
    (R : L.UnusedGroundedRecord hL S) (T : Set V)
    (hTsub : T ⊆ GroundingCut.BB
      (L.popularAuxiliaryInput hL.legal) S.cut)
    (hfinite : ∀ b,
      b ∈ (L.popularAuxiliaryInput hL.legal).finiteSource →
      PopularAuxiliary.Input.LambdaVertex.old b ∈ S.cut →
      ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen (fun x y ↦ (x, y) ∈
          L.assertion822ReservedSwitchedEdgesAt hL S R T) a b)
    (hcontrol : ∀ c : ControlRequest
      (L.popularAuxiliaryInput hL.legal) S.cut,
      ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen (fun x y ↦ (x, y) ∈
          L.assertion822ReservedSwitchedEdgesAt hL S R T) a c.1)
    (hblocking : ∀ P : (L.popularAuxiliaryInput hL.legal).Fragment,
      P ∈ GroundingCut.G0 (L.popularAuxiliaryInput hL.legal) S.cut →
      GroundingCut.IsBlockable
          (L.popularAuxiliaryInput hL.legal) S.cut P →
      ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen (fun x y ↦ (x, y) ∈
          L.assertion822ReservedSwitchedEdgesAt hL S R T) a
          (GroundingCut.blockingPoint
            (L.popularAuxiliaryInput hL.legal) S.cut P)) :
    ∀ t ∈ T, ∃ a ∈ Gamma.source \ {R.record.initial},
      Relation.ReflTransGen (fun x y ↦ (x, y) ∈
        L.assertion822ReservedSwitchedEdgesAt hL S R T) a t := by
  intro t ht
  rcases GroundingBBGeometry.mem_BB_finiteSourceWithCut_or_oldRequestExit_or_blockingPoint
      (hTsub ht) with
    ⟨htFinite, htCut⟩ | ⟨r, hrOld, hrExit⟩ |
      ⟨P, hPG0, hPblockable, hPt, _htSupport⟩
  · exact hfinite t htFinite htCut
  · cases r with
    | inl old =>
        have hold : old.1 = t := by
          simpa only [requestExit] using hrExit
        simpa only [oldRequestControl_val, hold] using
          hcontrol (oldRequestControl old)
    | inr edge => cases hrOld
  · rw [← hPt]
    exact hblocking P hPG0 hPblockable

end DWeb.KappaLadder
end Erdos599

#print axioms Erdos599.DWeb.KappaLadder.UnusedGroundedRecord.exists_selectedRequest_rootPrefix_withControls
#print axioms Erdos599.DWeb.KappaLadder.UnusedGroundedRecord.reservedSelectedRequest_initial_rootedAt_of_lastDeletedHead_cases
#print axioms Erdos599.DWeb.KappaLadder.UnusedGroundedRecord.reservedSelectedRequest_initial_rootedAt
#print axioms Erdos599.DWeb.KappaLadder.UnusedGroundedRecord.reservedInactiveControlAt_rooted
#print axioms Erdos599.DWeb.KappaLadder.UnusedGroundedRecord.reservedFrontier_rootedAt_of_cases
