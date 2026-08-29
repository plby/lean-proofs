/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingGroundedBoundaryFiniteTerminal

/-!
# Decoder provenance for the split-grounded finite boundary exchange

The geometry-only terminal outcome does not retain the signed decoder route.
That information is indispensable when the erased compression either uses a
forward ladder edge or hides a forward ladder contact.  This module retains
the actual private auxiliary path and its `MicroTrace`, and pulls either
failure back to a literal signed step/contact.  No ordinary-legality witness
is used.
-/

noncomputable section

open Cardinal Set

namespace Erdos599

open DirectedPath Alternating

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace SplitGroundingFiniteTerminalFailure

/-- Recover the decoder micro-trace without importing the stale legacy
grounded-record wrapper. -/
theorem exists_microTrace_of_finiteSource_target_path
    {J : Type u} (I : PopularAuxiliary.Input Gamma J)
    (q : FinitePath I.lambda.graph) {c : V}
    (hqStart : q.start = .old c) (hcFinite : c ∈ I.finiteSource)
    (hqTarget : q.finish ∈ I.lambda.target) :
    ∃ T : I.MicroTrace q,
      T.initial = c ∧ T.terminal ∈ I.targetMarkers ∧
        T.erasedCompression.path.initial = c ∧
        T.erasedCompression.path.terminal? = some T.terminal ∧
        (∀ z, (T.terminal, z) ∉
          T.erasedCompression.path.directionEdges .forward) ∧
        BackwardLinksOn I.ladder.paths T.erasedCompression.path := by
  have hqSource : q.start ∈ I.lambda.source := by
    rw [hqStart, I.mem_lambda_source_old]
    exact hcFinite
  let T := I.decodeFinitePath q hqSource hqTarget
  have hTInitial : T.initial = c := by
    classical
    simp only [T]
    unfold PopularAuxiliary.Input.decodeFinitePath
    split
    · rename_i x hx
      exact PopularAuxiliary.Input.LambdaVertex.old.inj
        (x.2.2.symm.trans hqStart)
    · rename_i i hi
      exact False.elim (by
        have hproxy :
            (PopularAuxiliary.Input.LambdaVertex.proxy i.1 : I.LV) =
              .old c := i.2.symm.trans hqStart
        cases hproxy)
  have hback : BackwardLinksOn I.ladder.paths
      T.erasedCompression.path := by
    apply T.runs.erasedSignedRoute.compressionOfValid_backwardLinksOn
      (fun {_s} hs ↦ T.valid _
        (T.runs.erasedSignedRoute.steps_sublist.subset hs))
      I.ladder.disjoint
    intro s hs hdir
    simpa [PopularAuxiliary.Input.familyEdges, familyEdges] using
      T.backward_on_ladder s
        (T.runs.erasedSignedRoute.steps_sublist.subset hs) hdir
  refine ⟨T, hTInitial, T.target_endpoint,
    T.erasedCompression.initial_eq.trans hTInitial,
    T.erasedCompression.terminal_eq, ?_, hback⟩
  intro z
  exact
    GroundingFiniteSourceDuplicateExchangeCore.erasedCompression_terminal_not_forward_source
      T

/-- Forward/reference disjointness follows pointwise from the retained
signed route. -/
theorem erasedCompression_forwardLinksOff_of_forward_not_mem
    {J : Type u} {I : PopularAuxiliary.Input Gamma J}
    {p : FinitePath I.lambda.graph} (T : I.MicroTrace p)
    (hforward : ∀ {s : PopularAuxiliary.Input.SignedEdge V},
      s ∈ T.runs.erasedSignedRoute.steps →
      s.direction = .forward →
      s.edge ∉ familyEdges I.ladder.paths) :
    ForwardLinksOff I.ladder.paths T.erasedCompression.path := by
  intro l hl hldir
  rw [Set.disjoint_left]
  intro e hel heFamily
  have heDirection : e ∈
      T.erasedCompression.path.directionEdges .forward := by
    simp only [AltPath.directionEdges, Set.mem_iUnion]
    exact ⟨l, hl, hldir, hel⟩
  let E := T.runs.erasedSignedRoute
  have hvalid : ∀ {s : PopularAuxiliary.Input.SignedEdge V},
      s ∈ E.steps →
      PopularAuxiliary.Input.SignedEdge.Valid (Gamma := Gamma) s :=
    fun {_s} hs ↦ T.valid _ (E.steps_sublist.subset hs)
  obtain ⟨s, hs, hsForward, hsEdge⟩ :=
    E.compressionOfValid_directionEdges_subset_directedSignedEdgeSet
      hvalid .forward heDirection
  apply hforward hs hsForward
  simpa only [hsEdge] using heFamily

end SplitGroundingFiniteTerminalFailure

namespace DWeb.KappaLadder

variable {L : Gamma.KappaLadder kappa} {hL : L.IsSplitKappaHindrance}
  {hground : Stationary.IsStationaryBelow kappa L.phiGround}
  {S : Popular.PopularSeparator
    (L.splitGroundedPopularAuxiliaryIndexed hL hground)}
  {K : GroundingSelection.Controls S}

private abbrev FiniteFailureInput :=
  L.splitGroundedPopularAuxiliaryInput hL.legal

/-- The private finite collision with the decoder provenance needed for a
source-faithful last-contact normalization. -/
structure SplitGroundedPrivateFiniteTerminalData
    {R : L.SplitGroundedUnusedRecord hL hground S K}
    {O : L.SplitGroundedPreStoppedBoundaryObstruction R}
    (hcase : SplitGroundedBlockingFiniteTerminalCase O) where
  q : FinitePath (FiniteFailureInput (L := L) (hL := hL)).lambda.graph
  trace : (FiniteFailureInput (L := L) (hL := hL)).MicroTrace q
  compression : FiniteTrace Gamma.graph
  terminal : V
  q_start : q.start = .old O.later
  q_target : q.finish ∈
    (FiniteFailureInput (L := L) (hL := hL)).lambda.target
  q_avoids : (FiniteFailureInput (L := L) (hL := hL)).lambda.Avoids q
    (S.cut \ {(.old O.later :
      (FiniteFailureInput (L := L) (hL := hL)).LV)})
  q_private : q.support ∩ S.cut =
    {(.old O.later : (FiniteFailureInput (L := L) (hL := hL)).LV)}
  q_targetPure :
    (FiniteFailureInput (L := L) (hL := hL)).IsTargetPure q
  compression_eq : trace.erasedCompression.path = .finite compression
  trace_initial : trace.initial = O.later
  trace_terminal : trace.terminal = terminal
  terminal_target : terminal ∈
    (FiniteFailureInput (L := L) (hL := hL)).targetMarkers
  terminal_outcome : TerminalContactGeometryOutcome
    (FiniteFailureInput (L := L) (hL := hL)).ladder.paths
    compression terminal

/-- Reconstruct the literal decoder trace from the private auxiliary path
already supplied by the split-legal finite exchange. -/
theorem SplitGroundedBlockingFiniteTerminalCase.exists_privateFiniteTerminalData
    {R : L.SplitGroundedUnusedRecord hL hground S K}
    {O : L.SplitGroundedPreStoppedBoundaryObstruction R}
    (hcase : SplitGroundedBlockingFiniteTerminalCase O) :
    Nonempty (L.SplitGroundedPrivateFiniteTerminalData hcase) := by
  obtain ⟨P, q, _Q₀, _y₀, _hPG0, hPterminal, hqStart, hqTarget,
      hqAvoid, hqPrivate, hqPure, _hQInitial, _hQTerminal, _hyTarget,
      hyParent, hlaterFrontier, _hyInitial, _hnoForward, _hback⟩ :=
    hcase.exists_private_finite_exchange
  obtain ⟨_Pcase, _hPG0case, _hblockable, _hpoint,
      _hterminalCase, hlaterFinite, _hlaterCut⟩ := hcase
  obtain ⟨T, hTInitial, hyTarget, hAInitial, hATerminal,
      hnoForward, hback⟩ :=
    SplitGroundingFiniteTerminalFailure.exists_microTrace_of_finiteSource_target_path
      (FiniteFailureInput (L := L) (hL := hL)) q hqStart
      hlaterFinite hqTarget
  have hparentGrounded :=
    L.splitGrounded_fragment_parent_grounded_of_finiteSource_mem_support
      (hL := hL) P hlaterFinite
        (Gamma.terminal_mem_support hPterminal)
  obtain ⟨a, haGround, hchosen⟩ := hparentGrounded
  obtain ⟨parent, hparentChosen, hparentSource⟩ := haGround
  have hparentEq : parent = P.parent :=
    Option.some.inj (hparentChosen.symm.trans hchosen)
  have hdisjoint : Disjoint P.parent.support
      (FiniteFailureInput (L := L) (hL := hL)).targetMarkers := by
    subst parent
    exact L.splitGrounded_record_support_disjoint_targetMarkers
      (hL := hL) hparentChosen hparentSource
  have hTNotParent : T.terminal ∉ P.parent.support := by
    intro hmem
    exact Set.disjoint_left.1 hdisjoint hmem hyTarget
  have hne : T.initial ≠ T.terminal := by
    rw [hTInitial]
    intro heq
    apply hTNotParent
    exact heq ▸ P.support_subset (Gamma.terminal_mem_support hPterminal)
  cases hA : T.erasedCompression.path with
  | trivial a =>
      have hai : a = T.initial := by
        have haLater : a = O.later := by
          simpa only [hA, AltPath.initial_trivial] using hAInitial
        exact haLater.trans hTInitial.symm
      have hat : a = T.terminal := by
        have : (some a : Option V) = some T.terminal := by
          simpa only [hA, AltPath.terminal?_trivial] using hATerminal
        exact Option.some.inj this
      exact False.elim (hne (hai.symm.trans hat))
  | infinite r =>
      have : (none : Option V) = some T.terminal := by
        simpa only [hA, AltPath.terminal?_infinite] using hATerminal
      cases this
  | finite Q =>
      have hQinitial : Q.initial = O.later := by
        rw [hA] at hAInitial
        change Q.initial = O.later at hAInitial
        exact hAInitial
      have hQterminal : Q.terminal = T.terminal := by
        rw [hA] at hATerminal
        simpa only [AltPath.terminal?_finite,
          Option.some.injEq] using hATerminal
      have hinitial : Q.initial ∈ Gamma.vertexSet
          (FiniteFailureInput (L := L) (hL := hL)).ladder.paths := by
        rw [hQinitial]
        exact terminalFrontier_subset_vertexSet _ hlaterFrontier
      have hwarp : Gamma.IsWarp
          (FiniteFailureInput (L := L) (hL := hL)).ladder.paths := by
        simpa [FiniteFailureInput, splitGroundedPopularAuxiliaryInput,
          KappaLadder.limitWarp]
          using hL.legal.warpStages (Ladder.finalStage kappa)
      have houtcome : TerminalContactGeometryOutcome
          (FiniteFailureInput (L := L) (hL := hL)).ladder.paths
          Q T.terminal := by
        apply finiteSourceTerminalOutcome_of_geometry hwarp
        · simpa only [hA] using hback
        · exact hinitial
        · exact L.splitGrounded_targetMarker_mem_initialSet_limitWarp
            (hL := hL) hyTarget
        · simpa only [hQinitial, hTInitial] using hne
        · exact hQterminal
        · simpa only [hA] using hnoForward
      exact ⟨{
        q := q
        trace := T
        compression := Q
        terminal := T.terminal
        q_start := hqStart
        q_target := hqTarget
        q_avoids := hqAvoid
        q_private := hqPrivate
        q_targetPure := hqPure
        compression_eq := hA
        trace_initial := hTInitial
        trace_terminal := rfl
        terminal_target := hyTarget
        terminal_outcome := houtcome }⟩

/-- Literal step/contact form of the two genuine normalization failures. -/
inductive SplitGroundedPrivateFiniteNormalizationOutcome
    {R : L.SplitGroundedUnusedRecord hL hground S K}
    {O : L.SplitGroundedPreStoppedBoundaryObstruction R}
    {hcase : SplitGroundedBlockingFiniteTerminalCase O}
    (data : L.SplitGroundedPrivateFiniteTerminalData hcase) : Prop
  | switching
      (h : IsTerminalContactSwitching
        (FiniteFailureInput (L := L) (hL := hL)).ladder.paths
        data.compression data.terminal)
  | forwardLadderStep
      (s : PopularAuxiliary.Input.SignedEdge V)
      (mem : s ∈ data.trace.runs.erasedSignedRoute.steps)
      (forward : s.direction = .forward)
      (ladder : s.edge ∈ familyEdges
        (FiniteFailureInput (L := L) (hL := hL)).ladder.paths)
  | uncoveredContact
      (x : V)
      (forward : x ∈
        (AltPath.finite data.compression).directionVertices .forward)
      (ladder : x ∈ Gamma.vertexSet
        (FiniteFailureInput (L := L) (hL := hL)).ladder.paths)
      (not_backward : x ∉
        (AltPath.finite data.compression).directionVertices .backward)
      (not_terminal :
        (AltPath.finite data.compression).terminal? ≠ some x)

/-- Pull the total geometry outcome back to the actual signed decoder
route. -/
theorem SplitGroundedPrivateFiniteTerminalData.normalizationOutcome
    {R : L.SplitGroundedUnusedRecord hL hground S K}
    {O : L.SplitGroundedPreStoppedBoundaryObstruction R}
    {hcase : SplitGroundedBlockingFiniteTerminalCase O}
    (data : L.SplitGroundedPrivateFiniteTerminalData hcase) :
    L.SplitGroundedPrivateFiniteNormalizationOutcome data := by
  cases data.terminal_outcome with
  | switching h => exact .switching h
  | forwardUsesReferenceEdge hnot =>
      by_contra hnone
      have hnoWitness : ∀ s : PopularAuxiliary.Input.SignedEdge V,
          ¬ (s ∈ data.trace.runs.erasedSignedRoute.steps ∧
            s.direction = .forward ∧
            s.edge ∈ familyEdges
              (FiniteFailureInput (L := L) (hL := hL)).ladder.paths) :=
        not_exists.mp (by
          intro hexists
          apply hnone
          rcases hexists with ⟨s, hs, hd, he⟩
          exact .forwardLadderStep s hs hd he)
      apply hnot
      have hoff :=
        SplitGroundingFiniteTerminalFailure.erasedCompression_forwardLinksOff_of_forward_not_mem
          data.trace (fun {s} hs hd he ↦
            hnoWitness s ⟨hs, hd, he⟩)
      simpa only [data.compression_eq] using hoff
  | uncoveredForwardContact hnot =>
      simp only [PopularAuxiliary.Input.ForwardVertexContactsCoveredAtTerminal,
        not_forall, not_or] at hnot
      obtain ⟨x, hforward, hladder, hnotBackward, hnotTerminal⟩ := hnot
      exact .uncoveredContact x hforward hladder hnotBackward hnotTerminal

end DWeb.KappaLadder
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.SplitGroundedBlockingFiniteTerminalCase.exists_privateFiniteTerminalData
#print axioms
  Erdos599.DWeb.KappaLadder.SplitGroundedPrivateFiniteTerminalData.normalizationOutcome
