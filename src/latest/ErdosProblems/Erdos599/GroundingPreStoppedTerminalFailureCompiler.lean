/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingPreStoppedFailureCompiler
import ErdosProblems.Erdos599.GroundingPreStoppedFiniteTerminalOutcome

/-!
# Compiling terminal-normalized pre-stopped failures

This is the terminal-normalized refinement of
`GroundingPreStoppedFailureCompiler`.  The private finite collision branch
does not merely expose a decoded path: it carries the total
`FiniteSourceTerminalOutcome`.  Thus a consumer may switch immediately in
the successful branch, while the two remaining branches name the exact
normalization failure to repair.
-/

noncomputable section

open Set

namespace Erdos599
namespace DWeb.KappaLadder

open Alternating

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace Assertion822PreStoppedBoundaryObstruction

/-- The canonical decoder payload of the private finite branch, together
with its total terminal-contact outcome.  Unlike `PrivateFiniteExchange`,
this structure retains the `MicroTrace`, so the two failure constructors can
be repaired by inspecting the actual signed route. -/
structure CanonicalPrivateFiniteTerminalOutcome
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    {o : L.Assertion822PreStoppedBoundaryObstruction hL S R}
    (D : FirstBoundaryReduction o) where
  collision : BlockingFiniteTerminalCase D.reduced
  exchange : PrivateFiniteExchange D.reduced
  q : _root_.Erdos599.DirectedPath.FinitePath
    (L.popularAuxiliaryInput hL.legal).lambda.graph
  trace : (L.popularAuxiliaryInput hL.legal).MicroTrace q
  compression : FiniteTrace Gamma.graph
  terminal : V
  q_start : q.start = .old D.reduced.later
  q_target : q.finish ∈
    (L.popularAuxiliaryInput hL.legal).lambda.target
  q_avoids : (L.popularAuxiliaryInput hL.legal).lambda.Avoids q
    (S.cut \ {(.old D.reduced.later :
      (L.popularAuxiliaryInput hL.legal).LV)})
  q_private : q.support ∩ S.cut =
    {(.old D.reduced.later : (L.popularAuxiliaryInput hL.legal).LV)}
  q_targetPure : (L.popularAuxiliaryInput hL.legal).IsTargetPure q
  compression_eq : trace.erasedCompression.path = .finite compression
  trace_initial : trace.initial = D.reduced.later
  trace_terminal : trace.terminal = terminal
  terminal_target : terminal ∈
    (L.popularAuxiliaryInput hL.legal).targetMarkers
  terminal_outcome : FiniteSourceTerminalOutcome
    (L.popularAuxiliaryInput hL.legal).ladder.paths compression terminal

/-- The step/contact-level form of the terminal normalization outcome.  The
forward-overlap branch is pulled all the way back through loop erasure to an
actual signed decoder step; the contact branch displays the exact uncovered
vertex. -/
inductive CanonicalNormalizationOutcome
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    {o : L.Assertion822PreStoppedBoundaryObstruction hL S R}
    {D : FirstBoundaryReduction o}
    (data : CanonicalPrivateFiniteTerminalOutcome D) : Prop
  | switching
      (h : IsTerminalContactSwitching
        (L.popularAuxiliaryInput hL.legal).ladder.paths
        data.compression data.terminal)
  | forwardLadderStep
      (s : PopularAuxiliary.Input.SignedEdge V)
      (mem : s ∈ data.trace.runs.erasedSignedRoute.steps)
      (forward : s.direction = .forward)
      (ladder : s.edge ∈ Alternating.familyEdges
        (L.popularAuxiliaryInput hL.legal).ladder.paths)
  | uncoveredContact
      (x : V)
      (forward : x ∈
        (AltPath.finite data.compression).directionVertices .forward)
      (ladder : x ∈ Gamma.vertexSet
        (L.popularAuxiliaryInput hL.legal).ladder.paths)
      (not_backward : x ∉
        (AltPath.finite data.compression).directionVertices .backward)
      (not_terminal :
        (AltPath.finite data.compression).terminal? ≠ some x)

/-- Extract the literal signed-step or contact witness from the total
terminal outcome. -/
theorem CanonicalPrivateFiniteTerminalOutcome.normalizationOutcome
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    {o : L.Assertion822PreStoppedBoundaryObstruction hL S R}
    {D : FirstBoundaryReduction o}
    (data : CanonicalPrivateFiniteTerminalOutcome D) :
    CanonicalNormalizationOutcome data := by
  cases data.terminal_outcome with
  | switching h => exact .switching h
  | forwardUsesLadderEdge hnot =>
      by_contra hnone
      have hnoWitness : ∀ s : PopularAuxiliary.Input.SignedEdge V,
          ¬ (s ∈ data.trace.runs.erasedSignedRoute.steps ∧
            s.direction = .forward ∧
            s.edge ∈ Alternating.familyEdges
              (L.popularAuxiliaryInput hL.legal).ladder.paths) :=
        not_exists.mp (by
          intro hexists
          apply hnone
          rcases hexists with ⟨s, hs, hd, he⟩
          exact .forwardLadderStep s hs hd he)
      apply hnot
      have hoff :=
        GroundingFiniteSourceDuplicateExchange.erasedCompression_forwardLinksOff_of_forward_not_mem
          data.trace (fun {s} hs hd he ↦
            hnoWitness s ⟨hs, hd, he⟩)
      simpa only [data.compression_eq] using hoff
  | uncoveredForwardContact hnot =>
      simp only [PopularAuxiliary.Input.ForwardVertexContactsCoveredAtTerminal,
        not_forall, not_or] at hnot
      obtain ⟨x, hforward, hladder, hnotBackward, hnotTerminal⟩ := hnot
      exact .uncoveredContact x hforward hladder hnotBackward hnotTerminal

/-- The total first-boundary classifier with the private finite branch
refined by its exact terminal-contact outcome. -/
inductive TerminalFailureOutcome
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    (o : L.Assertion822PreStoppedBoundaryObstruction hL S R) : Prop
  | earlierFinite
      (D : FirstBoundaryReduction o)
      (earlier : FiniteCase hL S D.reduced.earlier)
  | earlierControl
      (D : FirstBoundaryReduction o)
      (earlier : ControlCase hL S D.reduced.earlier)
  | privateFinite
      (D : FirstBoundaryReduction o)
      (data : CanonicalPrivateFiniteTerminalOutcome D)
  | selectedDeparture
      (D : FirstBoundaryReduction o)
      (departure : FirstSelectedDeparture D)
  | blockingToControl
      (D : FirstBoundaryReduction o)
      (earlier : BlockingCase hL S D.reduced.earlier)
      (later : ControlCase hL S D.reduced.later)
  | blockingToBlocking
      (D : FirstBoundaryReduction o)
      (earlier : BlockingCase hL S D.reduced.earlier)
      (later : BlockingCase hL S D.reduced.later)

/-- Every ordered pre-stopped collision has a terminal-normalized total
failure outcome. -/
theorem terminalFailureOutcome
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    (o : L.Assertion822PreStoppedBoundaryObstruction hL S R) :
    TerminalFailureOutcome o := by
  cases o.firstBoundaryFailureOutcome with
  | earlierFinite D hearlier =>
      exact .earlierFinite D hearlier
  | earlierControl D hearlier =>
      exact .earlierControl D hearlier
  | privateFinite D hcollision hexchange =>
      obtain ⟨q, T, Q, y, hqStart, hqTarget, hqAvoid, hqPrivate,
          hqPure, hcompression, hTinitial, hTterminal, hyTarget,
          hnoForward, hback⟩ :=
        hexchange.exists_microTrace_compression hcollision
      have hQinitial : Q.initial = D.reduced.later := by
        have h := T.erasedCompression.initial_eq.trans hTinitial
        rw [hcompression] at h
        change Q.initial = D.reduced.later at h
        exact h
      have hQterminal : Q.terminal = y := by
        have h := T.erasedCompression.terminal_eq.trans
          (congrArg some hTterminal)
        simpa only [hcompression, AltPath.terminal?_finite,
          Option.some.injEq] using h
      have hcollision' := hcollision
      have hcollisionCopy := hcollision
      obtain ⟨P, _hPG0, _hblockable, _hpoint, hPterminal,
          hfinite⟩ := hcollisionCopy
      have hparentGrounded :=
        L.fragment_parent_mem_groundedRecords_of_finiteSource_mem_support
          hL.legal P hfinite.1 (Gamma.terminal_mem_support hPterminal)
      have htargetDisjoint :=
        L.groundedRecord_support_disjoint_targetMarkers
          hL.legal hparentGrounded
      have hne : Q.initial ≠ y := by
        rw [hQinitial]
        intro heq
        exact Set.disjoint_left.1 htargetDisjoint
          (heq ▸ P.support_subset
            (Gamma.terminal_mem_support hPterminal)) hyTarget
      have hinitial : Q.initial ∈ Gamma.vertexSet
          (L.popularAuxiliaryInput hL.legal).ladder.paths := by
        rw [hQinitial]
        exact ⟨P.parent, P.parent_mem,
          P.support_subset (Gamma.terminal_mem_support hPterminal)⟩
      have houtcome := L.finiteSourceTerminalOutcome hL.legal hback
        hinitial hne hQterminal hyTarget hnoForward
      exact .privateFinite D {
        collision := hcollision'
        exchange := hexchange
        q := q
        trace := T
        compression := Q
        terminal := y
        q_start := hqStart
        q_target := hqTarget
        q_avoids := hqAvoid
        q_private := hqPrivate
        q_targetPure := hqPure
        compression_eq := hcompression
        trace_initial := hTinitial
        trace_terminal := hTterminal
        terminal_target := hyTarget
        terminal_outcome := houtcome }
  | selectedDeparture D hdeparture =>
      exact .selectedDeparture D hdeparture
  | blockingToControl D hearlier hlater =>
      exact .blockingToControl D hearlier hlater
  | blockingToBlocking D hearlier hlater =>
      exact .blockingToBlocking D hearlier hlater

end Assertion822PreStoppedBoundaryObstruction

/-- Construction-specific repairs of terminal-normalized root and collision
outcomes compile to the output-or-hindrance disjunction used by the grounding
theorem. -/
theorem assertion822Output_or_hindrance_of_preStoppedTerminalFailureRepairs
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    (repairRoot : ∀ (R : L.UnusedGroundedRecord hL S)
        (O : L.Assertion822PreStoppedRootObstruction hL S R),
      O.FailureOutcome →
        ∃ W : Set Gamma.DPath, Gamma.IsHindrance W)
    (repairBoundary : ∀ (R : L.UnusedGroundedRecord hL S)
        (O : L.Assertion822PreStoppedBoundaryObstruction hL S R),
      O.TerminalFailureOutcome →
        ∃ W : Set Gamma.DPath, Gamma.IsHindrance W) :
    Nonempty (GroundingFinalAssembly.Assertion822Output
        (L.popularAuxiliaryInput hL.legal) S.cut) ∨
      ∃ W : Set Gamma.DPath, Gamma.IsHindrance W := by
  apply L.assertion822Output_or_hindrance_of_preStoppedFailureRepairs hL S
    repairRoot
  intro R O _
  exact repairBoundary R O O.terminalFailureOutcome

end DWeb.KappaLadder
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.Assertion822PreStoppedBoundaryObstruction.CanonicalPrivateFiniteTerminalOutcome.normalizationOutcome
#print axioms
  Erdos599.DWeb.KappaLadder.Assertion822PreStoppedBoundaryObstruction.terminalFailureOutcome
#print axioms
  Erdos599.DWeb.KappaLadder.assertion822Output_or_hindrance_of_preStoppedTerminalFailureRepairs
