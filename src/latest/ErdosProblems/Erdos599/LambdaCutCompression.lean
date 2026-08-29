/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.LambdaCompressionBridge

/-!
# Lossless decoding up to an auxiliary cut

`Input.decodeFinitePath` is deliberately specialized to a path ending in
the auxiliary target.  The Section 8 selected warp, however, ends at the
popular cut, whose members may be old-vertex or edge gadgets.  Reusing the
target decoder there would assert a false endpoint hypothesis.

This file supplies the endpoint-relaxed analogue.  It retains every field
used by switching and compression, and drops only membership of the final
original vertex in `targetMarkers`.
-/

noncomputable section

namespace Erdos599
namespace PopularAuxiliary

open Set DirectedPath Alternating

universe u v

variable {V : Type u} {I : Type v} {Gamma : DWeb V}

namespace Input

variable (L : Input Gamma I)

/-- A lossless signed route ending at any gadget with an original exit. -/
structure CutMicroTrace (p : FinitePath L.lambda.graph) where
  steps : List (SignedEdge V)
  initial : V
  terminal : V
  runs : RunsFromTo initial terminal steps
  edgeSet_eq : signedEdgeSet steps = L.decodedRouteEdges p
  valid : ∀ s, s ∈ steps → SignedEdge.Valid (Gamma := Gamma) s
  backward_on_ladder : ∀ s, s ∈ steps → s.direction = .backward →
    s.edge ∈ L.familyEdges
  source_endpoint :
    (∃ x ∈ L.finiteSource, initial = x) ∨
      ∃ i : I, initial ∈ (L.proxyPath i).support

/-- Type-valued choice of the original exit of the final gadget. -/
abbrev ExitEndpointChoice (p : FinitePath L.lambda.graph) :=
  {z : V // L.gadgetExit p.finish = some z}

noncomputable def chooseExitEndpoint
    (p : FinitePath L.lambda.graph)
    (hexit : ∃ z, L.gadgetExit p.finish = some z) :
    L.ExitEndpointChoice p :=
  ⟨Classical.choose hexit, Classical.choose_spec hexit⟩

/-- Decode a source-starting finite auxiliary path up to an arbitrary
old/edge gadget. -/
noncomputable def decodeFinitePathToExit
    (p : FinitePath L.lambda.graph)
    (hstart : p.start ∈ L.lambda.source)
    (hexit : ∃ z, L.gadgetExit p.finish = some z) :
    L.CutMicroTrace p := by
  let z := L.chooseExitEndpoint p hexit
  match hs : L.chooseSourceEndpoint p hstart with
  | .inl x =>
      have hentry : L.gadgetEntry p.start = some x.1 := by
        exact (congrArg L.gadgetEntry x.2.2).trans rfl
      exact {
        steps := L.decodeWalkSteps p.walk
        initial := x.1
        terminal := z.1
        runs := L.decodeWalkSteps_runs_from_entry p.walk hentry z.2
        edgeSet_eq := L.signedEdgeSet_decodeWalkSteps p hstart
        valid := fun _ ht ↦ L.decodeWalkSteps_valid p hstart ht
        backward_on_ladder := fun _ ht hb ↦
          L.decodeWalkSteps_backward_on_ladder p hstart ht hb
        source_endpoint := Or.inl ⟨x.1, x.2.1, rfl⟩ }
  | .inr i =>
      let xr : {x : V // x ∈ (L.proxyPath i.1).support ∧
          RunsFromTo x z.1 (L.decodeWalkSteps p.walk)} :=
        Classical.choice (by
          obtain ⟨x, hx, hrun⟩ :=
            L.decodeWalkSteps_runs_from_eq_proxy p.walk i.2 z.2
          exact ⟨⟨x, hx, hrun⟩⟩)
      exact {
        steps := L.decodeWalkSteps p.walk
        initial := xr.1
        terminal := z.1
        runs := xr.2.2
        edgeSet_eq := L.signedEdgeSet_decodeWalkSteps p hstart
        valid := fun _ ht ↦ L.decodeWalkSteps_valid p hstart ht
        backward_on_ladder := fun _ ht hb ↦
          L.decodeWalkSteps_backward_on_ladder p hstart ht hb
        source_endpoint := Or.inr ⟨i.1, xr.2.1⟩ }

@[simp] theorem decodeFinitePathToExit_steps
    (p : FinitePath L.lambda.graph)
    (hstart : p.start ∈ L.lambda.source)
    (hexit : ∃ z, L.gadgetExit p.finish = some z) :
    (L.decodeFinitePathToExit p hstart hexit).steps =
      L.decodeWalkSteps p.walk := by
  classical
  unfold decodeFinitePathToExit
  cases hs : L.chooseSourceEndpoint p hstart <;> rfl

/-- An exact alternating compression of a cut-ending decoded route. -/
structure CutAlternatingCompression (p : FinitePath L.lambda.graph)
    (T : L.CutMicroTrace p) where
  path : AltPath Gamma.graph
  edgeSet_eq : path.edgeSet = signedEdgeSet T.steps
  initial_eq : path.initial = T.initial
  terminal_eq : path.terminal? = some T.terminal

theorem CutAlternatingCompression.edgeSet_eq_decodedRouteEdges
    {p : FinitePath L.lambda.graph} {T : L.CutMicroTrace p}
    (C : L.CutAlternatingCompression p T) :
    C.path.edgeSet = L.decodedRouteEdges p :=
  C.edgeSet_eq.trans T.edgeSet_eq

theorem CutAlternatingCompression.switchData_eq
    {p : FinitePath L.lambda.graph} {T : L.CutMicroTrace p}
    (C : L.CutAlternatingCompression p T) :
    L.decodedSwitchData p =
      Alternating.Cyclowarp.application L.ladder.paths C.path :=
  L.decodedSwitchData_eq_application_of_edgeSet p C.path
    C.edgeSet_eq_decodedRouteEdges

theorem CutAlternatingCompression.realizedBy
    {p : FinitePath L.lambda.graph} {T : L.CutMicroTrace p}
    (C : L.CutAlternatingCompression p T) (W : Set Gamma.DPath)
    (hW : (Alternating.Cyclowarp.application
      L.ladder.paths C.path).RealizedBy W) :
    (L.decodedSwitchData p).RealizedBy W := by
  rw [C.switchData_eq]
  exact hW

/-- The reduced finite-route certificate for a cut-ending trace. -/
structure CutReducedRunPresentation
    {p : FinitePath L.lambda.graph} (T : L.CutMicroTrace p) where
  input : Erdos599.Alternating.RunCompressor.FiniteInput Gamma.graph
  initial_eq : input.vertex 0 = T.initial
  terminal_eq : input.vertex input.lastEdge = T.terminal
  rawEdgeSet_eq : input.orientedEdgeSet = signedEdgeSet T.steps

noncomputable def CutReducedRunPresentation.toCutAlternatingCompression
    {p : FinitePath L.lambda.graph} {T : L.CutMicroTrace p}
    (R : L.CutReducedRunPresentation T) :
    L.CutAlternatingCompression p T where
  path := .finite R.input.toFiniteRunWalk.toFiniteTrace
  edgeSet_eq := R.input.toFiniteTrace_edgeSet.trans R.rawEdgeSet_eq
  initial_eq := by
    rw [AltPath.initial, FiniteRunWalk.toFiniteTrace_initial]
    exact R.initial_eq
  terminal_eq := by
    rw [AltPath.terminal?, FiniteRunWalk.toFiniteTrace_terminal,
      R.input.toFiniteRunWalk_final_last]
    exact congrArg some R.terminal_eq

end Input
end PopularAuxiliary
end Erdos599
