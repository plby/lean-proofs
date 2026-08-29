/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.LambdaDecoder
import ErdosProblems.Erdos599.RunCompressor

/-!
# The reduced finite-route interface for the Lambda decoder

The fields of `Input.MicroTrace` deliberately record a continuous signed
walk, rather than asserting that its projected vertices are injective.  That
distinction matters: chronological erasure of a repeated projected vertex
drops edges, and hence cannot prove the exact edge-set equality required by
`Input.AlternatingCompression`.

This file isolates the exact positive bridge.  First it completes the finite
maximal-run assembly left implicit in `RunCompressor`.  It then packages the
additional reducedness certificate which is sufficient to turn a decoded
micro-trace into an exact alternating compression.  Thus later Section 8
arguments have a concrete obligation: prove the reduced route certificate
for the selected Lambda paths, or explicitly work with an erased subroute.
-/

noncomputable section

namespace Erdos599
namespace PopularAuxiliary

open Set DirectedPath Alternating

universe u v

variable {V : Type u} {I : Type v} {Gamma : DWeb V}

namespace Input

variable (L : Input Gamma I)

/-- The zero-step decoder is already the trivial alternating path.  Thus
the only genuine compression obligation is the nonempty signed route. -/
noncomputable def alternatingCompressionOfStepsNil
    {p : FinitePath L.lambda.graph} {T : L.MicroTrace p}
    (hsteps : T.steps = []) : L.AlternatingCompression p T where
  path := .trivial T.initial
  edgeSet_eq := by
    rw [AltPath.edgeSet_trivial, hsteps, signedEdgeSet_nil]
  initial_eq := AltPath.initial_trivial T.initial
  terminal_eq := by
    rw [AltPath.terminal?_trivial]
    congr 1
    exact RunsFromTo.start_eq_of_nil (hsteps ▸ T.runs)

theorem exists_alternatingCompression_of_steps_eq_nil
    {p : FinitePath L.lambda.graph} {T : L.MicroTrace p}
    (hsteps : T.steps = []) :
    Nonempty (L.AlternatingCompression p T) :=
  ⟨L.alternatingCompressionOfStepsNil hsteps⟩

/-- A reduced presentation of a decoded micro-trace by a finite injective
two-colour route.  The final field identifies the *raw* direction-oriented
edge set of that route with the signed micro-steps.  The generic run
compressor proves separately that maximal-run compression preserves this
raw edge set exactly.

Unlike continuity and validity, the existence of such an injective raw
presentation is not a consequence of `MicroTrace` when projected vertices
repeat. -/
structure ReducedRunPresentation {p : FinitePath L.lambda.graph}
    (T : L.MicroTrace p) where
  input : Erdos599.Alternating.RunCompressor.FiniteInput Gamma.graph
  initial_eq : input.vertex 0 = T.initial
  terminal_eq : input.vertex input.lastEdge = T.terminal
  rawEdgeSet_eq : input.orientedEdgeSet = signedEdgeSet T.steps

/-- A reduced run presentation gives the exact alternating compression
required by the switching decoder. -/
noncomputable def ReducedRunPresentation.toAlternatingCompression
    {p : FinitePath L.lambda.graph} {T : L.MicroTrace p}
    (R : L.ReducedRunPresentation T) : L.AlternatingCompression p T where
  path := .finite R.input.toFiniteRunWalk.toFiniteTrace
  edgeSet_eq := R.input.toFiniteTrace_edgeSet.trans R.rawEdgeSet_eq
  initial_eq := by
    rw [AltPath.initial, FiniteRunWalk.toFiniteTrace_initial]
    change R.input.vertex 0 = T.initial
    exact R.initial_eq
  terminal_eq := by
    rw [AltPath.terminal?, FiniteRunWalk.toFiniteTrace_terminal,
      R.input.toFiniteRunWalk_final_last]
    change some (R.input.vertex R.input.lastEdge) = some T.terminal
    rw [R.terminal_eq]

theorem exists_alternatingCompression_of_reducedRunPresentation
    {p : FinitePath L.lambda.graph} {T : L.MicroTrace p}
    (R : L.ReducedRunPresentation T) :
    Nonempty (L.AlternatingCompression p T) :=
  ⟨R.toAlternatingCompression⟩

end Input
end PopularAuxiliary
end Erdos599
