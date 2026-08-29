/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HindranceGrounding
import ErdosProblems.Erdos599.LambdaDecoder

/-!
# The chronology input for the Section 8 auxiliary web

This file isolates the precise remaining issue in Assertion 8.12.  In the
source paper the path recorded at stage `a` is already inessential in
`Y_a`; consequently Lemmas 7.19--7.20 put its finite terminal in
`RF°(T_a)`.  The present ladder API instead defines the available paths at
`a` to be the inessential paths of the *successor* warp `Y_(a+1)`.

The first theorem below records exactly what follows from that definition:
the terminal is in the strict roof of the successor warp's terminal
frontier.  It does not put the terminal in the strict roof of `T_a`.

The final theorem is a formal obstruction certificate.  If a finite path
first recorded at `a` has an edge to a target marker born at the same stage,
then the corresponding one-edge path in `Lambda` has equal source and target
indices.  Thus the strict descent required by Assertion 8.12 is false unless
the ladder legality package rules out this same-stage configuration.  None
of the current fields of `KappaLadder.IsLegal` states the needed
current-stage strict-roof invariant.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace DWeb

open DirectedPath

universe u

variable {V : Type u} {Gamma : DWeb V}

namespace KappaLadder

/-- The strongest immediate strict-roof conclusion supplied by the current
successor-normalized bookkeeping definition. -/
theorem chosen_finite_terminal_mem_strictRoof_successorFrontier
    {kappa : Cardinal.{u}} (L : Gamma.KappaLadder kappa)
    (hlegal : L.IsLegal) {a : Ladder.Stage kappa} {p : Gamma.DPath}
    {x : V} (hchosen : L.chosen a = some p)
    (hterminal : Gamma.terminal? p = some x) :
    x ∈ Gamma.strictRoof
      (Gamma.terminalFrontier (L.successorWarp a)) := by
  have hpAvailable : p ∈ L.bookkeeping.available a :=
    L.bookkeeping.chosen_mem_available hlegal.validBookkeeping hchosen
  exact Gamma.terminal_mem_strictRoof_of_mem_inessentialPaths
    hpAvailable.1 hterminal

/-- The exact pathwise inequality demanded by Assertion 8.12, named here
so that the obstruction theorem can state its conclusion without hiding
any part of the desired result. -/
def AuxiliaryStrictDescent {kappa : Cardinal.{u}}
    (L : Gamma.KappaLadder kappa) (hlegal : L.IsLegal) : Prop :=
  ∀ (q : FinitePath (L.popularAuxiliaryInput hlegal).lambda.graph)
    (hstart : q.start ∈ (L.popularAuxiliaryInput hlegal).lambda.source)
    (hfinish : q.finish ∈ (L.popularAuxiliaryInput hlegal).lambda.target),
    (L.popularAuxiliaryInput hlegal).targetIndex
        (L.targetMarkerIndex hlegal) ⟨q.finish, hfinish⟩ <
      (L.popularAuxiliaryInput hlegal).sourceIndex
        L.finiteTerminalIndex L.groundedInfiniteIndex ⟨q.start, hstart⟩

/-- A directed edge between distinct vertices is a one-edge finite path. -/
private def oneEdgeFinitePath {W : Type u} {D : Digraph W}
    {x y : W} (hxy : D.Adj x y) (hne : x ≠ y) : FinitePath D where
  start := x
  finish := y
  walk := .cons hxy .nil
  isPath := by
    simp only [Walk.IsPath, Walk.support_cons, Walk.support_nil]
    simp [hne]

@[simp] private theorem oneEdgeFinitePath_start
    {W : Type u} {D : Digraph W} {x y : W}
    (hxy : D.Adj x y) (hne : x ≠ y) :
    (oneEdgeFinitePath hxy hne).start = x := rfl

@[simp] private theorem oneEdgeFinitePath_finish
    {W : Type u} {D : Digraph W} {x y : W}
    (hxy : D.Adj x y) (hne : x ≠ y) :
    (oneEdgeFinitePath hxy hne).finish = y := rfl

/-- A same-stage finite-record-to-target-marker edge gives a literal
one-edge counterexample to strict index descent in `Lambda`.

This theorem is useful as an audit certificate: a proof of unconditional
Assertion 8.12 from `IsLegal` must, in particular, derive that the hypotheses
below are inconsistent. -/
theorem not_auxiliaryStrictDescent_of_sameStage_arc
    {kappa : Cardinal.{u}} (L : Gamma.KappaLadder kappa)
    (hlegal : L.IsLegal) {a : Ladder.Stage kappa}
    {p : Gamma.DPath} {x y : V}
    (haGround : a ∈ L.phiGround)
    (haFinite : a ∈ L.phiFinite)
    (hchosen : L.chosen a = some p)
    (hterminal : Gamma.terminal? p = some x)
    (hmarker : L.marker a = some y)
    (hyEssential : y ∈ Gamma.vertexSet
      (Gamma.essentialWarpPart L.limitWarp))
    (hxy : Gamma.graph.Adj x y) (hne : x ≠ y) :
    ¬ L.AuxiliaryStrictDescent hlegal := by
  let I := L.popularAuxiliaryInput hlegal
  have hxFinite : x ∈ L.finiteTerminalSet :=
    ⟨a, haFinite, p, hchosen, hterminal⟩
  have hxFiniteI : x ∈ I.finiteSource := by
    exact ⟨a, ⟨haGround, haFinite⟩, p, hchosen, hterminal⟩
  have hyMarker : y ∈ L.markerSet := ⟨a, hmarker⟩
  have hyTarget : y ∈ I.targetMarkers := ⟨hyMarker, hyEssential⟩
  have hLambda : I.lambda.graph.Adj (.old x) (.old y) := by
    rw [I.lambda_adj_old_old]
    exact ⟨Or.inr hxFiniteI, Or.inr hyTarget, hxy⟩
  let q : FinitePath I.lambda.graph :=
    oneEdgeFinitePath hLambda (by
      intro h
      exact hne (PopularAuxiliary.Input.LambdaVertex.old.inj h))
  have hstart : q.start ∈ I.lambda.source := by
    change PopularAuxiliary.Input.LambdaVertex.old x ∈ I.lambda.source
    exact (I.mem_lambda_source_old x).2 hxFiniteI
  have hfinish : q.finish ∈ I.lambda.target := by
    change PopularAuxiliary.Input.LambdaVertex.old y ∈ I.lambda.target
    exact (I.mem_lambda_target_old y).2 hyTarget
  intro hdescent
  have hlt := hdescent q hstart hfinish
  have hxStage : L.finiteTerminalStage ⟨x, hxFinite⟩ = a :=
    L.finiteTerminalStage_eq hlegal hchosen hterminal hxFinite
  have hyStage : L.markerStage ⟨y, hyMarker⟩ = a :=
    L.markerStage_eq hlegal.markersInjective hmarker
  change L.markerStage ⟨y, hyMarker⟩ <
    L.finiteTerminalStage ⟨x, hxFinite⟩ at hlt
  rw [hxStage, hyStage] at hlt
  exact (lt_irrefl a hlt)

end KappaLadder
end DWeb
end Erdos599
