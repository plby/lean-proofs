/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.FracturedProjectionFiniteProvenance

/-!
# Occurrence lifts of finite compressor coordinates

Every raw coordinate edge of the concrete finite compressor is one retained
step of the projected upstairs trace.  In the forward case this file exposes
the literal upstairs edge and its source link, rather than merely its
downstairs ambient edge.  This is the occurrence datum needed to distinguish
the incoming and outgoing copies of a projected cut contact.
-/

noncomputable section

namespace Erdos599.Blueprint.LinkageBlueprint.FracturedAssignmentPeel

open Set DirectedPath _root_.Erdos599.Alternating
open Alternating.FracturedDuplication PopularAuxiliary.Input

universe u

variable {V : Type u} {Gamma : DWeb V}

/-- A forward raw edge of the exact finite compressor input lifts to a
forward link edge of the selected occurrence-level trace, with both endpoint
projections definitionally matching the compressor coordinates. -/
theorem projectedFiniteTraceInput_forwardEdge_occurrenceLift
    (Z : FracturedWarp Gamma)
    (Q : FiniteTrace (web Gamma Z).graph)
    (hnil : (projectedFiniteTraceSteps_runs Z Q).erasedSignedRoute.steps ≠ [])
    (n : Fin (projectedFiniteTraceInput Z Q hnil).lastEdge)
    (hforward : (projectedFiniteTraceInput Z Q hnil).colour n = .forward) :
    ∃ (l : Link (web Gamma Z).graph),
      l ∈ (AltPath.finite Q).links ∧ l.direction = .forward ∧
        ∃ e ∈ l.path.edgeSet,
          project e.1 = (projectedFiniteTraceInput Z Q hnil).vertex n ∧
          project e.2 =
            (projectedFiniteTraceInput Z Q hnil).vertex (n.1 + 1) := by
  let E := (projectedFiniteTraceSteps_runs Z Q).erasedSignedRoute
  let S := projectedFiniteTraceInput Z Q hnil
  let k : Fin E.steps.length := ⟨n.1, by exact n.2⟩
  have hkdir : (E.steps.get k).direction = .forward := by
    change (E.steps.get ⟨n.1, n.2⟩).direction = .forward at hforward
    exact hforward
  have hkraw := erasedRawEmbedding_step_eq Z Q k
  have hkmem : (projectedFiniteTraceSteps Z Q).get
      (erasedRawEmbedding Z Q k) ∈ projectedFiniteTraceSteps Z Q :=
    List.get_mem _ _
  obtain ⟨_hvalid, _hne, l, hl, hstepDir, e, he, hedge⟩ :=
    projectedFiniteTraceSteps_mem Z Q hkmem
  refine ⟨l, hl, ?_, e, he, ?_, ?_⟩
  · have hrawdir :
        ((projectedFiniteTraceSteps Z Q).get
          (erasedRawEmbedding Z Q k)).direction = .forward := by
      rw [← hkraw]
      exact hkdir
    exact hstepDir.symm.trans hrawdir
  · have hroute := E.step_edge_eq_routeVertices_forward k hkdir
    have hfirst : project e.1 = E.routeVertex k := by
      have hpair : (E.steps.get k).edge = (project e.1, project e.2) := by
        rw [hkraw]
        exact hedge
      exact congrArg Prod.fst hpair.symm |>.trans (congrArg Prod.fst hroute)
    change project e.1 = E.routeVertex n.1
    exact hfirst
  · have hroute := E.step_edge_eq_routeVertices_forward k hkdir
    have hsecond : project e.2 = E.routeVertex (k.1 + 1) := by
      have hpair : (E.steps.get k).edge = (project e.1, project e.2) := by
        rw [hkraw]
        exact hedge
      exact congrArg Prod.snd hpair.symm |>.trans (congrArg Prod.snd hroute)
    change project e.2 = E.routeVertex (n.1 + 1)
    exact hsecond

end Erdos599.Blueprint.LinkageBlueprint.FracturedAssignmentPeel

#print axioms Erdos599.Blueprint.LinkageBlueprint.FracturedAssignmentPeel.projectedFiniteTraceInput_forwardEdge_occurrenceLift
