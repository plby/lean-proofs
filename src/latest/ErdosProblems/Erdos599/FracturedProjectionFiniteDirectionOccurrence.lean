/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.FracturedProjectionFiniteOccurrenceLift
import ErdosProblems.Erdos599.HalfwayFiniteInputDirectionEdgeCoverage

/-!
# Occurrence lifts of finite compressed forward edges

The coordinate-level occurrence lift extends to every forward edge of the
actual finite compressed path by exact direction-edge coverage.
-/

noncomputable section

namespace Erdos599.Blueprint.LinkageBlueprint.FracturedAssignmentPeel

open Set DirectedPath _root_.Erdos599.Alternating
open Alternating.FracturedDuplication PopularAuxiliary.Input

universe u

variable {V : Type u} {Gamma : DWeb V}

/-- Every forward edge of a nonempty finite trace compression is the
projection of a literal edge of a forward link of the selected upstairs
trace. -/
theorem finiteTraceCompression_forwardEdge_occurrenceLift
    (Z : FracturedWarp Gamma)
    (Q : FiniteTrace (web Gamma Z).graph)
    (hnil : (projectedFiniteTraceSteps_runs Z Q).erasedSignedRoute.steps ≠ [])
    {x y : V}
    (hxy : (x, y) ∈ (finiteTraceCompression Z Q).path.directionEdges .forward) :
    ∃ (l : Link (web Gamma Z).graph),
      l ∈ (AltPath.finite Q).links ∧ l.direction = .forward ∧
        ∃ e ∈ l.path.edgeSet, project e.1 = x ∧ project e.2 = y := by
  let S := projectedFiniteTraceInput Z Q hnil
  have hpath := finiteTraceCompression_path_eq_of_steps_ne_nil Z Q hnil
  have hxy' : (x, y) ∈
      (AltPath.finite S.toFiniteRunWalk.toFiniteTrace).directionEdges .forward := by
    rw [← hpath]
    exact hxy
  obtain ⟨k, hkforward, hkedge⟩ :=
    S.mem_directionEdges_exists_rawEdge .forward hxy'
  have hlift := projectedFiniteTraceInput_forwardEdge_occurrenceLift
    Z Q hnil k hkforward
  obtain ⟨l, hl, hldir, e, he, htail, hhead⟩ := hlift
  refine ⟨l, hl, hldir, e, he, ?_, ?_⟩
  · have hraw : S.rawEdge k =
        (S.vertex k, S.vertex (k.1 + 1)) := by
      simp [Alternating.RunCompressor.FiniteInput.rawEdge, hkforward]
    have hpair : (x, y) = (S.vertex k, S.vertex (k.1 + 1)) :=
      hkedge.trans hraw
    exact htail.trans (congrArg Prod.fst hpair).symm
  · have hraw : S.rawEdge k =
        (S.vertex k, S.vertex (k.1 + 1)) := by
      simp [Alternating.RunCompressor.FiniteInput.rawEdge, hkforward]
    have hpair : (x, y) = (S.vertex k, S.vertex (k.1 + 1)) :=
      hkedge.trans hraw
    exact hhead.trans (congrArg Prod.snd hpair).symm

end Erdos599.Blueprint.LinkageBlueprint.FracturedAssignmentPeel

#print axioms Erdos599.Blueprint.LinkageBlueprint.FracturedAssignmentPeel.finiteTraceCompression_forwardEdge_occurrenceLift
