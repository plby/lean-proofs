/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwaySourceRootPruning
import ErdosProblems.Erdos599.Blueprint930

/-!
# Final real-terminal facts for source-root pruning

For an edge-real blueprint, a real-part sink is a genuine finite path
terminal.  Consequently pruning whole non-source-rooted components preserves
the final target-terminal conclusion of the fair scheduler.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace Blueprint
namespace LinkageBlueprint

universe u

variable {V : Type u}
variable {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}

/-- Edge reality is inherited by source-root pruning. -/
theorem sourceRootBlueprint_isEdgeReal
    (U : LinkageBlueprint Gamma Y kappa) (hreal : U.IsEdgeReal) :
    (sourceRootBlueprint U).IsEdgeReal :=
  (sourceRootBlueprint_edgeSet_subset U).trans hreal

/-- When every family edge is real, every real-part terminal is the finite
terminal of its blueprint path. -/
theorem realPart_terminals_subset_terminalSet_of_isEdgeReal
    (U : LinkageBlueprint Gamma Y kappa) (hreal : U.IsEdgeReal) :
    U.realPart.terminals ⊆ U.terminalSet := by
  intro x hx
  by_contra hxTerminal
  obtain ⟨y, hxy⟩ :=
    U.exists_outgoing_of_mem_vertexSet_of_not_mem_terminalSet
      (by simpa only [realPart_vertices] using hx.1) hxTerminal
  exact hx.2 ⟨y, hxy, hreal hxy⟩

/-- A genuine blueprint terminal is a real-part terminal when all of the
blueprint's edges are real. -/
theorem terminalSet_subset_realPart_terminals_general
    (U : LinkageBlueprint Gamma Y kappa) :
    U.terminalSet ⊆ U.realPart.terminals := by
  intro x hx
  have hxFamily := mem_familyGraph_terminals_of_mem_terminalSet hx
  change x ∈ U.vertexSet ∧ x ∉ U.familyGraph.tails at hxFamily
  refine ⟨?_, ?_⟩
  · simpa only [realPart_vertices] using hxFamily.1
  · rintro ⟨y, hxy⟩
    exact hxFamily.2 ⟨y, hxy.1⟩

/-- Under edge reality the two terminal notions coincide. -/
theorem realPart_terminals_eq_terminalSet_of_isEdgeReal
    (U : LinkageBlueprint Gamma Y kappa) (hreal : U.IsEdgeReal) :
    U.realPart.terminals = U.terminalSet :=
  Set.Subset.antisymm
    (realPart_terminals_subset_terminalSet_of_isEdgeReal U hreal)
    (terminalSet_subset_realPart_terminals_general U)

/-- Pruning non-source-rooted components preserves the scheduler's final
claim that every real terminal belongs to the original target. -/
theorem sourceRootBlueprint_realPart_terminals_subset_target
    (U : LinkageBlueprint Gamma Y kappa) (hreal : U.IsEdgeReal)
    (htarget : U.realPart.terminals ⊆ Gamma.target) :
    (sourceRootBlueprint U).realPart.terminals ⊆ Gamma.target := by
  intro x hx
  have hxPrunedTerminal : x ∈ (sourceRootBlueprint U).terminalSet :=
    realPart_terminals_subset_terminalSet_of_isEdgeReal
      (sourceRootBlueprint U) (sourceRootBlueprint_isEdgeReal U hreal) hx
  have hxTerminal : x ∈ U.terminalSet :=
    sourceRootBlueprint_terminalSet_subset U hxPrunedTerminal
  exact htarget
    (terminalSet_subset_realPart_terminals_general U hxTerminal)

end LinkageBlueprint
end Blueprint
end Erdos599
