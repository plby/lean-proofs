/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwaySourceRootedFairLimit

/-!
# Actual final-slice terminal boundary after source-root pruning

The fair limit has only original-target real terminals, and all of its
vertices are roofed by the final slice.  Testing the roof with the trivial
path at a target vertex shows that every pruned blueprint terminal belongs
to that slice.  No endpoint-purity or sink premise is used here.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace Blueprint
namespace LinkageBlueprint

universe u v w

variable {V : Type u}
variable {Gamma : DWeb V} {Y : Set Gamma.DPath} {kappa : Cardinal.{u}}

private theorem target_mem_of_mem_roof
    {S : Set V} {b : V}
    (hbTarget : b ∈ Gamma.target) (hbRoof : b ∈ Gamma.roof S) :
    b ∈ S := by
  let p : DirectedPath.FinitePath Gamma.graph :=
    DirectedPath.FinitePath.trivial Gamma.graph b
  obtain ⟨x, hxp, hxS⟩ := hbRoof p ⟨rfl, hbTarget⟩
  have hxb : x = b := by
    simpa only [p, DirectedPath.FinitePath.support_trivial,
      Set.mem_singleton_iff] using hxp
  exact hxb ▸ hxS

namespace IndexedTerminalResolutionState
namespace ReachableResolutionRecursor
namespace ResolutionChain

variable {persistent : Set V}
variable {Stage : Type w} [LinearOrder Stage]
variable {slice closure : Stage → Set V}
variable {I : Type v} [LinearOrder I] [Nonempty I]
variable {C : ResolutionChain
  (Gamma := Gamma) (Y := Y) (kappa := kappa)
  (persistent := persistent) (B := Gamma.target)
  (slice := slice) (closure := closure) I}
variable {seed : IndexedTerminalResolutionState
  (Gamma := Gamma) (Y := Y) (kappa := kappa)
  (persistent := persistent) (B := Gamma.target) slice closure}

namespace FairResolutionLimit

/-- Every terminal of the source-rooted final blueprint lies on the actual
final moving slice. -/
theorem sourceRoot_terminalSet_subset_finalSlice
    (R : FairResolutionLimit C seed) :
    (sourceRootBlueprint R.limit.blueprint).terminalSet ⊆
      slice R.limit.stageIndex := by
  intro x hx
  have hxReal :
      x ∈ (sourceRootBlueprint R.limit.blueprint).realPart.terminals :=
    terminalSet_subset_realPart_terminals_general
      (sourceRootBlueprint R.limit.blueprint) hx
  have hxTarget : x ∈ Gamma.target :=
    R.sourceRoot_realTerminals_target hxReal
  have hxVertex : x ∈ (sourceRootBlueprint R.limit.blueprint).vertexSet := by
    obtain ⟨p, hp, hpterm⟩ := hx
    exact ⟨p, hp,
      (imaginaryWeb Gamma Y kappa).terminal_mem_support hpterm⟩
  exact target_mem_of_mem_roof hxTarget
    (R.sourceRoot_isLinkageBlueprint.vertices_roofed hxVertex)

end FairResolutionLimit
end ResolutionChain
end ReachableResolutionRecursor
end IndexedTerminalResolutionState
end LinkageBlueprint
end Blueprint
end Erdos599
