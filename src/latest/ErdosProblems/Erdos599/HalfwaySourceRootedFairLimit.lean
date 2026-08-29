/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwaySourceRootPruningTerminal
import ErdosProblems.Erdos599.HalfwayIndexedRelationScheduler

/-!
# Source-rooted projection of the indexed fair limit

The indexed scheduler's relation limit may retain auxiliary components with
fresh roots.  Pruning those whole components produces a genuine source-rooted
final blueprint while preserving its six blueprint conditions, stability,
edge reality, target-terminal conclusion, and designated initial vertices.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace Blueprint
namespace LinkageBlueprint

universe u v w

variable {V : Type u}
variable {Gamma : DWeb V} {Y : Set Gamma.DPath} {kappa : Cardinal.{u}}

/-- With source-rooted reference paths, condition (2) becomes exact source
coverage after pruning. -/
theorem sourceRootBlueprint_source_cover_eq
    (U : LinkageBlueprint Gamma Y kappa) {T Z persistent : Set V}
    (hU : U.IsLinkageBlueprint T Z persistent)
    (hYsource : Gamma.initialSet Y ⊆ Gamma.source) :
    (sourceRootBlueprint U).initialSet ∪
      Gamma.initialSet ((sourceRootBlueprint U).referenceRemainder T) =
        Gamma.source := by
  apply Set.Subset.antisymm
  · rintro x (hxInitial | hxReference)
    · exact sourceRootBlueprint_initialSet_subset_source U hxInitial
    · apply hYsource
      obtain ⟨p, hp, hpx⟩ := hxReference
      exact ⟨p, hp.1.1, hpx⟩
  · exact (sourceRootBlueprint_isLinkageBlueprint U hU).covers_source

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

/-- The source-root projection remains a linkage blueprint at the actual
final moving slice. -/
theorem sourceRoot_isLinkageBlueprint (R : FairResolutionLimit C seed) :
    (sourceRootBlueprint R.limit.blueprint).IsLinkageBlueprint
      (slice R.limit.stageIndex) (closure R.limit.stageIndex) persistent :=
  sourceRootBlueprint_isLinkageBlueprint R.limit.blueprint
    R.limit.isBlueprint

/-- Stability is inherited by the source-root projection. -/
theorem sourceRoot_stable (R : FairResolutionLimit C seed) :
    (sourceRootBlueprint R.limit.blueprint).Stable
      (slice R.limit.stageIndex) persistent :=
  sourceRootBlueprint_stable R.limit.blueprint R.limit.stable

/-- The source-root projection of the all-real relation limit is edge-real. -/
theorem sourceRoot_isEdgeReal (R : FairResolutionLimit C seed) :
    (sourceRootBlueprint R.limit.blueprint).IsEdgeReal :=
  sourceRootBlueprint_isEdgeReal R.limit.blueprint R.real_limit

/-- Fairness and pruning together leave only original-target real
terminals. -/
theorem sourceRoot_realTerminals_target (R : FairResolutionLimit C seed) :
    (sourceRootBlueprint R.limit.blueprint).realPart.terminals ⊆
      Gamma.target :=
  sourceRootBlueprint_realPart_terminals_subset_target R.limit.blueprint
    R.real_limit R.toTerminalScheduledChain.final_terminals_subset

/-- Every initial vertex of the pruned final blueprint is an original
source. -/
theorem sourceRoot_initial_subset_source (R : FairResolutionLimit C seed) :
    (sourceRootBlueprint R.limit.blueprint).initialSet ⊆ Gamma.source :=
  sourceRootBlueprint_initialSet_subset_source R.limit.blueprint

/-- Exact source coverage follows when the global reference itself is
source-rooted. -/
theorem sourceRoot_source_cover_eq
    (R : FairResolutionLimit C seed)
    (hYsource : Gamma.initialSet Y ⊆ Gamma.source) :
    (sourceRootBlueprint R.limit.blueprint).initialSet ∪
      Gamma.initialSet
        ((sourceRootBlueprint R.limit.blueprint).referenceRemainder
          (slice R.limit.stageIndex)) = Gamma.source :=
  sourceRootBlueprint_source_cover_eq R.limit.blueprint
    R.limit.isBlueprint hYsource

/-- A designated original-source set already present at the fair limit
survives pruning. -/
theorem designated_initial_sourceRoot
    (R : FairResolutionLimit C seed) {A0 : Set V}
    (hA0source : A0 ⊆ Gamma.source)
    (hA0initial : A0 ⊆ R.limit.blueprint.initialSet) :
    A0 ⊆ (sourceRootBlueprint R.limit.blueprint).initialSet :=
  designated_initial_sourceRootBlueprint R.limit.blueprint
    hA0source hA0initial

end FairResolutionLimit
end ResolutionChain
end ReachableResolutionRecursor
end IndexedTerminalResolutionState
end LinkageBlueprint
end Blueprint
end Erdos599
