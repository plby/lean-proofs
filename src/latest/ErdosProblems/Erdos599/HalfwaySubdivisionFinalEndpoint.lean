/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwaySubdivisionFinalNoRay
import ErdosProblems.Erdos599.HalfwaySourceRootEndpointStart

/-!
# Overlap-aware endpoint projection of the subdivision-safe fair limit
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace Blueprint
namespace LinkageBlueprint

universe u v w

variable {V : Type u}
variable {Gamma : DWeb V} {Y : Set Gamma.DPath} {kappa : Cardinal.{u}}
variable {persistent : Set V}
variable {Stage : Type w} [LinearOrder Stage]
variable {slice closure : Stage → Set V}

namespace IndexedTerminalResolutionState
namespace ReachableResolutionRecursor
namespace ResolutionChain

variable {I : Type v} [LinearOrder I] [Nonempty I]
variable {C : ResolutionChain
  (Gamma := Gamma) (Y := Y) (kappa := kappa)
  (persistent := persistent) (B := Gamma.target)
  (slice := slice) (closure := closure) I}
variable {seed : IndexedTerminalResolutionState
  (Gamma := Gamma) (Y := Y) (kappa := kappa)
  (persistent := persistent) (B := Gamma.target) slice closure}

namespace FairResolutionLimit

/-- Subdivision incidence eliminates final rays; source--stopover overlap is
allowed at the first endpoint, so only non-source stopover carrier points
must be sinks. -/
theorem sourceRoot_endpointPure_of_subdivision_nonSource
    (R : FairResolutionLimit C seed)
    (hGamma : Gamma.IsNormalized)
    (hinc : HasHereditarySubdivisionIncidence Gamma.graph)
    (hkappa : aleph0 ≤ kappa)
    {S : Set V}
    (hterminal :
      (sourceRootBlueprint R.limit.blueprint).terminalSet ⊆ S)
    (hstopSink : ∀ x,
      x ∈ (sourceRootBlueprint R.limit.blueprint).vertexSet → x ∈ S →
        x ∉ Gamma.source →
          ¬ ∃ y, (x, y) ∈
            (sourceRootBlueprint R.limit.blueprint).edgeSet) :
    ∀ p ∈ (sourceRootBlueprint R.limit.blueprint).paths,
      (sourceRootBlueprint R.limit.blueprint).IsPathBetween
        Gamma.source S p :=
  sourceRootBlueprint_endpointPure_of_noRay_of_nonSourceFrontierSink
    R.limit.blueprint hGamma R.real_limit
      (R.no_directedRay_of_subdivision hGamma hinc hkappa)
      hterminal hstopSink

end FairResolutionLimit
end ResolutionChain
end ReachableResolutionRecursor
end IndexedTerminalResolutionState
end LinkageBlueprint
end Blueprint
end Erdos599
