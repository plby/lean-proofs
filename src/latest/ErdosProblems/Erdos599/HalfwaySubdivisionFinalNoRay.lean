/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ArcSubdivisionNoStrong
import ErdosProblems.Erdos599.IndexedRelationLimitGeometry
import ErdosProblems.Erdos599.HalfwaySourceRootedFairLimit
import ErdosProblems.Erdos599.HalfwaySourceRootEndpoint

/-!
# Ray-free final limits under hereditary subdivision incidence

Every ray of the indexed real relation limit contains a strong imaginary
edge.  Hereditary subdivision incidence forbids every original edge from
being strong.  Since the final relation contains only original edges, these
two facts exclude forward rays and discharge the stopping premise of the
source-root endpoint theorem.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace Blueprint
namespace LinkageBlueprint

open Alternating

universe u v w

variable {V : Type u}
variable {Gamma : DWeb V} {Y : Set Gamma.DPath} {kappa : Cardinal.{u}}

namespace IndexedRealExtensionChain

variable {I : Type v} [LinearOrder I] [Nonempty I]
variable {B : Set V}

/-- The final real relation has no forward ray when the ambient original
graph has hereditary subdivision incidence. -/
theorem realRelationBlueprint_no_directedRay_of_subdivision
    (C : IndexedRealExtensionChain I Gamma Y kappa B)
    (hstrong : ∀ i, (C.stage i).InfinitelyManyStrongEdges)
    (hGamma : Gamma.IsNormalized) (hB : B ⊆ Gamma.target)
    (hinc : HasHereditarySubdivisionIncidence Gamma.graph)
    (hkappa : aleph0 ≤ kappa) :
    ¬ ContainsDirectedRay C.realRelationBlueprint.edgeSet := by
  rintro ⟨s, hs⟩
  let r : DirectedPath.Ray (imaginaryGraph Gamma Y kappa) := {
    toFun := s.vertex
    adj_succ := fun n ↦ original_adj_imaginaryGraph (by
      have hedge : (s.vertex n, s.vertex (n + 1)) ∈ C.realEdgeLimit := by
        rw [← C.realRelationBlueprint_edgeSet]
        exact hs ⟨n, rfl⟩
      obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hedge
      exact hi.2)
    injective := s.injective }
  have hray : r.edgeSet ⊆ C.realEdgeLimit := by
    rintro e ⟨n, rfl⟩
    rw [← C.realRelationBlueprint_edgeSet]
    exact hs ⟨n, rfl⟩
  obtain ⟨n, hn⟩ :=
    (C.realEdgeLimit_every_ray_strong hstrong hGamma hB r hray).nonempty
  have hedge : Gamma.graph.Adj (r n) (r (n + 1)) := by
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (hray ⟨n, rfl⟩)
    exact hi.2
  exact hinc.no_strongImaginaryEdge hkappa hedge hn

end IndexedRealExtensionChain

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

/-- Scheduler-facing no-ray theorem for the actual final blueprint. -/
theorem no_directedRay_of_subdivision
    (R : FairResolutionLimit C seed)
    (hGamma : Gamma.IsNormalized)
    (hinc : HasHereditarySubdivisionIncidence Gamma.graph)
    (hkappa : aleph0 ≤ kappa) :
    ¬ ContainsDirectedRay R.limit.blueprint.edgeSet := by
  rw [R.relation_limit]
  exact C.toIndexedRealExtensionChain
    |>.realRelationBlueprint_no_directedRay_of_subdivision
      (fun i ↦ (C.stage i).isBlueprint.infinitely_many_strong)
      hGamma Set.Subset.rfl hinc hkappa

/-- Under subdivision incidence, the remaining stopover-sink boundary
condition suffices for endpoint purity of the pruned fair limit. -/
theorem sourceRoot_endpointPure_of_subdivision
    (R : FairResolutionLimit C seed)
    (hGamma : Gamma.IsNormalized)
    (hinc : HasHereditarySubdivisionIncidence Gamma.graph)
    (hkappa : aleph0 ≤ kappa)
    {S : Set V}
    (hterminal :
      (sourceRootBlueprint R.limit.blueprint).terminalSet ⊆ S)
    (hstopSink : ∀ x,
      x ∈ (sourceRootBlueprint R.limit.blueprint).vertexSet → x ∈ S →
        ¬ ∃ y, (x, y) ∈
          (sourceRootBlueprint R.limit.blueprint).edgeSet) :
    ∀ p ∈ (sourceRootBlueprint R.limit.blueprint).paths,
      (sourceRootBlueprint R.limit.blueprint).IsPathBetween
        Gamma.source S p :=
  sourceRootBlueprint_endpointPure_of_noRay_of_frontierSink
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
