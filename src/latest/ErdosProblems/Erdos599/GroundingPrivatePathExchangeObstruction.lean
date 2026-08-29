/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingSelectedRootPrefixObstruction
import ErdosProblems.Erdos599.GroundingMinimalSeparatingBoundary

/-!
# Minimal-separator obstruction to fixed-relation root exchange

Inclusion-minimality of the stopping frontier supplies a private ambient
source--target path, but it does not change the root of a component of a
fixed switched relation.  This file equips the existing last-backward-owner
example with a web and a globally minimal separating singleton.  All the
formal ingredients of the proposed abstract private-path exchange are then
present: the relation is a subrelation of the web, is locally bi-unique, the
frontier is a sink, and its point has a private path.  Nevertheless the point
is reachable only from the excluded backward owner.
-/

noncomputable section

open Set

namespace Erdos599
namespace GroundingPrivatePathExchangeObstruction

open DirectedPath
open GroundingSelectedRootPrefixObstruction
open GroundingMinimalSeparatingBoundary

/-- Regard the literal three-edge switched relation from the local
obstruction as the ambient web graph. -/
def web : DWeb Vertex where
  graph := { Adj := fun x y => (x, y) ∈ switchedEdges }
  source := {0, 2}
  target := {4}

private theorem adj24 : web.graph.Adj 2 4 := by
  change (2, 4) ∈ switchedEdges
  rw [switchedEdges_eq]
  simp

/-- The terminal component's one-edge private source--target path. -/
def ownerPath : FinitePath web.graph where
  start := 2
  finish := 4
  walk := .cons adj24 .nil
  isPath := by
    change ([2, 4] : List Vertex).Nodup
    simp

@[simp] theorem ownerPath_support : ownerPath.support = {2, 4} := by
  ext x
  simp [ownerPath, FinitePath.support, Walk.support]

@[simp] theorem ownerPath_edgeSet : ownerPath.edgeSet = {(2, 4)} := by
  simp [ownerPath, FinitePath.edgeSet, Walk.edgeSet]

/-- The singleton request exit separates every source--target path simply
because it is the unique target. -/
theorem requestExit_isSeparator : Popular.IsSeparator web ({4} : Set Vertex) := by
  intro p _hpSource hpTarget
  have hpFinish : p.finish = 4 := by simpa [web] using hpTarget
  refine ⟨4, ?_, Set.mem_singleton 4⟩
  rw [← hpFinish]
  exact p.finish_mem_support

/-- The request-exit singleton is globally inclusion-minimal as a separator
from the whole source set. -/
theorem requestExit_isMinimalSeparator :
    CardinalInduction.IsMinimalSeparatorFrom
      web web.source ({4} : Set Vertex) := by
  refine ⟨(isSeparator_iff_source_subset_roof ({4} : Set Vertex)).1
      requestExit_isSeparator, ?_⟩
  intro U hUsep hUT
  have h2Source : (2 : Vertex) ∈ web.source := by simp [web]
  have h4U : (4 : Vertex) ∈ U := by
    obtain ⟨x, hxPath, hxU⟩ := hUsep h2Source ownerPath ⟨rfl, by simp [web, ownerPath]⟩
    have hx : x = 2 ∨ x = 4 := by
      simpa [ownerPath_support] using hxPath
    rcases hx with rfl | rfl
    · have h2T : (2 : Vertex) ∈ ({4} : Set Vertex) := hUT hxU
      simp at h2T
    · exact hxU
  simpa using h4U

/-- Minimality indeed supplies the advertised private path at the terminal
frontier point. -/
theorem exists_privatePath_at_requestExit :
    ∃ a ∈ web.source, ∃ p : FinitePath web.graph,
      web.IsTargetPathFrom a p ∧ p.support ∩ ({4} : Set Vertex) = {4} :=
  exists_privatePath_of_minimalSeparatingSubset
    requestExit_isMinimalSeparator (by simp)

/-- The switched relation is literally the ambient adjacency relation. -/
theorem switchedEdges_subset_adj :
    switchedEdges ⊆ {e | web.graph.Adj e.1 e.2} := by
  intro e he
  exact he

/-- The switched relation is locally bi-unique. -/
theorem switchedEdges_biUnique :
    Relator.BiUnique (fun x y => (x, y) ∈ switchedEdges) := by
  rw [switchedEdges_eq]
  constructor <;> intro x y z hxy hxz <;>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hxy hxz <;>
    aesop

/-- The minimal frontier point has no outgoing switched edge. -/
theorem requestExit_noOutgoing :
    ¬ Alternating.HasOutgoing switchedEdges (4 : Vertex) := by
  rintro ⟨y, hy⟩
  rw [switchedEdges_eq] at hy
  simp at hy

/-- Even in the presence of a private path for a globally minimal separator,
the fixed switched component cannot be rerooted away from its backward
owner. -/
theorem minimal_privatePath_does_not_give_allowed_fixedRelation_root :
    CardinalInduction.IsMinimalSeparatorFrom
        web web.source ({4} : Set Vertex) ∧
      (∃ a ∈ web.source, ∃ p : FinitePath web.graph,
        web.IsTargetPathFrom a p ∧
          p.support ∩ ({4} : Set Vertex) = {4}) ∧
      ¬ ∃ a ∈ web.source \ {2},
        Relation.ReflTransGen
          (fun x y => (x, y) ∈ switchedEdges) a 4 := by
  exact ⟨requestExit_isMinimalSeparator,
    exists_privatePath_at_requestExit,
    requestExit_has_no_root_after_excluding_backwardOwner⟩

end GroundingPrivatePathExchangeObstruction
end Erdos599

#print axioms Erdos599.GroundingPrivatePathExchangeObstruction.requestExit_isMinimalSeparator
#print axioms Erdos599.GroundingPrivatePathExchangeObstruction.minimal_privatePath_does_not_give_allowed_fixedRelation_root
