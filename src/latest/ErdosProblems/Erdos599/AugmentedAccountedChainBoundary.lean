/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.AugmentedAccountedChainExactLimit
import ErdosProblems.Erdos599.ColouredSafeAccountedLimit
import ErdosProblems.Erdos599.MarkedRaySubset

/-!
# Marks and sinks of graph-explicit accounted limits

The forward-ray argument needs only that rays in the actual augmented graph
miss the original target. All marks are parameterized; no identification
with full-reference strong edges is involved.
-/

namespace Erdos599.AugmentedAccountedChain

open Set DirectedPath Alternating ColouredSafeLocalTransactionRealLedger
open ColouredSafeAugmentedRealReach
open Blueprint.ColouredSafeShortcutGraph.RealStageChain
  (forward_index_of_reaches eq_of_reaches_of_noOutgoing)

universe u v

variable {V : Type u} {Gamma D : DWeb V} {I : Type v} [LinearOrder I]

theorem noRealCompletion_on_eventualRay (C : AugmentedAccountedChain Gamma D I)
    (hTarget : ∀ (r : Ray D.graph) (n : Nat), r n ∉ Gamma.target)
    (r : Ray D.graph) (hr : r.edgeSet ⊆ C.eventualEdges) (j : I) (n : Nat) :
    ¬RealReaches Gamma D (C.stage j) (r n) Gamma.target := by
  rintro ⟨b, hb, hreach⟩
  obtain ⟨m, _hnm, hbm⟩ := forward_index_of_reaches C.eventualEdges_biUnique.2
    r (fun n ↦ hr ⟨n, rfl⟩) (C.realReach_eventual hreach) n rfl
  exact hTarget r m (hbm ▸ hb)

theorem eventualRay_edge_mem_stage (C : AugmentedAccountedChain Gamma D I)
    (hTarget : ∀ (r : Ray D.graph) (n : Nat), r n ∉ Gamma.target)
    (r : Ray D.graph) (hr : r.edgeSet ⊆ C.eventualEdges)
    (i : I) (n : Nat) (hx : r n ∈ D.vertexSet (C.stage i)) :
    (r n, r (n + 1)) ∈ familyEdges (C.stage i) := by
  obtain ⟨j0, hj0⟩ := hr ⟨n, rfl⟩
  let j := max i j0
  have hjEdge : (r n, r (n + 1)) ∈ familyEdges (C.stage j) := hj0 j (le_max_right _ _)
  rcases C.account (le_max_left i j0) (r n) hx with hterm | ⟨y, hyi, hyj⟩ | hdone
  · have hno := hterm.2
    rw [TerminalContactSwitch.terminalFrontier_eq_vertexSet_diff_hasOutgoing_anyWarp
      (C.warp j)] at hno
    exact False.elim (hno.2 ⟨r (n + 1), hjEdge⟩)
  · have hy := (IsWarp.familyEdges_biUnique (C.warp j)).2 hyj hjEdge
    exact hy ▸ hyi
  · exact False.elim (C.noRealCompletion_on_eventualRay hTarget r hr j n hdone)

theorem eventualRay_edges_subset_stage (C : AugmentedAccountedChain Gamma D I)
    (hTarget : ∀ (r : Ray D.graph) (n : Nat), r n ∉ Gamma.target)
    (r : Ray D.graph) (hr : r.edgeSet ⊆ C.eventualEdges)
    (i : I) (hfirst : r 0 ∈ D.vertexSet (C.stage i)) :
    r.edgeSet ⊆ familyEdges (C.stage i) := by
  have hvertices : ∀ n, r n ∈ D.vertexSet (C.stage i) := by
    intro n
    induction n with
    | zero => exact hfirst
    | succ n ih =>
        exact (familyEdges_subset_vertexSet_prod (C.stage i)
          (C.eventualRay_edge_mem_stage hTarget r hr i n ih)).2
  rintro _ ⟨n, rfl⟩
  exact C.eventualRay_edge_mem_stage hTarget r hr i n (hvertices n)

theorem eventualWarp_infinitelyManyMarked (C : AugmentedAccountedChain Gamma D I)
    (hTarget : ∀ (r : Ray D.graph) (n : Nat), r n ∉ Gamma.target)
    {marked : V → V → Prop} (hmarked : ∀ i, D.InfinitelyManyMarkedEdges (C.stage i) marked)
    {U : Set D.DPath} (hUE : familyEdges U = C.eventualEdges) :
    D.InfinitelyManyMarkedEdges U marked := by
  intro r hrU
  have hr : r.edgeSet ⊆ C.eventualEdges := by
    intro e he
    rw [← hUE]
    exact Set.mem_iUnion.mpr ⟨Sum.inr r, Set.mem_iUnion.mpr ⟨hrU, he⟩⟩
  obtain ⟨i, hi⟩ := hr ⟨0, rfl⟩
  have hfirst := (familyEdges_subset_vertexSet_prod (C.stage i) (hi i le_rfl)).1
  exact (C.warp i).markedIndices_infinite_of_edgeSet_subset (hmarked i) r
    (C.eventualRay_edges_subset_stage hTarget r hr i hfirst)

theorem eventual_sink_mem_target_or_stage_terminal (C : AugmentedAccountedChain Gamma D I)
    {x : V} (hsink : ¬HasOutgoing C.eventualEdges x)
    (i : I) (hx : x ∈ D.vertexSet (C.stage i)) :
    x ∈ Gamma.target ∨ x ∈ D.terminalFrontier (C.stage i) := by
  classical
  by_cases hxB : x ∈ Gamma.target
  · exact Or.inl hxB
  right
  by_contra hxT
  have hout : HasOutgoing (familyEdges (C.stage i)) x := by
    by_contra hno
    apply hxT
    rw [TerminalContactSwitch.terminalFrontier_eq_vertexSet_diff_hasOutgoing_anyWarp (C.warp i)]
    exact ⟨hx, hno⟩
  obtain ⟨y, hxy⟩ := hout
  apply hsink
  refine ⟨y, i, ?_⟩
  intro j hij
  rcases C.account hij x hx with hterm | ⟨z, hzOld, hzNew⟩ | ⟨b, hb, hxb⟩
  · exact False.elim (hxT hterm.1)
  · have hzy := (IsWarp.familyEdges_biUnique (C.warp i)).2 hzOld hxy
    exact hzy ▸ hzNew
  · have hbx := eq_of_reaches_of_noOutgoing hsink (C.realReach_eventual hxb)
    exact False.elim (hxB (hbx ▸ hb))

#print axioms eventualRay_edges_subset_stage
#print axioms eventualWarp_infinitelyManyMarked
#print axioms eventual_sink_mem_target_or_stage_terminal

end Erdos599.AugmentedAccountedChain
