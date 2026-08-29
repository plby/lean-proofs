/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeEndpointStageStrongSwitch
import ErdosProblems.Erdos599.ColouredSafeEndpointStageInfiniteSwitch
import ErdosProblems.Erdos599.ColouredSafeStrongTwoPortSplice
import ErdosProblems.Erdos599.ColouredSafeOnePortSplice
import ErdosProblems.Erdos599.ColouredSafeGraphLift

/-!
# Exact graph-independent insertion of strong and infinite switches

Lift the actual real switch family into the ambient supergraph and use the
existing one-port or two-port splice. All switch members are retained in
the exact edge and carrier relations. The old ray traces are retained too.
No initial augmented warp or fair replacement history is presumed to exist.
-/

noncomputable section

namespace Erdos599.ColouredSafeAmbientOccurrence

open Set Cardinal DirectedPath Alternating Blueprint
open ColouredSafeReverseReachability ColouredSafeGraphLift

universe u

variable {V : Type u} {Gamma D : DWeb V} {Y : Set Gamma.DPath} {s t : V}

theorem TouchedStrongSwitch.exists_spliceIn_exact
    {A : Occurrence Y s} (T : TouchedStrongSwitch A t)
    (hAdj : ∀ {x y}, Gamma.graph.Adj x y → D.graph.Adj x y)
    {W : Set D.DPath} (hW : D.IsWarp W) (hedge : (s, t) ∈ familyEdges W)
    (hfresh : Gamma.vertexSet T.paths ∩ D.vertexSet W ⊆ {s, t}) :
    ∃ U : Set D.DPath, D.IsWarp U ∧
      familyEdges U = (familyEdges W \ {(s, t)}) ∪ familyEdges T.paths ∧
      D.vertexSet U = D.vertexSet W ∪ Gamma.vertexSet T.paths ∧
      D.initialSet U = D.initialSet W ∪ (Gamma.initialSet T.paths \ {s}) ∧
      D.terminalFrontier U = D.terminalFrontier W ∪ (Gamma.terminalFrontier T.paths \ {t}) ∧
      T.sourcePath.edgeSet ⊆ familyEdges U ∧
      ∀ r : Ray D.graph, Sum.inr r ∈ U →
        ∃ r0 : Ray D.graph, Sum.inr r0 ∈ W ∧
          ∃ lost : Set (V × V), lost.Finite ∧ r0.edgeSet \ lost ⊆ r.edgeSet := by
  let K : Set D.DPath := liftFamily hAdj T.paths
  let ps : FinitePath D.graph := T.sourcePath.lift hAdj
  let qt : FinitePath D.graph := T.terminalPath.lift hAdj
  have hpsK : (Sum.inl ps : D.DPath) ∈ K := ⟨.inl T.sourcePath, T.source_mem, rfl⟩
  have hqtK : (Sum.inl qt : D.DPath) ∈ K := ⟨.inl T.terminalPath, T.terminal_mem, rfl⟩
  have hdistinct : (Sum.inl ps : D.DPath) ≠ Sum.inl qt := by
    intro he
    have heq := Sum.inl.inj he
    have hv : T.sourcePath.support = T.terminalPath.support := by
      have hsupport := congrArg FinitePath.support heq
      simpa only [ps, qt, FinitePath.support_lift] using hsupport
    exact Set.disjoint_left.mp T.port_supports_disjoint
      T.sourcePath.start_mem_support (hv ▸ T.sourcePath.start_mem_support)
  have hKfresh : D.vertexSet K ∩ D.vertexSet W ⊆ {s, t} := by
    simpa only [K, liftFamily_vertexSet] using hfresh
  obtain ⟨U, hU, hUE, hUV, hUI, hUT, htrace⟩ :=
    ColouredSafeStrongTwoPortSplice.exists_twoPortSplice_exact hW
      (liftFamily_isWarp hAdj T.isWarp) (liftFamily_finiteCharacter hAdj T.finiteCharacter)
      hedge ps qt hpsK hqtK hdistinct T.source_start T.terminal_finish hKfresh
  have hEdges : familyEdges U = (familyEdges W \ {(s, t)}) ∪ familyEdges T.paths := by
    simpa only [K, liftFamily_edges] using hUE
  refine ⟨U, hU, hEdges, ?_, ?_, ?_, ?_, htrace⟩
  · simpa only [K, liftFamily_vertexSet] using hUV
  · simpa only [K, liftFamily_initialSet] using hUI
  · simpa only [K, liftFamily_terminalFrontier] using hUT
  · rw [hEdges]
    intro edge he
    exact Or.inr (Set.mem_iUnion.mpr ⟨.inl T.sourcePath,
      Set.mem_iUnion.mpr ⟨T.source_mem, he⟩⟩)

theorem TouchedInfiniteSwitch.exists_spliceIn_exact
    {A : Occurrence Y s} (T : TouchedInfiniteSwitch A)
    (hAdj : ∀ {x y}, Gamma.graph.Adj x y → D.graph.Adj x y)
    {W : Set D.DPath} (hW : D.IsWarp W) (hsW : s ∈ D.terminalFrontier W)
    (hfresh : Gamma.vertexSet T.paths ∩ D.vertexSet W ⊆ {s}) :
    ∃ U : Set D.DPath, D.IsWarp U ∧
      familyEdges U = familyEdges W ∪ familyEdges T.paths ∧
      D.vertexSet U = D.vertexSet W ∪ Gamma.vertexSet T.paths ∧
      D.initialSet U = D.initialSet W ∪ (Gamma.initialSet T.paths \ {s}) ∧
      D.terminalFrontier U = (D.terminalFrontier W \ {s}) ∪ Gamma.terminalFrontier T.paths ∧
      T.sourcePath.edgeSet ⊆ familyEdges U ∧
      ∀ r : Ray D.graph, Sum.inr r ∈ U →
        ∃ r0 : Ray D.graph, Sum.inr r0 ∈ W ∧
          ∃ lost : Set (V × V), lost.Finite ∧ r0.edgeSet \ lost ⊆ r.edgeSet := by
  let K : Set D.DPath := liftFamily hAdj T.paths
  let ps : FinitePath D.graph := T.sourcePath.lift hAdj
  have hpsK : (Sum.inl ps : D.DPath) ∈ K := ⟨.inl T.sourcePath, T.source_mem, rfl⟩
  have hKfresh : D.vertexSet K ∩ D.vertexSet W ⊆ {s} := by
    simpa only [K, liftFamily_vertexSet] using hfresh
  obtain ⟨U, hU, hUE, hUV, hUI, hUT, hpE, htrace⟩ :=
    ColouredSafeOnePortSplice.exists_onePortSplice_with_path_exact hW
      (liftFamily_isWarp hAdj T.isWarp) (liftFamily_finiteCharacter hAdj T.finiteCharacter)
      hsW ps hpsK T.source_start hKfresh
  refine ⟨U, hU, ?_, ?_, ?_, ?_, ?_, htrace⟩
  · simpa only [K, liftFamily_edges] using hUE
  · simpa only [K, liftFamily_vertexSet] using hUV
  · simpa only [K, liftFamily_initialSet] using hUI
  · simpa only [K, liftFamily_terminalFrontier] using hUT
  · have heq : ps.edgeSet = T.sourcePath.edgeSet :=
      path_edges_lift hAdj (.inl T.sourcePath : Gamma.DPath)
    exact heq ▸ hpE

#print axioms TouchedStrongSwitch.exists_spliceIn_exact
#print axioms TouchedInfiniteSwitch.exists_spliceIn_exact

end Erdos599.ColouredSafeAmbientOccurrence
