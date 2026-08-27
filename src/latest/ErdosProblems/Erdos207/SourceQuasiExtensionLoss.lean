/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceQuasiObstructionCount
import ErdosProblems.Erdos207.MasterExtensionLoss
import ErdosProblems.Erdos207.PatternTriangleGeometry
import ErdosProblems.Erdos207.PatternExcludedOverlaps

/-! # The precise surviving-graph availability loss is a quasi-moment obstruction -/

namespace Erdos207

open Finset
open scoped Classical NNReal

noncomputable section

theorem extension_vertex_adj_of_mem_support
    {V : Type*} [Fintype V] [DecidableEq V]
    {G Q : SimpleGraph V} {A : TripleSystemOn V} {S : Finset V} {u v : V}
    (htri : ConsistsOfTriangles G A) (hu : u ∈ iterationExtensionVertices A Q S)
    (huB : u ∉ graphSupportFinset Q) (hv : v ∈ graphSupportFinset Q) : G.Adj v u := by
  obtain ⟨w, hvw⟩ := mem_graphSupportFinset_iff.mp hv
  have he : s(v, w) ∈ graphEdges Q := mem_graphEdges_iff.mpr hvw
  obtain ⟨T, hTA, huT, heT⟩ := (mem_iterationExtensionVertices_iff.mp hu).2 _ he
  have hvT := (mk_mem_tripleEdgeFinset_iff.mp heT).1
  exact htri T hTA v hvT u huT (fun heq ↦ huB (heq ▸ hv))

theorem surviving_extension_adj_of_mem_support
    {V : Type*} [Fintype V] [DecidableEq V]
    {G G' Q : SimpleGraph V} {A : TripleSystemOn V} {S : Finset V} {u v : V}
    (htri : ConsistsOfTriangles G A) (hu : u ∈ iterationExtensionVertices A Q S)
    (huB : u ∉ graphSupportFinset Q) (hv : v ∈ graphSupportFinset Q)
    (hnot : u ∉ removedAroundPattern G G' S Q) : G'.Adj v u := by
  have hG := extension_vertex_adj_of_mem_support htri hu huB hv
  have hS := (mem_iterationExtensionVertices_iff.mp hu).1
  by_contra hG'
  apply hnot
  exact mem_biUnion.mpr ⟨v, hv, mem_sdiff.mpr ⟨mem_neighborsIn_iff.mpr ⟨hS, hG⟩,
    fun h ↦ hG' (mem_neighborsIn_iff.mp h).2⟩⟩

theorem surviving_extension_spokes_residual
    {V : Type*} [Fintype V] [DecidableEq V]
    {G G' Γ Q : SimpleGraph V} {A I D : TripleSystemOn V} {S : Finset V} {u : V}
    (htri : ConsistsOfTriangles G A) (hu : u ∈ iterationExtensionVertices A Q S)
    (huB : u ∉ graphSupportFinset Q) (hnot : u ∉ removedAroundPattern G G' S Q)
    (hbase : G' ≤ Γ) (hleave : G' ≤ leaveGraph (I ∪ D)) :
    sourceQuasiSpokes (graphSupportFinset Q) u ⊆ graphEdges Γ ∧
      ∀ a ∈ sourceQuasiSpokes (graphSupportFinset Q) u,
        a ∉ (coveredGraph (I ∪ D)).edgeSet := by
  constructor
  · intro a ha
    obtain ⟨v, hv, rfl⟩ := mem_image.mp ha
    exact mem_graphEdges_iff.mpr (hbase (surviving_extension_adj_of_mem_support htri hu huB hv hnot).symm)
  · intro a ha
    obtain ⟨v, hv, rfl⟩ := mem_image.mp ha
    exact (hleave (surviving_extension_adj_of_mem_support htri hu huB hv hnot).symm).2

theorem patternExtensionTriangle_vertices
    {V : Type*} [Fintype V] [DecidableEq V] (Q : SimpleGraph V)
    (e : graphEdges Q) (u : V) (hu : u ∉ graphSupportFinset Q) :
    (patternExtensionTriangle Q e u hu).1 = insert u e.1.toFinset := by
  rw [← patternExtensionTriangle_erase_vertex Q e u hu,
    insert_erase (patternExtensionTriangle_vertex_mem Q e u hu)]

theorem extensionLoss_subset_support_union_removed_union_quasi
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) {F : ForbiddenFamilyOn V} {G Γ : SimpleGraph V} {U S : Finset V}
    {A I D M : TripleSystemOn V} {Q : SimpleGraph V}
    (hQ : Q ≤ updatedStageGraph G U M) (hS : S ⊆ U)
    (htri : ConsistsOfTriangles G A) (hGleave : G ≤ leaveGraph (I ∪ D))
    (hpacking : IsPackingOn (I ∪ (D ∪ M))) (havoid : AvoidsForbidden (I ∪ (D ∪ M)) F)
    (hbase : G ≤ Γ) (hterminal : S ⊆ W.U (Fin.last ell))
    (hQterminal : graphSupportFinset Q ⊆ W.U (Fin.last ell))
    (hsafe : ∀ T ∈ A, ¬ CompletesForbidden F I T) :
    iterationExtensionVertices A Q S \ iterationExtensionVertices (updatedStageAvailable F U A I D M) Q S ⊆
      graphSupportFinset Q ∪ (removedAroundPattern G (updatedStageGraph G U M) S Q ∪
        (graphEdges Q).biUnion (fun e ↦
          sourceQuasiObstructedVertices W F e S (graphSupportFinset Q) Γ I (D ∪ M))) := by
  intro u hu
  by_cases huB : u ∈ graphSupportFinset Q
  · exact mem_union_left _ huB
  by_cases huRemoved : u ∈ removedAroundPattern G (updatedStageGraph G U M) S Q
  · exact mem_union_right _ (mem_union_left _ huRemoved)
  have hold := (mem_sdiff.mp hu).1
  have hdecomp := extensionLoss_subset_support_union_removed_union_forbidden
    hQ hS htri hGleave hpacking havoid hu
  have hforbid : u ∈ forbiddenAroundPattern F A (I ∪ (D ∪ M)) Q :=
    (mem_union.mp ((mem_union.mp hdecomp).resolve_left huB)).resolve_left huRemoved
  obtain ⟨e, _, he⟩ := mem_biUnion.mp hforbid
  obtain ⟨v, hv, hvu⟩ := mem_image.mp he
  have hh := mem_forbiddenBlockedThirdVertices_iff.mp hv
  let T := thirdVertexTriple (out_fst_ne_snd_of_mem_graphEdges e.2) v
  have heT : e.1 ∈ tripleEdgeFinset T := by
    rw [← e.1.out_eq, mk_mem_tripleEdgeFinset_iff]
    exact ⟨left_mem_thirdVertexTriple _ _, right_mem_thirdVertexTriple _ _, out_fst_ne_snd_of_mem_graphEdges e.2⟩
  have huT : u ∈ T.1 := hvu ▸ third_mem_thirdVertexTriple _ v
  have hcanonical : patternExtensionTriangle Q ⟨e.1, e.2⟩ u huB = T :=
    patternExtensionTriangle_eq_of_mem Q ⟨e.1, e.2⟩ u huB T huT heT
  have hvertices : T.1 = insert u e.1.toFinset := by
    rw [← hcanonical, patternExtensionTriangle_vertices]
  have hlevel : W.level T = Fin.last ell := by
    apply le_antisymm (Fin.le_last _)
    apply W.le_level_of_subset T
    rw [hvertices]
    exact insert_subset (hterminal (mem_iterationExtensionVertices_iff.mp hold).1)
      ((graphEdge_toFinset_subset_support e.2).trans hQterminal)
  have hspokes := surviving_extension_spokes_residual htri hold huB huRemoved
    ((updatedStageGraph_le G U M).trans hbase) (updatedStageGraph_le_leave_enlarged hGleave)
  apply mem_union_right
  apply mem_union_right
  apply mem_biUnion.mpr
  refine ⟨e.1, e.2, mem_filter.mpr ⟨(mem_iterationExtensionVertices_iff.mp hold).1,
    huB, hspokes.1, hspokes.2, T, hvertices, heT, hlevel, hh.2, hsafe T hh.1⟩⟩

theorem card_extensionLoss_le_sum_quasi
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) {F : ForbiddenFamilyOn V} {G Γ : SimpleGraph V} {U S : Finset V}
    {A I D M : TripleSystemOn V} {Q : SimpleGraph V}
    (hQ : Q ≤ updatedStageGraph G U M) (hS : S ⊆ U)
    (htri : ConsistsOfTriangles G A) (hGleave : G ≤ leaveGraph (I ∪ D))
    (hpacking : IsPackingOn (I ∪ (D ∪ M))) (havoid : AvoidsForbidden (I ∪ (D ∪ M)) F)
    (hbase : G ≤ Γ) (hterminal : S ⊆ W.U (Fin.last ell))
    (hQterminal : graphSupportFinset Q ⊆ W.U (Fin.last ell))
    (hsafe : ∀ T ∈ A, ¬ CompletesForbidden F I T) :
    (iterationExtensionVertices A Q S \ iterationExtensionVertices (updatedStageAvailable F U A I D M) Q S).card ≤
      (graphSupportFinset Q).card +
        (∑ v ∈ graphSupportFinset Q, (neighborsIn G S v \ neighborsIn (updatedStageGraph G U M) S v).card) +
        ∑ e ∈ graphEdges Q, (sourceQuasiObstructedVertices W F e S (graphSupportFinset Q) Γ I (D ∪ M)).card := by
  have hs := card_le_card (extensionLoss_subset_support_union_removed_union_quasi W hQ hS htri hGleave
    hpacking havoid hbase hterminal hQterminal hsafe)
  have hr := card_removedAroundPattern_le_sum G (updatedStageGraph G U M) S Q
  have hq := card_biUnion_le (s := graphEdges Q)
    (t := fun e ↦ sourceQuasiObstructedVertices W F e S (graphSupportFinset Q) Γ I (D ∪ M))
  have hu := card_union_le (removedAroundPattern G (updatedStageGraph G U M) S Q)
    ((graphEdges Q).biUnion fun e ↦ sourceQuasiObstructedVertices W F e S (graphSupportFinset Q) Γ I (D ∪ M))
  have hv := card_union_le (graphSupportFinset Q) (removedAroundPattern G (updatedStageGraph G U M) S Q ∪
    (graphEdges Q).biUnion fun e ↦ sourceQuasiObstructedVertices W F e S (graphSupportFinset Q) Γ I (D ∪ M))
  omega

end

end Erdos207
