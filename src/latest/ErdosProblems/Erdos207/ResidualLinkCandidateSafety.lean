/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.AmbientLinkRelation
import ErdosProblems.Erdos207.LocalInnerDegreeLoss
import ErdosProblems.Erdos207.SupportedTypicalResidualLinks

/-! # Genuine residual link candidates are pair-safe after the outer/internal cover -/

namespace Erdos207

open Finset
open scoped Classical

noncomputable section

theorem linkMatchingTriple_avoidsGraph_of_three_edges
    {V : Type*} [DecidableEq V] (K : BipartiteLink V) (H : SimpleGraph V)
    (a : ↥K.left) (b : ↥K.right)
    (hleft : ¬ H.Adj K.center (K.leftEmbedding a))
    (hright : ¬ H.Adj K.center (K.rightEmbedding b))
    (hinner : ¬ H.Adj (K.leftEmbedding a) (K.rightEmbedding b)) :
    TriangleAvoidsGraph H (linkMatchingTriple K.center K.leftEmbedding K.rightEmbedding
      K.center_ne_left K.center_ne_right K.left_ne_right a b) := by
  intro u hu v hv huv hH
  rw [mem_linkMatchingTriple_iff] at hu hv
  rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl
  · exact huv rfl
  · exact hleft hH
  · exact hright hH
  · exact hleft hH.symm
  · exact huv rfl
  · exact hinner hH
  · exact hright hH.symm
  · exact hinner hH.symm
  · exact huv rfl

theorem IsResidualBipartition.available_triangle_pair_safe
    {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {P R A : TripleSystemOn V} {center : V} {K : BipartiteLink V} {U : Finset V}
    (hK : IsResidualBipartition G R center K)
    (hleft : K.left ⊆ U) (hright : K.right ⊆ U) (hinner : TrianglesMeetAtMostOne U R)
    (hGleave : G ≤ leaveGraph P) (htri : ConsistsOfTriangles G A)
    (a : ↥K.left) (b : ↥K.right) (havailable : linkAvailableRelation K A a b) :
    TriangleAvoidsGraph (coveredGraph (P ∪ R)) (linkMatchingTriple K.center K.leftEmbedding K.rightEmbedding
      K.center_ne_left K.center_ne_right K.left_ne_right a b) := by
  let T := linkMatchingTriple K.center K.leftEmbedding K.rightEmbedding
    K.center_ne_left K.center_ne_right K.left_ne_right a b
  have hT : T ∈ A := havailable
  have ha : a.1 ∈ residualNeighbors G R center := by
    rw [← hK.2.1]
    exact mem_union_left _ a.2
  have hb : b.1 ∈ residualNeighbors G R center := by
    rw [← hK.2.1]
    exact mem_union_right _ b.2
  have hsR : TriangleAvoidsGraph (coveredGraph R) T :=
    linkMatchingTriple_avoidsGraph_of_three_edges K (coveredGraph R) a b
      (by
        change ¬ (coveredGraph R).Adj K.center a.1
        rw [hK.1]
        exact (mem_residualNeighbors_iff.mp ha).2)
      (by
        change ¬ (coveredGraph R).Adj K.center b.1
        rw [hK.1]
        exact (mem_residualNeighbors_iff.mp hb).2)
      (hinner.not_covered_adj (hleft a.2) (hright b.2))
  intro u hu v hv huv hcovered
  obtain ⟨S, hS, huS, hvS, _h⟩ := coveredGraph_adj.mp hcovered
  rcases mem_union.mp hS with hSP | hSR
  · have hleave := hGleave (htri T hT u hu v hv huv)
    exact (leaveGraph_adj.mp hleave).2 ⟨S, hSP, huS, hvS, huv⟩
  · exact hsR u hu v hv huv (coveredGraph_adj.mpr ⟨S, hSR, huS, hvS, huv⟩)

end

end Erdos207
