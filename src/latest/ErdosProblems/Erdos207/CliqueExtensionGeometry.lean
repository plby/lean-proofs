/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.CliquePatternTypicality

/-! # The complete graph carried by a proper clique extension -/

namespace Erdos207

open Finset

noncomputable section

theorem cliquePattern_insert_le
    {V : Type*} [DecidableEq V] (G : SimpleGraph V) (S : Finset V) (v : V)
    (hS : cliquePattern S ≤ G) (hspokes : ∀ w ∈ S, v ≠ w → G.Adj v w) :
    cliquePattern (insert v S) ≤ G := by
  intro a b hab
  have hne : a ≠ b := hab.1
  rcases mem_insert.mp hab.2.1 with rfl | ha
  · have hb : b ∈ S := (mem_insert.mp hab.2.2).resolve_left (Ne.symm hne)
    exact hspokes b hb hne
  · rcases mem_insert.mp hab.2.2 with rfl | hb
    · exact (hspokes a ha hne.symm).symm
    · exact hS ⟨hne, ha, hb⟩

theorem triple_edges_subset_of_clique
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V) (T : TripleOn V)
    (hS : cliquePattern S ≤ G) (hT : T.1 ⊆ S) : tripleEdgeFinset T ⊆ graphEdges G := by
  intro e he
  induction e using Sym2.inductionOn with
  | _ a b =>
      have hm := mk_mem_tripleEdgeFinset_iff.mp he
      exact mem_graphEdges_iff.mpr (hS ⟨hm.2.2, hT hm.1, hT hm.2.1⟩)

theorem cliquePattern_insert_le_of_extension
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (A : TripleSystemOn V) (S : Finset V) (v : V)
    (hS : 2 ≤ S.card) (hSG : cliquePattern S ≤ G)
    (hA : ∀ T ∈ A, tripleEdgeFinset T ⊆ graphEdges G)
    (hv : v ∈ properPatternExtensions A (cliquePattern S) univ) :
    cliquePattern (insert v S) ≤ G := by
  have hv' : v ∈ triangleSetExtensionVertices (triangleVertexFamily A) S := by
    rwa [triangleSetExtensionVertices_eq_properPattern A S hS]
  have hext := (mem_triangleSetExtensionVertices_iff (triangleVertexFamily A) S v).mp hv'
  apply (cliquePattern_le_iff G (insert v S)).mpr
  exact triangleCompleteSet_insert_pairs (graphPairFamily G) (triangleVertexFamily A) S v
    ((cliquePattern_le_iff G S).mp hSG) hS (graphPairFamily_contains_triangle_pairs G A hA) hext.2

theorem clique_extension_triangle_subset
    {V : Type*} [Fintype V] [DecidableEq V]
    (S : Finset V) (v : V) (e : Sym2 V) (T : TripleOn V)
    (hv : v ∉ S) (he : e ∈ graphEdges (cliquePattern S))
    (hvT : v ∈ T.1) (heT : e ∈ tripleEdgeFinset T) : T.1 ⊆ insert v S := by
  have hP : e.toFinset ∈ S.powersetCard 2 := by
    rw [← graphPairFamily_cliquePattern S]
    exact mem_image_of_mem _ he
  have hm := mem_powersetCard.mp hP
  have hoff := (cliquePattern S).not_isDiag_of_mem_edgeSet (mem_graphEdges_iff.mp he)
  have hPT := (mem_tripleEdgeFinset_iff_toFinset_subset_of_not_isDiag e T hoff).mp heT
  have hcard : (insert v e.toFinset).card = 3 := by
    rw [card_insert_of_notMem (fun hvP ↦ hv (hm.1 hvP)), hm.2]
  have heq : insert v e.toFinset = T.1 :=
    eq_of_subset_of_card_le (insert_subset hvT hPT) (by rw [T.2, hcard])
  rw [← heq]
  exact insert_subset_insert v hm.1

end

end Erdos207
