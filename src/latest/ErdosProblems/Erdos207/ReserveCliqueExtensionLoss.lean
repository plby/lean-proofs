/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.CliqueExtensionGeometry
import ErdosProblems.Erdos207.ReserveProtectedPreliminaryGeometry

/-! # Deterministic proper-extension loss under the actual reserve and inner-edge deletion -/

namespace Erdos207

open Finset

noncomputable section

theorem reserveProtected_clique_insert_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U : Finset V) (R : Finset (Sym2 V))
    (A : TripleSystemOn V) (S : Finset V) (v : V)
    (hS : 2 ≤ S.card) (hSG : cliquePattern S ≤ reserveProtectedOuterGraph G U R)
    (hA : ∀ T ∈ A, tripleEdgeFinset T ⊆ graphEdges G)
    (hv : v ∈ properPatternExtensions A (cliquePattern S) univ)
    (hvU : v ∉ U) (hR : ∀ w ∈ S, s(v, w) ∉ R) :
    cliquePattern (insert v S) ≤ reserveProtectedOuterGraph G U R := by
  have hGold := cliquePattern_insert_le_of_extension G A S v hS
    (hSG.trans (reserveProtectedOuterGraph_le G U R)) hA hv
  apply cliquePattern_insert_le _ S v hSG
  intro w hw hvw
  change s(v, w) ∈ (reserveProtectedOuterGraph G U R).edgeSet
  apply mem_graphEdges_iff.mp
  rw [graphEdges_reserveProtectedOuterGraph]
  apply mem_sdiff.mpr
  refine ⟨mem_outerGraphEdges_iff.mpr ⟨?_, ?_⟩, hR w hw⟩
  · exact mem_graphEdges_iff.mpr (hGold
      ⟨hvw, mem_insert_self _ _, mem_insert_of_mem hw⟩)
  · intro hsub
    exact hvU (hsub (by simp [Sym2.toFinset_mk_eq]))

theorem properCliqueExtension_survives_reserve
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U : Finset V) (R : Finset (Sym2 V))
    (A : TripleSystemOn V) (S : Finset V) (v : V)
    (hS : 2 ≤ S.card) (hSG : cliquePattern S ≤ reserveProtectedOuterGraph G U R)
    (hA : ∀ T ∈ A, tripleEdgeFinset T ⊆ graphEdges G)
    (hv : v ∈ properPatternExtensions A (cliquePattern S) univ)
    (hvU : v ∉ U) (hR : ∀ w ∈ S, s(v, w) ∉ R) :
    v ∈ properPatternExtensions (reserveProtectedOuterAvailable G U R A) (cliquePattern S) univ := by
  have hclique := reserveProtected_clique_insert_le G U R A S v hS hSG hA hv hvU hR
  have hm := mem_properPatternExtensions_iff.mp hv
  have hvS : v ∉ S := by simpa only [cliquePattern_support S hS] using hm.2
  apply mem_properPatternExtensions_iff.mpr
  refine ⟨mem_iterationExtensionVertices_iff.mpr ⟨mem_univ _, fun e he ↦ ?_⟩, hm.2⟩
  obtain ⟨T, hTA, hvT, heT⟩ := (mem_iterationExtensionVertices_iff.mp hm.1).2 e he
  have hsub := clique_extension_triangle_subset S v e T hvS he hvT heT
  have hprotected := triple_edges_subset_of_clique (reserveProtectedOuterGraph G U R)
    (insert v S) T hclique hsub
  rw [graphEdges_reserveProtectedOuterGraph] at hprotected
  exact ⟨T, mem_reserveProtectedOuterAvailable_iff.mpr ⟨hTA, hprotected⟩, hvT, heT⟩

def reserveCliqueSpokeVertices
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : TripleSystemOn V) (S : Finset V) (R : Finset (Sym2 V)) (w : V) : Finset V :=
  (properPatternExtensions A (cliquePattern S) univ).filter (fun v ↦ s(v, w) ∈ R)

theorem properCliqueExtension_reserve_loss_subset
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U : Finset V) (R : Finset (Sym2 V))
    (A : TripleSystemOn V) (S : Finset V)
    (hS : 2 ≤ S.card) (hSG : cliquePattern S ≤ reserveProtectedOuterGraph G U R)
    (hA : ∀ T ∈ A, tripleEdgeFinset T ⊆ graphEdges G) :
    properPatternExtensions A (cliquePattern S) univ \
      properPatternExtensions (reserveProtectedOuterAvailable G U R A) (cliquePattern S) univ ⊆
      U ∪ S.biUnion (reserveCliqueSpokeVertices A S R) := by
  classical
  intro v hv
  have hm := mem_sdiff.mp hv
  by_cases hvU : v ∈ U
  · exact mem_union_left _ hvU
  · by_cases hex : ∃ w ∈ S, s(v, w) ∈ R
    · obtain ⟨w, hwS, hwR⟩ := hex
      exact mem_union_right _ (mem_biUnion.mpr ⟨w, hwS, mem_filter.mpr ⟨hm.1, hwR⟩⟩)
    · have hR : ∀ w ∈ S, s(v, w) ∉ R := fun w hw hmem ↦ hex ⟨w, hw, hmem⟩
      exact (hm.2 (properCliqueExtension_survives_reserve G U R A S v hS hSG hA hm.1 hvU hR)).elim

theorem properCliqueExtension_reserve_card_bounds
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U : Finset V) (R : Finset (Sym2 V))
    (A : TripleSystemOn V) (S : Finset V)
    (hS : 2 ≤ S.card) (hSG : cliquePattern S ≤ reserveProtectedOuterGraph G U R)
    (hA : ∀ T ∈ A, tripleEdgeFinset T ⊆ graphEdges G) :
    (properPatternExtensions (reserveProtectedOuterAvailable G U R A) (cliquePattern S) univ).card ≤
      (properPatternExtensions A (cliquePattern S) univ).card ∧
    (properPatternExtensions A (cliquePattern S) univ).card ≤
      (properPatternExtensions (reserveProtectedOuterAvailable G U R A) (cliquePattern S) univ).card +
        U.card + ∑ w ∈ S, (reserveCliqueSpokeVertices A S R w).card := by
  have hmono := properPatternExtensions_mono_available
    (reserveProtectedOuterAvailable_subset G U R A) (cliquePattern S) univ
  refine ⟨card_le_card hmono, ?_⟩
  have hsub := card_le_card (properCliqueExtension_reserve_loss_subset G U R A S hS hSG hA)
  have hbound : (U ∪ S.biUnion (reserveCliqueSpokeVertices A S R)).card ≤
      U.card + ∑ w ∈ S, (reserveCliqueSpokeVertices A S R w).card :=
    (card_union_le _ _).trans (Nat.add_le_add_left card_biUnion_le _)
  have hdiff := card_sdiff_of_subset hmono
  have horder := card_le_card hmono
  omega

end

end Erdos207
