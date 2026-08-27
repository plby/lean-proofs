/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.CliquePatternEncoding

/-! # Proper graph-pattern extensions are exactly the regularizer's extensions -/

namespace Erdos207

open Finset

noncomputable section

theorem triangleSetExtensionVertices_eq_properPattern
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : TripleSystemOn V) (S : Finset V) (hS : 2 ≤ S.card) :
    triangleSetExtensionVertices (triangleVertexFamily A) S =
      properPatternExtensions A (cliquePattern S) univ := by
  ext v
  rw [mem_triangleSetExtensionVertices_iff, mem_properPatternExtensions_iff,
    cliquePattern_support S hS]
  constructor
  · rintro ⟨hvS, hext⟩
    refine ⟨mem_iterationExtensionVertices_iff.mpr ⟨mem_univ _, fun e he ↦ ?_⟩, hvS⟩
    have hP : e.toFinset ∈ S.powersetCard 2 := by
      rw [← graphPairFamily_cliquePattern S]
      exact mem_image_of_mem _ he
    obtain ⟨T, hTA, heq⟩ := mem_image.mp (hext e.toFinset hP)
    have hoff := (cliquePattern S).not_isDiag_of_mem_edgeSet (mem_graphEdges_iff.mp he)
    refine ⟨T, hTA, ?_, ?_⟩
    · rw [heq]
      exact mem_insert_self _ _
    · apply (mem_tripleEdgeFinset_iff_toFinset_subset_of_not_isDiag e T hoff).mpr
      rw [heq]
      exact subset_insert _ _
  · rintro ⟨hpattern, hvS⟩
    refine ⟨hvS, fun P hP ↦ ?_⟩
    have hm := mem_powersetCard.mp hP
    obtain ⟨a, b, hab, hPeq⟩ := card_eq_two.mp hm.2
    have hbase : s(a, b) ∈ graphEdges (cliquePattern S) := by
      apply (mem_graphPairFamily_toFinset_iff (cliquePattern S) s(a, b)).mp
      rw [graphPairFamily_cliquePattern S, Sym2.toFinset_mk_eq, ← hPeq]
      exact hP
    obtain ⟨T, hTA, hvT, heT⟩ := (mem_iterationExtensionVertices_iff.mp hpattern).2 _ hbase
    have hPT : P ⊆ T.1 := by
      have hoff : ¬ (s(a, b) : Sym2 V).IsDiag := by simpa only [Sym2.mk_isDiag_iff] using hab
      have hsub := (mem_tripleEdgeFinset_iff_toFinset_subset_of_not_isDiag s(a, b) T hoff).mp heT
      simpa only [Sym2.toFinset_mk_eq, ← hPeq] using hsub
    have hcard : (insert v P).card = 3 := by
      rw [card_insert_of_notMem (fun hvP ↦ hvS (hm.1 hvP)), hm.2]
    have heq : insert v P = T.1 :=
      eq_of_subset_of_card_le (insert_subset hvT hPT) (by rw [T.2, hcard])
    exact mem_image.mpr ⟨T, hTA, heq.symm⟩

end

end Erdos207
