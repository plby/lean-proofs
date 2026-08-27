/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.CliquePatternExtensions

/-! # Pair-pattern proper extensions count incident triangles exactly -/

namespace Erdos207

open Finset

noncomputable section

theorem triangleSetExtensionVertices_pair_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : Finset (Finset V)) (P : Finset V) (hP : P.card = 2)
    (hA : ∀ T ∈ A, T.card = 3) :
    (triangleSetExtensionVertices A P).card = (A.filter (P ⊆ ·)).card := by
  have hpower : P.powersetCard 2 = {P} := by rw [← hP, powersetCard_self]
  have hext (v : V) : v ∈ triangleSetExtensionVertices A P ↔ v ∉ P ∧ insert v P ∈ A := by
    rw [mem_triangleSetExtensionVertices_iff, hpower]
    simp
  apply card_bij (fun v _ ↦ insert v P)
  · intro v hv
    exact mem_filter.mpr ⟨((hext v).mp hv).2, subset_insert _ _⟩
  · intro v hv w hw heq
    have hm : v ∈ insert w P := heq ▸ mem_insert_self v P
    exact (mem_insert.mp hm).resolve_right ((hext v).mp hv).1
  · intro T hT
    have hm := mem_filter.mp hT
    have hc : (T \ P).card = 1 := by rw [card_sdiff_of_subset hm.2, hA T hm.1, hP]
    obtain ⟨v, hv⟩ := card_eq_one.mp hc
    have hvT : v ∈ T \ P := hv.symm ▸ mem_singleton_self v
    have heq : insert v P = T := by
      simpa only [hv, singleton_union] using sdiff_union_of_subset hm.2
    exact ⟨v, (hext v).mpr ⟨(mem_sdiff.mp hvT).2, heq.symm ▸ hm.1⟩, heq⟩

theorem properPatternExtensions_pair_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : TripleSystemOn V) (P : Finset V) (hP : P.card = 2) :
    (properPatternExtensions A (cliquePattern P) univ).card =
      (A.filter (fun T ↦ P ⊆ T.1)).card := by
  rw [← triangleSetExtensionVertices_eq_properPattern A P (by omega),
    triangleSetExtensionVertices_pair_card (triangleVertexFamily A) P hP (triangleVertexFamily_uniform A),
    triangleVertexFamily_incident_card]

theorem properPatternExtensions_edge_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : TripleSystemOn V) (e : Sym2 V) (he : ¬ e.IsDiag) :
    (properPatternExtensions A (cliquePattern e.toFinset) univ).card =
      (A.filter (fun T ↦ e ∈ tripleEdgeFinset T)).card := by
  rw [properPatternExtensions_pair_card A e.toFinset (Sym2.card_toFinset_of_not_isDiag e he),
    ← triangleVertexFamily_incident_card, triangleVertexFamily_edge_card A e he]

end

end Erdos207
