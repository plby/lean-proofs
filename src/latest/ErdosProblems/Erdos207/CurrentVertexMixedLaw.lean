/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.CurrentVertexGraphEncoding
import ErdosProblems.Erdos207.GraphMixedProductBound

/-! # Lossless transport of the current-vertex mixed law to ambient vertices -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem sym2Map_mem_coveredGraph_iff
    {V W : Type*} [DecidableEq V] [DecidableEq W]
    (f : V ↪ W) (M : TripleSystemOn V) (e : Sym2 V) :
    f.sym2Map e ∈ (coveredGraph (mapTripleSystem f M)).edgeSet ↔
      e ∈ (coveredGraph M).edgeSet := by
  classical
  rw [coveredGraph_edgeSet_eq_biUnion, coveredGraph_edgeSet_eq_biUnion]
  simp only [mem_coe, mem_biUnion, mapTripleSystem, mem_map]
  constructor
  · rintro ⟨T, ⟨S, hS, rfl⟩, he⟩
    exact ⟨S, hS, (sym2Map_mem_tripleEdgeFinset_iff f e S).mp he⟩
  · rintro ⟨S, hS, he⟩
    exact ⟨mapTriple f S, ⟨S, hS, rfl⟩,
      (sym2Map_mem_tripleEdgeFinset_iff f e S).mpr he⟩

theorem mapped_graph_mixed_event_iff
    {V W : Type*} [DecidableEq V] [DecidableEq W]
    (f : V ↪ W) (Q M : TripleSystemOn V) (E : Finset (Sym2 V)) :
    (mapTripleSystem f Q ⊆ mapTripleSystem f M ∧
      ∀ e ∈ E.map f.sym2Map, e ∉ (coveredGraph (mapTripleSystem f M)).edgeSet) ↔
    (Q ⊆ M ∧ ∀ e ∈ E, e ∉ (coveredGraph M).edgeSet) := by
  classical
  simp only [mapTripleSystem_subset_iff, forall_mem_map, sym2Map_mem_coveredGraph_iff]

theorem IsGraphMixedProductBound.of_current_vertices
    {Ω V : Type*} [Fintype Ω] [Fintype V] [DecidableEq V]
    {L : FiniteLaw Ω} (U : Finset V) (selected : Ω → TripleSystemOn U)
    (G : SimpleGraph V) (hG : GraphSupportedOn G (U : Set V))
    {survival point C error : ℝ≥0}
    (h : IsGraphMixedProductBound L selected (G.induce (U : Set V))
      survival point C error) :
    IsGraphMixedProductBound L
      (fun x ↦ mapTripleSystem (Function.Embedding.subtype (fun v ↦ v ∈ U)) (selected x))
      G survival point C error := by
  classical
  let f := Function.Embedding.subtype (fun v ↦ v ∈ U)
  intro Q edges hedge
  by_cases hQ : ∀ T ∈ Q, T.1 ⊆ U
  · let Qlocal := restrictTripleSystemTo U Q
    have hQmap : mapTripleSystem f Qlocal = Q := map_restrictTripleSystemTo U Q hQ
    have hQcard : Qlocal.card = Q.card := card_restrictTripleSystemTo U Q hQ
    have hedge' : edges ⊆ (graphEdges (G.induce (U : Set V))).map f.sym2Map := by
      simpa only [f, graphEdges_induce_map G U hG] using hedge
    obtain ⟨Elocal, hElocal, hEmap⟩ := subset_map_iff.mp hedge'
    have hElocal' : Elocal ⊆ graphEdges (V := U) (G.induce (U : Set V)) := by
      intro edge he
      have he' := hElocal he
      revert he'
      refine Sym2.inductionOn edge (fun x y hxy ↦ ?_)
      have hadj : (G.induce (U : Set V)).Adj x y := mem_graphEdges_iff.mp hxy
      exact mem_graphEdges_iff.mpr hadj
    have hevent : (fun x ↦ Q ⊆ mapTripleSystem f (selected x) ∧
        ∀ e ∈ edges, e ∉ (coveredGraph (mapTripleSystem f (selected x))).edgeSet) =
        (fun x ↦ Qlocal ⊆ selected x ∧
          ∀ e ∈ Elocal, e ∉ (coveredGraph (selected x)).edgeSet) := by
      funext x
      apply propext
      rw [← hQmap, hEmap]
      exact mapped_graph_mixed_event_iff f Qlocal (selected x) Elocal
    change L.probability (fun x ↦ Q ⊆ mapTripleSystem f (selected x) ∧
      ∀ e ∈ edges, e ∉ (coveredGraph (mapTripleSystem f (selected x))).edgeSet) ≤ _
    rw [hevent]
    have hbound := h Qlocal Elocal hElocal'
    simpa only [hQcard, hEmap, card_map] using hbound
  · have hz : L.probability (fun x ↦ Q ⊆ mapTripleSystem f (selected x) ∧
        ∀ e ∈ edges, e ∉ (coveredGraph (mapTripleSystem f (selected x))).edgeSet) ≤
        L.probability (fun _ ↦ False) := by
      apply L.probability_mono
      intro x hx
      apply hQ
      intro T hT
      obtain ⟨S, _, rfl⟩ := mem_map.mp (hx.1 hT)
      exact mapTriple_subtype_supported U S
    rw [L.probability_false] at hz
    exact hz.trans zero_le

end

end Erdos207
