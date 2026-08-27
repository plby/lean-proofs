/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.ResidualGraphDistribution

/-! # Later selected edges cannot be charged again as independently surviving initial edges -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem IsGraphStronglyWellDistributed.later_triangle_overlap_bound
    {Ω V : Type*} [Fintype Ω] [Fintype V] [DecidableEq V] {ell : ℕ}
    {L : FiniteLaw Ω} {W : Vortex V ell} {k : Fin (ell + 1)} {G : SimpleGraph V}
    {initial later : Ω → TripleSystemOn V} {p C b : ℝ≥0}
    (h : IsGraphStronglyWellDistributed L W k G initial later p C b)
    (hsupport : L.SupportedOn fun ω ↦ IsPackingOn (initial ω ∪ later ω) ∧ Disjoint (initial ω) (later ω))
    (T : TripleOn V) (hT : tripleEdgeFinset T ⊆ graphEdges G) :
    L.probability (fun ω ↦ T ∈ later ω) ≤
      C ^ 4 * (p ^ 4 / ((W.U (W.truncatedLevel k T)).card : ℝ≥0) + b) := by
  classical
  have hsub : L.probability (fun ω ↦ T ∈ later ω) ≤
      L.probability (StrongDistributionEvent initial later ∅ {T} (tripleEdgeFinset T)) := by
    apply L.probability_mono_of_supported hsupport
    intro ω hω hmem
    refine ⟨empty_subset _, singleton_subset_iff.mpr hmem, ?_⟩
    intro e he hcovered
    rw [coveredGraph_edgeSet_eq_biUnion] at hcovered
    exact disjoint_left.mp (hω.1.disjoint_family_edges hω.2) hcovered
      (mem_biUnion.mpr ⟨T, hmem, he⟩)
  apply hsub.trans
  have hraw := h ∅ {T} (tripleEdgeFinset T) (by simp) hT
  simpa [card_tripleEdgeFinset, laterTriangleScale, pow_succ, div_eq_mul_inv, mul_assoc] using hraw

theorem not_graphStrong_of_later_triangle_overlap
    {Ω V : Type*} [Fintype Ω] [Fintype V] [DecidableEq V] {ell : ℕ}
    (L : FiniteLaw Ω) (W : Vortex V ell) (k : Fin (ell + 1)) (G : SimpleGraph V)
    (initial later : Ω → TripleSystemOn V) (p C b : ℝ≥0)
    (hsupport : L.SupportedOn fun ω ↦ IsPackingOn (initial ω ∪ later ω) ∧ Disjoint (initial ω) (later ω))
    (T : TripleOn V) (hT : tripleEdgeFinset T ⊆ graphEdges G)
    (hsmall : C ^ 4 * (p ^ 4 / ((W.U (W.truncatedLevel k T)).card : ℝ≥0) + b) <
      L.probability (fun ω ↦ T ∈ later ω)) :
    ¬ IsGraphStronglyWellDistributed L W k G initial later p C b := by
  intro h
  exact (not_lt_of_ge (h.later_triangle_overlap_bound hsupport T hT)) hsmall

/-- A concrete finite separation: three vertices, eight equally likely
outcomes, and a single triangle assigned to one of the two selected families. -/
theorem exists_residualGraphStrong_not_graphStrong :
    ∃ (L : FiniteLaw (Fin 8)) (W : Vortex (Fin 3) 0) (G : SimpleGraph (Fin 3))
      (initial later : Fin 8 → TripleSystemOn (Fin 3)),
      L.SupportedOn (fun ω ↦ IsPackingOn (initial ω ∪ later ω) ∧ Disjoint (initial ω) (later ω)) ∧
      IsResidualGraphStronglyWellDistributed L W 0 G initial later (1 / 8) 4 0 ∧
      ¬ IsGraphStronglyWellDistributed L W 0 G initial later (1 / 8) 4 0 := by
  classical
  let T : TripleOn (Fin 3) := ⟨univ, by decide⟩
  let L : FiniteLaw (Fin 8) := FiniteLaw.uniform
  let W : Vortex (Fin 3) 0 := ⟨fun _ ↦ univ, rfl, fun _ _ _ ↦ Subset.rfl⟩
  let G := coveredGraph ({T} : TripleSystemOn (Fin 3))
  let initial := fun ω : Fin 8 ↦ if ω = 0 then ∅ else ({T} : TripleSystemOn (Fin 3))
  let later := fun ω : Fin 8 ↦ if ω = 0 then ({T} : TripleSystemOn (Fin 3)) else ∅
  have hunion : ∀ ω, initial ω ∪ later ω = {T} := by
    intro ω
    by_cases hω : ω = 0 <;> simp [initial, later, hω]
  have hsupport : L.SupportedOn (fun ω ↦ IsPackingOn (initial ω ∪ later ω) ∧ Disjoint (initial ω) (later ω)) := by
    intro ω _
    refine ⟨(hunion ω).symm ▸ isPackingOn_singleton T, ?_⟩
    by_cases hω : ω = 0 <;> simp [initial, later, hω]
  have hprob : L.probability (fun ω ↦ T ∈ later ω) = 1 / 8 := by
    have h := FiniteLaw.uniform_probability_unique (fun ω : Fin 8 ↦ T ∈ later ω) 0
      (fun ω ↦ by by_cases hω : ω = 0 <;> simp [later, hω])
    change (FiniteLaw.uniform : FiniteLaw (Fin 8)).probability (fun ω ↦ T ∈ later ω) = 1 / 8
    rw [h]
    norm_num
  have hTgraph : tripleEdgeFinset T ⊆ graphEdges G := by
    intro e he
    apply mem_graphEdges_iff.mpr
    rw [coveredGraph_edgeSet_eq_biUnion]
    exact mem_biUnion.mpr ⟨T, mem_singleton_self T, he⟩
  have hunique : ∀ U : TripleOn (Fin 3), U = T := by
    intro U
    apply Subtype.ext
    exact eq_univ_of_card U.1 (by simpa only [Fintype.card_fin] using U.2)
  have hfamilies : ∀ Q : TripleSystemOn (Fin 3), Q = ∅ ∨ Q = {T} := by
    intro Q
    by_cases hQ : Q = ∅
    · exact Or.inl hQ
    · right
      obtain ⟨U, hU⟩ := nonempty_iff_ne_empty.mpr hQ
      exact eq_singleton_iff_unique_mem.mpr ⟨hunique U ▸ hU, fun U _ ↦ hunique U⟩
  refine ⟨L, W, G, initial, later, hsupport, ?_, ?_⟩
  · intro Ifix Dfix Efix hdis hE
    by_cases hEempty : Efix = ∅
    · subst Efix
      rcases hfamilies Ifix with rfl | rfl <;> rcases hfamilies Dfix with rfl | rfl
      · exact (L.probability_le_one _).trans (by simp)
      · have hevent : ResidualDistributionEvent initial later ∅ {T} ∅ = (fun ω ↦ T ∈ later ω) := by
          funext ω
          simp [ResidualDistributionEvent]
        rw [hevent, hprob]
        rw [← NNReal.coe_le_coe]
        norm_num [laterTriangleScale, W]
      · exact (L.probability_le_one _).trans (by rw [← NNReal.coe_le_coe]; norm_num [laterTriangleScale])
      · simp at hdis
    · have hzero : L.probability (ResidualDistributionEvent initial later Ifix Dfix Efix) ≤
          L.probability (fun _ ↦ False) := by
        apply L.probability_mono
        intro ω hω
        obtain ⟨e, he⟩ := nonempty_iff_ne_empty.mpr hEempty
        apply hω.2.2 e he
        rw [hunion ω]
        exact mem_graphEdges_iff.mp (hE he)
      rw [L.probability_false] at hzero
      exact hzero.trans zero_le
  · apply not_graphStrong_of_later_triangle_overlap L W 0 G initial later (1 / 8) 4 0 hsupport T hTgraph
    rw [hprob]
    norm_num [W]

end

end Erdos207
