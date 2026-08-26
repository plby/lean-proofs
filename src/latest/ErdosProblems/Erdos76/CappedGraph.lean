import ErdosProblems.Erdos76.CappedLP
import ErdosProblems.Erdos76.CoverRepair

/-! Capped fractional triangle packings and their dual cover defects. -/

open Finset
open scoped BigOperators Matrix

namespace Erdos76.CappedGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

attribute [local instance] Classical.propDecidable

theorem exists_capped_graph_pair (G : SimpleGraph V) (μ : ℝ) (hμ : 0 < μ) :
    ∃ w : Finset V → ℝ, ∃ z : Sym2 V → ℝ, ∃ r : Finset V → ℝ,
      IsFractionalPacking G w ∧ (∀ t ∈ G.cliqueFinset 3, w t ≤ μ) ∧
      (∀ e ∈ G.edgeFinset, 0 ≤ z e) ∧ (∀ t ∈ G.cliqueFinset 3, 0 ≤ r t) ∧
      (∀ t ∈ G.cliqueFinset 3, 1 ≤ CoverRepair.triangleCost G z t + r t) ∧
      fractionalSize G w = (∑ e ∈ G.edgeFinset, z e) + μ * fractionalSize G r := by
  classical
  obtain ⟨x, y, r, hx, hload, hy, hr, hcover, heq⟩ := CappedLP.exists_capped_primal_dual
    (LPDuality.triangleIncidenceMatrix G)
    (by intro e t; unfold LPDuality.triangleIncidenceMatrix; split_ifs <;> norm_num) μ hμ
  refine ⟨LPDuality.triangleWeight G x, LPDuality.edgeCoverWeight G y,
    LPDuality.triangleWeight G r, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · constructor
    · intro t ht
      have ht' := SimpleGraph.mem_cliqueFinset_iff.mp ht
      simpa [LPDuality.triangleWeight, ht'] using (hx ⟨t, ht'⟩).1
    · intro e he
      let e' : LPDuality.EdgeIndex G := ⟨e, SimpleGraph.mem_edgeFinset.mp he⟩
      rw [← LPDuality.triangleIncidence_mulVec_apply G x e']
      exact hload e'
  · intro t ht
    have ht' := SimpleGraph.mem_cliqueFinset_iff.mp ht
    simpa [LPDuality.triangleWeight, ht'] using (hx ⟨t, ht'⟩).2
  · intro e he
    have he' := SimpleGraph.mem_edgeFinset.mp he
    simpa [LPDuality.edgeCoverWeight, he'] using hy ⟨e, he'⟩
  · intro t ht
    have ht' := SimpleGraph.mem_cliqueFinset_iff.mp ht
    simpa [LPDuality.triangleWeight, ht'] using hr ⟨t, ht'⟩
  · intro t ht
    let t' : LPDuality.TriangleIndex G := ⟨t, SimpleGraph.mem_cliqueFinset_iff.mp ht⟩
    have h := hcover t'
    rw [LPDuality.triangleIncidence_vecMul_apply G y t'] at h
    simpa only [CoverRepair.triangleCost, LPDuality.triangleWeight,
      dif_pos (SimpleGraph.mem_cliqueFinset_iff.mp ht), t'] using h
  · rw [LPDuality.triangleWeight_fractionalSize, LPDuality.edgeCoverWeight_sum,
      LPDuality.triangleWeight_fractionalSize]
    exact heq

lemma fractionalSize_le_card_sq {G : SimpleGraph V} {w : Finset V → ℝ}
    (hw : IsFractionalPacking G w) : fractionalSize G w ≤ (Fintype.card V : ℝ) ^ 2 := by
  have hcover : LPDuality.IsFractionalEdgeCover G (fun _ ↦ 1) := by
    constructor
    · simp
    · intro t ht
      simp only [sum_const, nsmul_eq_mul, mul_one,
        NewProof.triangle_edge_card t (SimpleGraph.mem_cliqueFinset_iff.mp ht)]
      norm_num
  have hsize := LPDuality.fractionalSize_le_edgeCover_sum G w (fun _ ↦ 1) hw hcover
  simp only [sum_const, nsmul_eq_mul, mul_one] at hsize
  have hcard : (G.edgeFinset.card : ℝ) ≤ ((Fintype.card V).choose 2 : ℝ) := by
    exact_mod_cast G.card_edgeFinset_le_card_choose_two
  rw [Nat.cast_choose_two] at hcard
  have hn : (0 : ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
  nlinarith

lemma defect_card_bound {G : SimpleGraph V} {z : Sym2 V → ℝ} {r : Finset V → ℝ}
    (hr : ∀ t ∈ G.cliqueFinset 3, 0 ≤ r t)
    (hcover : ∀ t ∈ G.cliqueFinset 3, 1 ≤ CoverRepair.triangleCost G z t + r t)
    (α : ℝ) :
    α * (CoverRepair.badTriangles G z α).card ≤ fractionalSize G r := by
  have hpoint : ∀ t ∈ CoverRepair.badTriangles G z α, α ≤ r t := by
    intro t ht
    have ht' := mem_filter.mp ht
    have hc := hcover t ht'.1
    linarith [ht'.2]
  calc
    α * (CoverRepair.badTriangles G z α).card =
        ∑ _t ∈ CoverRepair.badTriangles G z α, α := by simp [mul_comm]
    _ ≤ ∑ t ∈ CoverRepair.badTriangles G z α, r t := sum_le_sum hpoint
    _ ≤ fractionalSize G r :=
      sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun t ht _ ↦ hr t ht)

end Erdos76.CappedGraph
