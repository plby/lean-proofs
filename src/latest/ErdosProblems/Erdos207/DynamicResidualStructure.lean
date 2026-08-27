/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.DynamicMasterCrossingCoverStage

/-!
# Residual structure at a dynamic crossing-link state

The internal-edge family forces every still-uncovered neighbor of an outer
center into the next vortex set.  Parity is preserved as well: old selected
families cover no edge of the current graph, so the graph edges covered at a
reached state are exactly those covered by the currently selected available
triangles.
-/

namespace Erdos207

open Finset

noncomputable section

private lemma coveredGraph_mono_residual
    {V : Type*} [DecidableEq V]
    {P Q : TripleSystemOn V} (hPQ : P ⊆ Q) :
    coveredGraph P ≤ coveredGraph Q := by
  intro u v huv
  obtain ⟨T, hTP, huT, hvT, huv⟩ := coveredGraph_adj.mp huv
  exact coveredGraph_adj.mpr ⟨T, hPQ hTP, huT, hvT, huv⟩

/-- If `D` covers every graph edge whose endpoints both lie outside `U`,
then every current residual neighbor of a center outside `U` lies in `U`. -/
lemma residualNeighbors_subset_of_internal_cover
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {U : Finset V} {D P : TripleSystemOn V} {center : V}
    (hDP : D ⊆ P)
    (hcover : ∀ u v : V, G.Adj u v → u ∉ U → v ∉ U →
      (coveredGraph D).Adj u v)
    (hc : center ∉ U) :
    residualNeighbors G P center ⊆ U := by
  intro x hx
  by_contra hxU
  have hxdata := mem_residualNeighbors_iff.mp hx
  exact hxdata.2 (coveredGraph_mono_residual hDP
    (hcover center x hxdata.1 hc hxU))

/-- At a reached dynamic state, coverage of a current graph edge by the
total family is equivalent to coverage by the selected available subfamily.
The old `I ∪ D` family lies in the leave of `G`, and the preliminary stage
family `R` is itself available. -/
lemma coveredGraph_inter_available_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {A I D R P : TripleSystemOn V}
    (hold : G ≤ leaveGraph (I ∪ D))
    (hRselected : R ⊆ A)
    (hPsub : P ⊆ (I ∪ (D ∪ R)) ∪ A)
    {u v : V} (huv : G.Adj u v) :
    (coveredGraph P).Adj u v ↔
      (coveredGraph (P ∩ A)).Adj u v := by
  constructor
  · intro hcovered
    obtain ⟨T, hTP, huT, hvT, huvT⟩ := coveredGraph_adj.mp hcovered
    have hmem := hPsub hTP
    rcases mem_union.mp hmem with hTold | hTA
    · rcases mem_union.mp hTold with hTI | hTDR
      · have hleave := leaveGraph_adj.mp (hold huv)
        exact (hleave.2 ⟨T, mem_union_left D hTI, huT, hvT, huvT⟩).elim
      · rcases mem_union.mp hTDR with hTD | hTR
        · have hleave := leaveGraph_adj.mp (hold huv)
          exact (hleave.2 ⟨T, mem_union_right I hTD, huT, hvT, huvT⟩).elim
        · exact coveredGraph_adj.mpr
            ⟨T, mem_inter.mpr ⟨hTP, hRselected hTR⟩, huT, hvT, huvT⟩
    · exact coveredGraph_adj.mpr
        ⟨T, mem_inter.mpr ⟨hTP, hTA⟩, huT, hvT, huvT⟩
  · intro hcovered
    exact coveredGraph_mono_residual
      (P := P ∩ A) (Q := P) inter_subset_left hcovered

lemma residualNeighbors_inter_available
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {A I D R P : TripleSystemOn V}
    (hold : G ≤ leaveGraph (I ∪ D))
    (hRselected : R ⊆ A)
    (hPsub : P ⊆ (I ∪ (D ∪ R)) ∪ A)
    (center : V) :
    residualNeighbors G P center = residualNeighbors G (P ∩ A) center := by
  ext x
  simp only [mem_residualNeighbors_iff]
  constructor
  · rintro ⟨hcx, hnot⟩
    exact ⟨hcx, fun h ↦ hnot
      ((coveredGraph_inter_available_iff hold hRselected hPsub hcx).mpr h)⟩
  · rintro ⟨hcx, hnot⟩
    exact ⟨hcx, fun h ↦ hnot
      ((coveredGraph_inter_available_iff hold hRselected hPsub hcx).mp h)⟩

/-- Even graph degrees imply even current residual degrees throughout the
dynamic iteration. -/
theorem residualNeighbors_even_of_dynamic_state
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {A I D R P : TripleSystemOn V}
    (heven : ∀ v, Even (G.degree v))
    (htri : ConsistsOfTriangles G A)
    (hold : G ≤ leaveGraph (I ∪ D))
    (hRselected : R ⊆ A)
    (hPsub : P ⊆ (I ∪ (D ∪ R)) ∪ A)
    (hPpacking : IsPackingOn P)
    (center : V) : Even (residualNeighbors G P center).card := by
  have htriPA : ConsistsOfTriangles G (P ∩ A) := by
    intro T hT
    exact htri T (mem_inter.mp hT).2
  have hpackingPA : IsPackingOn (P ∩ A) :=
    hPpacking.mono inter_subset_left
  rw [residualNeighbors_inter_available hold hRselected hPsub center]
  exact residualNeighbors_even heven htriPA hpackingPA center

/-- Every spoke in a residual bipartition is an edge of the current leave. -/
lemma IsResidualBipartition.leave_sides
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {P : TripleSystemOn V} {center : V} {K : BipartiteLink V}
    (hK : IsResidualBipartition G P center K) :
    (∀ a : ↥K.left, (leaveGraph P).Adj K.center a.1) ∧
    (∀ b : ↥K.right, (leaveGraph P).Adj K.center b.1) := by
  constructor
  · intro a
    have hares : a.1 ∈ residualNeighbors G P center := by
      rw [← hK.2.1]
      exact mem_union_left K.right a.2
    have ha := mem_residualNeighbors_iff.mp hares
    rw [hK.1]
    apply leaveGraph_adj.mpr
    exact ⟨ha.1.ne, fun hwitness ↦ ha.2 (coveredGraph_adj.mpr hwitness)⟩
  · intro b
    have hbres : b.1 ∈ residualNeighbors G P center := by
      rw [← hK.2.1]
      exact mem_union_right K.left b.2
    have hb := mem_residualNeighbors_iff.mp hbres
    rw [hK.1]
    apply leaveGraph_adj.mpr
    exact ⟨hb.1.ne, fun hwitness ↦ hb.2 (coveredGraph_adj.mpr hwitness)⟩

end

end Erdos207
