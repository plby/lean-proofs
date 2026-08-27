/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.InitialProductResidualIncidence
import ErdosProblems.Erdos207.TrackedInitialSparsification

/-!
# Residual incidence from the unamplified tracked-edge product

The initial law has two roles.  Its coarse mixed product controls later
rooted configurations, while its sharper edge-only product controls the
maximum degree of the residual outer graph.  This file performs the finite
witness union for that sharp edge-only estimate and conditions the coarse
strong law on the resulting positive-probability event.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- Every edge of a graph disjoint from the absorber and not wholly inside
the root set is one of the pairs tracked by the initial process. -/
lemma outsideTrackablePart_eq_self_of_subset_outerGraphEdges
    {V : Type*} [Fintype V] [DecidableEq V]
    {H G : SimpleGraph V} {U : Finset V} {E : Finset (Sym2 V)}
    (hHG : Disjoint H G) (hE : E ⊆ outerGraphEdges G U) :
    outsideTrackablePart H U E = E := by
  classical
  apply Subset.antisymm (outsideTrackablePart_subset H U E)
  intro e heE
  have heOuter := mem_outerGraphEdges_iff.mp (hE heE)
  have heGset : e ∈ G.edgeSet := mem_graphEdges_iff.mp heOuter.1
  have hoff : ¬ e.IsDiag := G.not_isDiag_of_mem_edgeSet heGset
  have hnotH : e ∉ graphEdges H := by
    intro heH
    exact (Set.disjoint_left.mp (SimpleGraph.disjoint_edgeSet.mpr hHG)
      (mem_graphEdges_iff.mp heH) heGset).elim
  change e ∈ E.filter fun f ↦
    ¬ f.IsDiag ∧ f ∉ graphEdges H ∧ ¬ f.toFinset ⊆ U
  exact mem_filter.mpr ⟨heE, hoff, hnotH, heOuter.2⟩

def trackedResidualOuterIncidenceTail
    (V : Type*) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U : Finset V)
    (survival b : ℝ≥0) (r : ℕ) : ℝ≥0 :=
  ∑ v : V, ((outerIncidentEdges G U v).powersetCard r).card *
    (survival ^ r + b)

theorem probability_exists_large_residualOuter_incidence_le_of_tracked
    {Omega V : Type*} [Fintype Omega] [Fintype V]
    [DecidableEq V]
    {L : FiniteLaw Omega} {selected : Omega → TripleSystemOn V}
    (G : SimpleGraph V) (U : Finset V) (survival b : ℝ≥0) (r : ℕ)
    (htracked : ∀ E : Finset (Sym2 V), E.card = r →
      E ⊆ outerGraphEdges G U →
      L.probability (fun omega ↦
        ∀ e ∈ E, e ∉ (coveredGraph (selected omega)).edgeSet) ≤
          survival ^ E.card + b) :
    L.probability (fun omega ↦ ∃ v : V,
        r ≤ (outerIncidentEdges G U v ∩
          preliminaryResidualOuterEdges G U (selected omega)).card) ≤
      trackedResidualOuterIncidenceTail V G U survival b r := by
  classical
  calc
    L.probability (fun omega ↦ ∃ v : V,
        r ≤ (outerIncidentEdges G U v ∩
          preliminaryResidualOuterEdges G U (selected omega)).card) ≤
      ∑ v ∈ (univ : Finset V), L.probability (fun omega ↦
        r ≤ (outerIncidentEdges G U v ∩
          preliminaryResidualOuterEdges G U (selected omega)).card) := by
      simpa using L.probability_exists_le (univ : Finset V)
        (fun v omega ↦ r ≤ (outerIncidentEdges G U v ∩
          preliminaryResidualOuterEdges G U (selected omega)).card)
    _ ≤ ∑ v ∈ (univ : Finset V),
        ((outerIncidentEdges G U v).powersetCard r).card *
          (survival ^ r + b) := by
      apply sum_le_sum
      intro v _hv
      let event : Finset (Sym2 V) → Omega → Prop := fun E omega ↦
        E ⊆ preliminaryResidualOuterEdges G U (selected omega)
      calc
        L.probability (fun omega ↦
            r ≤ (outerIncidentEdges G U v ∩
              preliminaryResidualOuterEdges G U (selected omega)).card) ≤
          L.probability (fun omega ↦ ∃ E ∈
            (outerIncidentEdges G U v).powersetCard r, event E omega) := by
            apply L.probability_mono
            intro omega hlarge
            obtain ⟨E, hEsub, hEcard⟩ := exists_subset_card_eq hlarge
            exact ⟨E, mem_powersetCard.mpr
              ⟨hEsub.trans inter_subset_left, hEcard⟩,
              hEsub.trans inter_subset_right⟩
        _ ≤ ∑ E ∈ (outerIncidentEdges G U v).powersetCard r,
            L.probability (event E) :=
          L.probability_exists_le
            ((outerIncidentEdges G U v).powersetCard r) event
        _ ≤ ∑ _E ∈ (outerIncidentEdges G U v).powersetCard r,
            (survival ^ r + b) := by
          apply sum_le_sum
          intro E hE
          have hcard : E.card = r := (mem_powersetCard.mp hE).2
          have houter : E ⊆ outerGraphEdges G U := by
            intro e he
            exact (mem_outerIncidentEdges_iff.mp
              ((mem_powersetCard.mp hE).1 he)).1
          have hmono : L.probability (event E) ≤
              L.probability (fun omega ↦
                ∀ e ∈ E,
                  e ∉ (coveredGraph (selected omega)).edgeSet) := by
            apply L.probability_mono
            intro omega hresidual
            exact subset_uncovered_of_subset_preliminaryResidualOuterEdges
              hresidual
          exact hmono.trans (by
            simpa only [hcard] using (htracked E hcard houter))
        _ = ((outerIncidentEdges G U v).powersetCard r).card *
            (survival ^ r + b) := by
          simp only [sum_const, nsmul_eq_mul]
    _ = trackedResidualOuterIncidenceTail V G U survival b r := by
      simp [trackedResidualOuterIncidenceTail]

/-- Condition an initial product law on any explicitly bounded residual-star
event.  Specialized geometries can therefore use exactly the residual edge
family exposed by their preliminary process. -/
theorem IsInitialProductBound.exists_conditionedOn_residualStarEvent
    {Omega V : Type*} [Fintype Omega] [DecidableEq Omega]
    [Fintype V] [DecidableEq V] {ell : ℕ}
    {L : FiniteLaw Omega} {W : Vortex V ell} {k : Fin (ell + 1)}
    {selected : Omega → TripleSystemOn V}
    {reserve : Omega → Finset (Sym2 V)}
    {p C b epsilon : ℝ≥0}
    (hproduct : IsInitialProductBound L selected p C b)
    (hC : 1 ≤ C) (Good : Omega → Prop)
    (hbad : L.probability (fun omega ↦ ¬ Good omega) ≤ epsilon)
    (hepsilon : epsilon < 1) :
    ∃ hGood : 0 < L.probability Good,
      (L.conditionOn Good hGood).SupportedOn Good ∧
      1 - epsilon ≤ L.probability Good ∧
      IsReserveStronglyWellDistributed (L.conditionOn Good hGood) W k
        selected (fun _ ↦ (∅ : TripleSystemOn V)) reserve p 1
        (C / L.probability Good) b := by
  have hlower : 1 - epsilon ≤ L.probability Good := by
    rw [L.probability_not Good] at hbad
    exact tsub_le_iff_tsub_le.mp hbad
  have hGood : 0 < L.probability Good :=
    (tsub_pos_iff_lt.mpr hepsilon).trans_le hlower
  refine ⟨hGood, L.conditionOn_supported Good hGood, hlower, ?_⟩
  exact (hproduct.toReserveStronglyWellDistributed_one
    (W := W) (k := k) (reserve := reserve) hC).conditionOn Good hGood

theorem IsInitialProductBound.exists_conditionedOn_trackedResidualOuterIncidence
    {Omega V : Type*} [Fintype Omega] [DecidableEq Omega]
    [Fintype V] [DecidableEq V] {ell : ℕ}
    {L : FiniteLaw Omega} {W : Vortex V ell} {k : Fin (ell + 1)}
    {selected : Omega → TripleSystemOn V}
    {reserve : Omega → Finset (Sym2 V)}
    {p C b survival : ℝ≥0}
    (hproduct : IsInitialProductBound L selected p C b)
    (hC : 1 ≤ C) (G : SimpleGraph V) (U : Finset V) (r : ℕ)
    (htracked : ∀ E : Finset (Sym2 V), E.card = r →
      E ⊆ outerGraphEdges G U →
      L.probability (fun omega ↦
        ∀ e ∈ E, e ∉ (coveredGraph (selected omega)).edgeSet) ≤
          survival ^ E.card + b)
    (htail : trackedResidualOuterIncidenceTail V G U survival b r < 1) :
    let Good : Omega → Prop := fun omega ↦ ∀ v : V,
      (outerIncidentEdges G U v ∩
        preliminaryResidualOuterEdges G U (selected omega)).card < r
    ∃ hGood : 0 < L.probability Good,
      (L.conditionOn Good hGood).SupportedOn Good ∧
      1 - trackedResidualOuterIncidenceTail V G U survival b r ≤
        L.probability Good ∧
      IsReserveStronglyWellDistributed (L.conditionOn Good hGood) W k
        selected (fun _ ↦ (∅ : TripleSystemOn V)) reserve p 1
        (C / L.probability Good) b := by
  classical
  dsimp only
  let Bad : Omega → Prop := fun omega ↦ ∃ v : V,
    r ≤ (outerIncidentEdges G U v ∩
      preliminaryResidualOuterEdges G U (selected omega)).card
  let Good : Omega → Prop := fun omega ↦ ∀ v : V,
    (outerIncidentEdges G U v ∩
      preliminaryResidualOuterEdges G U (selected omega)).card < r
  have hbad : L.probability Bad ≤
      trackedResidualOuterIncidenceTail V G U survival b r := by
    simpa only [Bad] using
      probability_exists_large_residualOuter_incidence_le_of_tracked
        (L := L) (selected := selected) G U survival b r htracked
  have hbadlt : L.probability Bad < 1 := hbad.trans_lt htail
  have hGoodEq : L.probability Good = 1 - L.probability Bad := by
    rw [← L.probability_not Bad]
    congr 1
    funext omega
    simp only [Good, Bad]
    push_neg
    rfl
  have hlower :
      1 - trackedResidualOuterIncidenceTail V G U survival b r ≤
        L.probability Good := by
    rw [hGoodEq]
    exact tsub_le_tsub_left hbad 1
  have hGood : 0 < L.probability Good := by
    rw [hGoodEq]
    exact tsub_pos_iff_lt.mpr hbadlt
  refine ⟨hGood, L.conditionOn_supported Good hGood, hlower, ?_⟩
  exact (hproduct.toReserveStronglyWellDistributed_one
    (W := W) (k := k) (reserve := reserve) hC).conditionOn Good hGood

end

end Erdos207
