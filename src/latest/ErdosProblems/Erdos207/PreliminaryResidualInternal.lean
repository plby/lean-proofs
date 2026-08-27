/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.PreliminaryOuterResidual
import ErdosProblems.Erdos207.InternalEdgeTerminalRootSuccess

/-!
# Conditioning on bounded residual internal incidence

The preliminary phase leaves a random family of uncovered outer edges.  The
internal cover-down only schedules those residual edges whose two endpoints
lie outside the next vortex set.  This file identifies that subfamily and
conditions the preliminary law on the high-probability event that all of its
vertex degrees are small.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- Residual preliminary edges whose two endpoints lie outside `U`. -/
def preliminaryResidualInternalEdges
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U : Finset V) (P : TripleSystemOn V) :
    Finset (Sym2 V) :=
  internalOuterEdges G U ∩ preliminaryResidualOuterEdges G U P

lemma preliminaryResidualInternalEdges_subset_internalOuterEdges
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U : Finset V) (P : TripleSystemOn V) :
    preliminaryResidualInternalEdges G U P ⊆ internalOuterEdges G U :=
  inter_subset_left

lemma preliminaryResidualInternalEdges_subset_residualOuterEdges
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U : Finset V) (P : TripleSystemOn V) :
    preliminaryResidualInternalEdges G U P ⊆
      preliminaryResidualOuterEdges G U P :=
  inter_subset_right

/-- An internal outer edge is, in particular, an outer edge. -/
lemma internalOuterEdges_subset_outerGraphEdges
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U : Finset V) :
    internalOuterEdges G U ⊆ outerGraphEdges G U := by
  intro e he
  have he' := mem_internalOuterEdges_iff.mp he
  apply mem_outerGraphEdges_iff.mpr
  refine ⟨he'.1, ?_⟩
  intro hsub
  apply he'.2.1
  apply hsub
  simpa using Sym2.out_fst_mem e

/-- The scheduled star of the residual internal family is contained in the
outer-incidence test family intersected with all residual outer edges. -/
lemma scheduledEdgesAt_preliminaryResidualInternalEdges_subset
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U : Finset V) (P : TripleSystemOn V) (v : V) :
    scheduledEdgesAt (preliminaryResidualInternalEdges G U P) v ⊆
      outerIncidentEdges G U v ∩ preliminaryResidualOuterEdges G U P := by
  intro e he
  have hs := mem_scheduledEdgesAt_iff.mp he
  have hres := mem_inter.mp hs.1
  apply mem_inter.mpr
  refine ⟨mem_outerIncidentEdges_iff.mpr ⟨?_, ?_⟩, hres.2⟩
  · exact internalOuterEdges_subset_outerGraphEdges G U hres.1
  · simpa using hs.2

/-- Hence every preliminary outcome with outer residual degree at most `d`
has scheduled residual internal degree at most `d`. -/
theorem scheduled_residualInternal_incidence_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {U : Finset V} {P : TripleSystemOn V} {d : ℕ}
    (hdegree : ∀ v : V,
      (outerIncidentEdges G U v ∩
        preliminaryResidualOuterEdges G U P).card ≤ d) :
    ∀ v : V,
      (scheduledEdgesAt (preliminaryResidualInternalEdges G U P) v).card ≤ d := by
  intro v
  exact (card_le_card
    (scheduledEdgesAt_preliminaryResidualInternalEdges_subset G U P v)).trans
      (hdegree v)

/-- The explicit union-bound error for a residual outer-degree cutoff. -/
def residualOuterIncidenceTail
    (V : Type*) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U : Finset V) (eta : ℝ≥0) (r : ℕ) : ℝ≥0 :=
  ∑ v : V, ((outerIncidentEdges G U v).powersetCard r).card * eta ^ r

/-- A pure selected/residual product law can be conditioned on uniformly
bounded residual incidence.  The only loss is the reciprocal of the explicit
good-event lower bound `1 - residualOuterIncidenceTail`. -/
theorem FiniteLaw.exists_conditionedOn_residualOuterIncidence
    {Omega V : Type*} [Fintype Omega] [Fintype V] [DecidableEq V]
    (L : FiniteLaw Omega) (G : SimpleGraph V) (U : Finset V)
    (selected : Omega → TripleSystemOn V)
    (residual : Omega → Finset (Sym2 V))
    (alpha eta : ℝ≥0) (r : ℕ)
    (hmixed : ∀ Q : TripleSystemOn V, ∀ E : Finset (Sym2 V),
      L.probability (fun omega ↦ Q ⊆ selected omega ∧
        E ⊆ residual omega) ≤ alpha ^ Q.card * eta ^ E.card)
    (htail : residualOuterIncidenceTail V G U eta r < 1) :
    let Good : Omega → Prop := fun omega ↦ ∀ v : V,
      (outerIncidentEdges G U v ∩ residual omega).card < r
    ∃ hGood : 0 < L.probability Good,
      (L.conditionOn Good hGood).SupportedOn Good ∧
      1 - residualOuterIncidenceTail V G U eta r ≤ L.probability Good ∧
      ∀ Q : TripleSystemOn V, ∀ E : Finset (Sym2 V),
        (L.conditionOn Good hGood).probability (fun omega ↦
          Q ⊆ selected omega ∧ E ⊆ residual omega) ≤
        (alpha / (1 - residualOuterIncidenceTail V G U eta r)) ^ Q.card *
          (eta / (1 - residualOuterIncidenceTail V G U eta r)) ^ E.card := by
  classical
  dsimp only
  let Bad : Omega → Prop := fun omega ↦ ∃ v : V,
    r ≤ (outerIncidentEdges G U v ∩ residual omega).card
  let Good : Omega → Prop := fun omega ↦ ∀ v : V,
    (outerIncidentEdges G U v ∩ residual omega).card < r
  have hbad : L.probability Bad ≤ residualOuterIncidenceTail V G U eta r := by
    have hraw := L.probability_exists_large_residualOuter_incidence_le
      G U selected residual alpha eta 0 r
      (fun Q E ↦ (hmixed Q E).trans (by simp))
    simpa only [Bad, residualOuterIncidenceTail, add_zero] using hraw
  have hbadlt : L.probability Bad < 1 := hbad.trans_lt htail
  have hGoodEq : L.probability Good = 1 - L.probability Bad := by
    rw [← L.probability_not Bad]
    congr 1
    funext omega
    simp only [Good, Bad]
    push_neg
    rfl
  have hlower : 1 - residualOuterIncidenceTail V G U eta r ≤
      L.probability Good := by
    rw [hGoodEq]
    exact tsub_le_tsub_left hbad 1
  have hGood : 0 < L.probability Good := by
    rw [hGoodEq]
    exact tsub_pos_iff_lt.mpr hbadlt
  refine ⟨hGood, L.conditionOn_supported Good hGood, hlower, ?_⟩
  have hden : 0 < 1 - residualOuterIncidenceTail V G U eta r :=
    tsub_pos_iff_lt.mpr htail
  have hraw : ∀ Q : TripleSystemOn V, ∀ E : Finset (Sym2 V),
      L.probability (fun omega ↦ Good omega ∧
        Q ⊆ selected omega ∧ E ⊆ residual omega) ≤
          alpha ^ Q.card * eta ^ E.card := by
    intro Q E
    exact (L.probability_mono fun _ h ↦ h.2).trans (hmixed Q E)
  intro Q E
  have hconditioned := L.conditionOn_probability_mixedProduct_le Good
    selected residual alpha eta hGood hraw Q E
  have halpha : alpha / L.probability Good ≤
      alpha / (1 - residualOuterIncidenceTail V G U eta r) :=
    div_le_div_of_nonneg_left zero_le hden hlower
  have heta : eta / L.probability Good ≤
      eta / (1 - residualOuterIncidenceTail V G U eta r) :=
    div_le_div_of_nonneg_left zero_le hden hlower
  exact hconditioned.trans (by gcongr)

/-- At the cutoff `d + 1`, support of the conditioned law supplies exactly
the non-strict scheduled-degree bound required by retrospective success. -/
theorem scheduled_residualInternal_incidence_le_of_good
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {U : Finset V} {P : TripleSystemOn V} {d : ℕ}
    (hgood : ∀ v : V,
      (outerIncidentEdges G U v ∩
        preliminaryResidualOuterEdges G U P).card < d + 1) :
    ∀ v : V,
      (scheduledEdgesAt (preliminaryResidualInternalEdges G U P) v).card ≤ d := by
  apply scheduled_residualInternal_incidence_le
  intro v
  exact Nat.lt_succ_iff.mp (by
    simpa only [Nat.succ_eq_add_one] using hgood v)

end

end Erdos207
