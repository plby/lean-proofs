/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.ResidualGraphDistribution
import ErdosProblems.Erdos207.PendingGreedySurvival

/-! # Adjoining triangles exposes their genuinely old residual edges -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

attribute [local instance] Classical.propDecidable

theorem residualDistributionEvent_adjoin_partition
    {Ω Ξ V : Type*} [Fintype Ω] [Fintype Ξ] [Fintype V] [DecidableEq V]
    (initial later : Ω → TripleSystemOn V) (added : Ω → Ξ → TripleSystemOn V)
    (G : SimpleGraph V) (Ifix Dfix : TripleSystemOn V) (Efix : Finset (Sym2 V))
    (z : Ω × Ξ)
    (hpack : IsPackingOn ((initial z.1 ∪ later z.1) ∪ added z.1 z.2))
    (hdis : Disjoint (initial z.1 ∪ later z.1) (added z.1 z.2))
    (hgraph : ∀ T ∈ added z.1 z.2, tripleEdgeFinset T ⊆ graphEdges G)
    (hz : ResidualDistributionEvent (jointInitial initial) (jointLater later added) Ifix Dfix Efix z) :
    ∃ S ∈ Dfix.powerset,
      IsPackingOn (Dfix \ S) ∧
      (Dfix \ S).biUnion tripleEdgeFinset ⊆ graphEdges G ∧
      Disjoint ((Dfix \ S).biUnion tripleEdgeFinset) Efix ∧
      ResidualDistributionEvent initial later Ifix S (pendingSurvivalEdges (Dfix \ S) Efix) z.1 ∧
      Dfix \ S ⊆ added z.1 z.2 := by
  classical
  obtain ⟨S, hS, hOld, hNew⟩ := strongDistributionEvent_jointLater_partition initial later added
    Ifix Dfix Efix z hz.toStrong
  have hQpack : IsPackingOn (Dfix \ S) :=
    hpack.mono (hNew.trans (subset_union_right : added z.1 z.2 ⊆ _))
  have hQgraph : (Dfix \ S).biUnion tripleEdgeFinset ⊆ graphEdges G := by
    intro e he
    obtain ⟨T, hT, heT⟩ := mem_biUnion.mp he
    exact hgraph T (hNew hT) heT
  have hQE : Disjoint ((Dfix \ S).biUnion tripleEdgeFinset) Efix := by
    apply disjoint_left.mpr
    intro e heQ heE
    apply hz.2.2 e heE
    obtain ⟨T, hT, heT⟩ := mem_biUnion.mp heQ
    rw [coveredGraph_edgeSet_eq_biUnion]
    exact mem_biUnion.mpr ⟨T, mem_union_right _ (mem_union_right _ (hNew hT)), heT⟩
  refine ⟨S, hS, hQpack, hQgraph, hQE, ⟨hOld.1, hOld.2.1, ?_⟩, hNew⟩
  intro e he hcovered
  obtain heQ | heE := mem_union.mp he
  · obtain ⟨T, hT, heT⟩ := mem_biUnion.mp heQ
    rw [coveredGraph_edgeSet_eq_biUnion] at hcovered
    exact disjoint_left.mp (hpack.disjoint_family_edges hdis) hcovered
      (mem_biUnion.mpr ⟨T, hNew hT, heT⟩)
  · apply hz.2.2 e heE
    rw [coveredGraph_edgeSet_eq_biUnion] at hcovered ⊢
    obtain ⟨T, hT, heT⟩ := mem_biUnion.mp hcovered
    exact mem_biUnion.mpr ⟨T, by simpa only [jointInitial, jointLater, union_assoc] using
      (mem_union_left (added z.1 z.2) hT), heT⟩

theorem FiniteLaw.jointBind_residual_adjoin_probability_le_on_support
    {Ω Ξ V : Type*} [Fintype Ω] [Fintype Ξ] [Fintype V]
    [DecidableEq Ω] [DecidableEq Ξ] [DecidableEq V]
    (L : FiniteLaw Ω) (K : Ω → FiniteLaw Ξ)
    (G : SimpleGraph V) (initial later : Ω → TripleSystemOn V)
    (added : Ω → Ξ → TripleSystemOn V) (addedBound : TripleSystemOn V → ℝ≥0)
    (hadded : ∀ ω, 0 < L.mass ω → ∀ Q, (K ω).probability (fun ξ ↦ Q ⊆ added ω ξ) ≤ addedBound Q)
    (hstruct : ∀ ω, 0 < L.mass ω → (K ω).SupportedOn fun ξ ↦
      IsPackingOn ((initial ω ∪ later ω) ∪ added ω ξ) ∧
      Disjoint (initial ω ∪ later ω) (added ω ξ) ∧
      ∀ T ∈ added ω ξ, tripleEdgeFinset T ⊆ graphEdges G)
    (Ifix Dfix : TripleSystemOn V) (Efix : Finset (Sym2 V)) :
    (L.jointBind K).probability
      (ResidualDistributionEvent (jointInitial initial) (jointLater later added) Ifix Dfix Efix) ≤
      ∑ S ∈ Dfix.powerset, if IsPackingOn (Dfix \ S) ∧
        (Dfix \ S).biUnion tripleEdgeFinset ⊆ graphEdges G ∧
        Disjoint ((Dfix \ S).biUnion tripleEdgeFinset) Efix then
        addedBound (Dfix \ S) * L.probability
          (ResidualDistributionEvent initial later Ifix S (pendingSurvivalEdges (Dfix \ S) Efix)) else 0 := by
  classical
  let Good := fun S : TripleSystemOn V ↦ IsPackingOn (Dfix \ S) ∧
    (Dfix \ S).biUnion tripleEdgeFinset ⊆ graphEdges G ∧
    Disjoint ((Dfix \ S).biUnion tripleEdgeFinset) Efix
  let Old := fun S : TripleSystemOn V ↦
    ResidualDistributionEvent initial later Ifix S (pendingSurvivalEdges (Dfix \ S) Efix)
  let Event := fun S : TripleSystemOn V ↦ fun z : Ω × Ξ ↦
    Good S ∧ Old S z.1 ∧ Dfix \ S ⊆ added z.1 z.2
  have hsupport := (show L.SupportedOn (fun ω ↦ 0 < L.mass ω) from fun _ h ↦ h).jointBind hstruct
  have hcover : (L.jointBind K).probability
      (ResidualDistributionEvent (jointInitial initial) (jointLater later added) Ifix Dfix Efix) ≤
      (L.jointBind K).probability (fun z ↦ ∃ S ∈ Dfix.powerset, Event S z) := by
    apply (L.jointBind K).probability_mono_of_supported hsupport
    intro z hz hevent
    obtain ⟨S, hS, hQ, hG, hQE, hOld, hNew⟩ := residualDistributionEvent_adjoin_partition
      initial later added G Ifix Dfix Efix z hz.2.1 hz.2.2.1 hz.2.2.2 hevent
    exact ⟨S, hS, ⟨hQ, hG, hQE⟩, hOld, hNew⟩
  apply hcover.trans ((L.jointBind K).probability_exists_le Dfix.powerset Event |>.trans _)
  apply sum_le_sum
  intro S hS
  change (L.jointBind K).probability (Event S) ≤ if Good S then _ else _
  by_cases hgood : Good S
  · rw [if_pos hgood]
    have hremove : Event S = (fun z ↦ Old S z.1 ∧ Dfix \ S ⊆ added z.1 z.2) := by
      funext z
      simp only [Event, hgood, true_and]
    rw [hremove]
    exact L.jointBind_probability_and_le_on_support K (Old S)
      (fun ω ξ ↦ Dfix \ S ⊆ added ω ξ) (addedBound (Dfix \ S))
      (fun ω hω _ ↦ hadded ω hω (Dfix \ S))
  · rw [if_neg hgood]
    have hzero : Event S = (fun _ ↦ False) := by
      funext z
      simp only [Event, hgood, false_and]
    rw [hzero, FiniteLaw.probability_false]

theorem FiniteLaw.jointBind_residual_adjoin_probability_le
    {Ω Ξ V : Type*} [Fintype Ω] [Fintype Ξ] [Fintype V]
    [DecidableEq Ω] [DecidableEq Ξ] [DecidableEq V]
    (L : FiniteLaw Ω) (K : Ω → FiniteLaw Ξ)
    (G : SimpleGraph V) (initial later : Ω → TripleSystemOn V)
    (added : Ω → Ξ → TripleSystemOn V) (addedBound : TripleSystemOn V → ℝ≥0)
    (hadded : ∀ ω Q, (K ω).probability (fun ξ ↦ Q ⊆ added ω ξ) ≤ addedBound Q)
    (hstruct : ∀ ω, 0 < L.mass ω → (K ω).SupportedOn fun ξ ↦
      IsPackingOn ((initial ω ∪ later ω) ∪ added ω ξ) ∧
      Disjoint (initial ω ∪ later ω) (added ω ξ) ∧
      ∀ T ∈ added ω ξ, tripleEdgeFinset T ⊆ graphEdges G)
    (Ifix Dfix : TripleSystemOn V) (Efix : Finset (Sym2 V)) :
    (L.jointBind K).probability
      (ResidualDistributionEvent (jointInitial initial) (jointLater later added) Ifix Dfix Efix) ≤
      ∑ S ∈ Dfix.powerset, if IsPackingOn (Dfix \ S) ∧
        (Dfix \ S).biUnion tripleEdgeFinset ⊆ graphEdges G ∧
        Disjoint ((Dfix \ S).biUnion tripleEdgeFinset) Efix then
        addedBound (Dfix \ S) * L.probability
          (ResidualDistributionEvent initial later Ifix S (pendingSurvivalEdges (Dfix \ S) Efix)) else 0 :=
  L.jointBind_residual_adjoin_probability_le_on_support K G initial later added addedBound
    (fun ω _ ↦ hadded ω) hstruct Ifix Dfix Efix

theorem IsResidualGraphStronglyWellDistributed.jointBind_adjoin_le
    {Ω Ξ V : Type*} [Fintype Ω] [Fintype Ξ] [Fintype V]
    [DecidableEq Ω] [DecidableEq Ξ] [DecidableEq V] {ell : ℕ}
    {L : FiniteLaw Ω} {K : Ω → FiniteLaw Ξ} {W : Vortex V ell} {k : Fin (ell + 1)}
    {G : SimpleGraph V} {initial later : Ω → TripleSystemOn V} {p C b : ℝ≥0}
    (hstrong : IsResidualGraphStronglyWellDistributed L W k G initial later p C b)
    (added : Ω → Ξ → TripleSystemOn V) (addedBound : TripleSystemOn V → ℝ≥0)
    (hadded : ∀ ω Q, (K ω).probability (fun ξ ↦ Q ⊆ added ω ξ) ≤ addedBound Q)
    (hstruct : ∀ ω, 0 < L.mass ω → (K ω).SupportedOn fun ξ ↦
      IsPackingOn ((initial ω ∪ later ω) ∪ added ω ξ) ∧
      Disjoint (initial ω ∪ later ω) (added ω ξ) ∧
      ∀ T ∈ added ω ξ, tripleEdgeFinset T ⊆ graphEdges G)
    (Ifix Dfix : TripleSystemOn V) (Efix : Finset (Sym2 V))
    (hdis : Disjoint Ifix Dfix) (hE : Efix ⊆ graphEdges G) :
    (L.jointBind K).probability
      (ResidualDistributionEvent (jointInitial initial) (jointLater later added) Ifix Dfix Efix) ≤
      ∑ S ∈ Dfix.powerset, if IsPackingOn (Dfix \ S) ∧
        (Dfix \ S).biUnion tripleEdgeFinset ⊆ graphEdges G ∧
        Disjoint ((Dfix \ S).biUnion tripleEdgeFinset) Efix then
        addedBound (Dfix \ S) *
          (C ^ (Ifix.card + S.card + (3 * (Dfix \ S).card + Efix.card)) *
            (p ^ (3 * (Dfix \ S).card + Efix.card) *
              (Fintype.card V : ℝ≥0)⁻¹ ^ Ifix.card * laterTriangleScale W k p S + b)) else 0 := by
  classical
  apply (L.jointBind_residual_adjoin_probability_le K G initial later added addedBound hadded hstruct
    Ifix Dfix Efix).trans
  apply sum_le_sum
  intro S hS
  split_ifs with hgood
  · apply mul_le_mul_of_nonneg_left _ zero_le
    have hedge : pendingSurvivalEdges (Dfix \ S) Efix ⊆ graphEdges G := union_subset hgood.2.1 hE
    have hbound := hstrong Ifix S (pendingSurvivalEdges (Dfix \ S) Efix)
      (Disjoint.mono_right (mem_powerset.mp hS) hdis) hedge
    simpa only [card_pendingSurvivalEdges hgood.1 hgood.2.2] using hbound
  · exact le_rfl

end

end Erdos207
