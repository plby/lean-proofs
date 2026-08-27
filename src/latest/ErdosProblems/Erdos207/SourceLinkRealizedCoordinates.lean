/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceLinkCanonicalMoment
import ErdosProblems.Erdos207.ResidualReserveCandidateLaw
import ErdosProblems.Erdos207.LocalizedMasterUnionRootedThreatWeight

/-! # Realized marked coordinates in the corrected residual-reserve law -/

namespace Erdos207

open Finset
open scoped Classical NNReal

noncomputable section

def sourceLinkRetainedEdges
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (U : Finset V)
    (I D : TripleSystemOn V) (R : Finset (Sym2 V)) : Finset (Sym2 V) :=
  (graphEdges G).filter fun e ↦ e ∉ (coveredGraph (I ∪ D)).edgeSet ∧
    (IsCrossingEdge U e → e ∈ R)

def sourceLinkRealizedCoordinates
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (U : Finset V)
    (I D Q : TripleSystemOn V) (R : Finset (Sym2 V)) : Finset (SourceLinkCoordinate V) :=
  (I.disjSum (D.disjSum Q)).disjSum (sourceLinkRetainedEdges G U I D R)

theorem sourceLinkRetainedEdges_subset_iff
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (U : Finset V)
    (I D : TripleSystemOn V) (R E : Finset (Sym2 V)) :
    E ⊆ sourceLinkRetainedEdges G U I D R ↔
      E ⊆ graphEdges G ∧ (∀ e ∈ E, e ∉ (coveredGraph (I ∪ D)).edgeSet) ∧
        E.filter (IsCrossingEdge U) ⊆ R := by
  constructor
  · intro h
    refine ⟨fun e he ↦ (mem_filter.mp (h he)).1,
      fun e he ↦ (mem_filter.mp (h he)).2.1, ?_⟩
    intro e he
    have hh := mem_filter.mp he
    exact (mem_filter.mp (h hh.1)).2.2 hh.2
  · rintro ⟨hG, hnot, hR⟩ e he
    exact mem_filter.mpr ⟨hG he, hnot e he, fun hc ↦ hR (mem_filter.mpr ⟨he, hc⟩)⟩

theorem sourceLink_subset_realized_iff
    {Ω Ξ V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U : Finset V) (initial later : Ω → TripleSystemOn V)
    (candidate : Ω → Ξ → TripleSystemOn V) (reserve : Ω → Finset (Sym2 V))
    (H : Finset (SourceLinkCoordinate V)) (hE : H.toRight ⊆ graphEdges G) (z : Ω × Ξ) :
    H ⊆ sourceLinkRealizedCoordinates G U (initial z.1) (later z.1) (candidate z.1 z.2) (reserve z.1) ↔
      ResidualReserveDistributionEvent initial later reserve H.toLeft.toLeft H.toLeft.toRight.toLeft
        H.toRight (H.toRight.filter (IsCrossingEdge U)) z.1 ∧
          H.toLeft.toRight.toRight ⊆ candidate z.1 z.2 := by
  simp only [sourceLinkRealizedCoordinates, subset_disjSum, sourceLinkRetainedEdges_subset_iff,
    ResidualReserveDistributionEvent, ResidualDistributionEvent]
  tauto

theorem laterTriangleScale_eq_prefix_weight
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (k : Fin (ell + 1)) (p : ℝ≥0) (D : TripleSystemOn V) :
    laterTriangleScale W k p D = setWeight (vortexTripleWeight (W.prefix k) p) D := by
  unfold laterTriangleScale setWeight vortexTripleWeight
  apply prod_congr rfl
  intro T _
  rw [W.prefix_U_level_eq_truncatedLevel k T]

theorem sourceLink_mixed_weight_eq_prescription
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (k : Fin (ell + 1)) (U : Finset V) (p r sigma : ℝ≥0)
    (H : Finset (SourceLinkCoordinate V)) :
    setWeight (sourceLinkMixedWeight (fun _ ↦ (Fintype.card V : ℝ≥0)⁻¹)
      (vortexTripleWeight (W.prefix k) p) (fun _ ↦ sigma) (sourceLinkCanonicalEdgeWeight U p r)) H =
      sigma ^ H.toLeft.toRight.toRight.card *
        (p ^ H.toRight.card * r ^ (H.toRight.filter (IsCrossingEdge U)).card *
          (Fintype.card V : ℝ≥0)⁻¹ ^ H.toLeft.toLeft.card *
            laterTriangleScale W k p H.toLeft.toRight.toLeft) := by
  have hfactor : setWeight (sourceLinkMixedWeight (fun _ ↦ (Fintype.card V : ℝ≥0)⁻¹)
      (vortexTripleWeight (W.prefix k) p) (fun _ ↦ sigma) (sourceLinkCanonicalEdgeWeight U p r)) H =
      setWeight (sourceLinkTriangleWeight (fun _ ↦ (Fintype.card V : ℝ≥0)⁻¹)
        (vortexTripleWeight (W.prefix k) p) (fun _ ↦ sigma)) H.toLeft *
          setWeight (sourceLinkCanonicalEdgeWeight U p r) H.toRight := by
    unfold setWeight
    rw [prod_sum_eq_prod_toLeft_mul_prod_toRight]
    rfl
  rw [hfactor, sourceLinkTriangleWeight_factor, sourceLinkCanonicalEdgeWeight_product,
    laterTriangleScale_eq_prefix_weight]
  simp only [setWeight, prod_const]
  ring

theorem IsResidualReserveStronglyWellDistributed.jointBind_sourceLink_prescriptions
    {Ω Ξ V : Type*} [Fintype Ω] [Fintype Ξ] [Fintype V]
    [DecidableEq Ω] [DecidableEq Ξ] [DecidableEq V] {ell : ℕ}
    {L : FiniteLaw Ω} {K : Ω → FiniteLaw Ξ} {W : Vortex V ell} {k : Fin (ell + 1)}
    {G : SimpleGraph V} {initial later : Ω → TripleSystemOn V}
    {reserve : Ω → Finset (Sym2 V)} {p r C b : ℝ≥0}
    (hstrong : IsResidualReserveStronglyWellDistributed L W k G initial later reserve p r C b)
    (U : Finset V) (candidate : Ω → Ξ → TripleSystemOn V) (sigma J delta : ℝ≥0)
    (hsigma : sigma ≤ 1) (hC : 1 ≤ C) (hJ : 1 ≤ J)
    (hcandidate : ∀ ω, 0 < L.mass ω → ∀ Q,
      (K ω).probability (fun ξ ↦ Q ⊆ candidate ω ξ) ≤ sigma ^ Q.card + J ^ Q.card * delta)
    (H : Finset (SourceLinkCoordinate V)) (hdis : Disjoint H.toLeft.toLeft H.toLeft.toRight.toLeft)
    (hE : H.toRight ⊆ graphEdges G) :
    (L.jointBind K).probability (fun z ↦ H ⊆ sourceLinkRealizedCoordinates G U
      (initial z.1) (later z.1) (candidate z.1 z.2) (reserve z.1)) ≤
      (max (C ^ 2) J) ^ H.card *
        (setWeight (sourceLinkMixedWeight (fun _ ↦ (Fintype.card V : ℝ≥0)⁻¹)
          (vortexTripleWeight (W.prefix k) p) (fun _ ↦ sigma) (sourceLinkCanonicalEdgeWeight U p r)) H + b + delta) := by
  have hraw := hstrong.jointBind_candidate_prescriptions candidate sigma J delta hsigma hC hJ hcandidate
    H.toLeft.toLeft H.toLeft.toRight.toLeft H.toLeft.toRight.toRight H.toRight
    (H.toRight.filter (IsCrossingEdge U)) hdis hE (filter_subset _ _)
  have hevent : (fun z : Ω × Ξ ↦ H ⊆ sourceLinkRealizedCoordinates G U
        (initial z.1) (later z.1) (candidate z.1 z.2) (reserve z.1)) =
      (fun z ↦ ResidualReserveDistributionEvent initial later reserve
        H.toLeft.toLeft H.toLeft.toRight.toLeft H.toRight (H.toRight.filter (IsCrossingEdge U)) z.1 ∧
          H.toLeft.toRight.toRight ⊆ candidate z.1 z.2) := by
    funext z
    exact propext (sourceLink_subset_realized_iff G U initial later candidate reserve H hE z)
  have hcard : H.toLeft.toLeft.card + H.toLeft.toRight.toLeft.card +
      H.toLeft.toRight.toRight.card + H.toRight.card = H.card := by
    rw [add_assoc H.toLeft.toLeft.card, card_toLeft_add_card_toRight,
      card_toLeft_add_card_toRight, card_toLeft_add_card_toRight]
  rw [hevent, sourceLink_mixed_weight_eq_prescription]
  simpa only [hcard] using hraw

end

end Erdos207
