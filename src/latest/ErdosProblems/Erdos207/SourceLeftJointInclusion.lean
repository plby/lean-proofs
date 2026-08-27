/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceQuasiJointInclusion
import ErdosProblems.Erdos207.ResidualReserveDistribution

/-! # Two-colour coordinates with edges both reserved and fully residual -/

namespace Erdos207

open Finset
open scoped Classical NNReal

noncomputable section

def sourceLeftRealizedCoordinates
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (I D : TripleSystemOn V) (reserve : Finset (Sym2 V)) : Finset (SourceQuasiCoordinate V) :=
  (I.disjSum D).disjSum ((graphEdges G ∩ reserve).filter fun e ↦ e ∉ (coveredGraph (I ∪ D)).edgeSet)

theorem sourceLeft_subset_realized_iff
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (I D : TripleSystemOn V) (reserve : Finset (Sym2 V)) (H : Finset (SourceQuasiCoordinate V)) :
    H ⊆ sourceLeftRealizedCoordinates G I D reserve ↔
      H.toLeft.toLeft ⊆ I ∧ H.toLeft.toRight ⊆ D ∧ H.toRight ⊆ graphEdges G ∧
        H.toRight ⊆ reserve ∧ ∀ e ∈ H.toRight, e ∉ (coveredGraph (I ∪ D)).edgeSet := by
  simp only [sourceLeftRealizedCoordinates, subset_disjSum]
  constructor
  · rintro ⟨⟨hI, hD⟩, hE⟩
    exact ⟨hI, hD, fun e he ↦ (mem_inter.mp (mem_filter.mp (hE he)).1).1,
      fun e he ↦ (mem_inter.mp (mem_filter.mp (hE he)).1).2,
      fun e he ↦ (mem_filter.mp (hE he)).2⟩
  · rintro ⟨hI, hD, hG, hR, hE⟩
    exact ⟨⟨hI, hD⟩, fun e he ↦ mem_filter.mpr ⟨mem_inter.mpr ⟨hG he, hR he⟩, hE e he⟩⟩

theorem sourceLeft_weight_eq_prescription
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (k : Fin (ell+1)) (p r : ℝ≥0) (H : Finset (SourceQuasiCoordinate V)) :
    setWeight (sourceQuasiWeight (fun _ ↦ (Fintype.card V : ℝ≥0)⁻¹)
      (vortexTripleWeight (W.prefix k) p) (p*r)) H =
      p^H.toRight.card * r^H.toRight.card * (Fintype.card V : ℝ≥0)⁻¹ ^ H.toLeft.toLeft.card *
        laterTriangleScale W k p H.toLeft.toRight := by
  rw [sourceQuasiWeight_factor, laterTriangleScale_eq_prefix_weight, mul_pow]
  simp only [setWeight, prod_const]
  ring

theorem IsResidualReserveStronglyWellDistributed.sourceLeft_joint_inclusion
    {Ω V : Type*} [Fintype Ω] [Fintype V] [DecidableEq V] {ell : ℕ}
    {L : FiniteLaw Ω} {W : Vortex V ell} {k : Fin (ell+1)} {G : SimpleGraph V}
    {initial later : Ω → TripleSystemOn V} {reserve : Ω → Finset (Sym2 V)} {p r C b : ℝ≥0}
    (h : IsResidualReserveStronglyWellDistributed L W k G initial later reserve p r C b)
    (hdis : L.SupportedOn fun ω ↦ Disjoint (initial ω) (later ω)) (hC : 1 ≤ C)
    (H : Finset (SourceQuasiCoordinate V)) :
    L.probability (fun ω ↦ H ⊆ sourceLeftRealizedCoordinates G (initial ω) (later ω) (reserve ω)) ≤
      (C^2)^H.card * (setWeight (sourceQuasiWeight (fun _ ↦ (Fintype.card V : ℝ≥0)⁻¹)
        (vortexTripleWeight (W.prefix k) p) (p*r)) H + b) := by
  by_cases hcolors : Disjoint H.toLeft.toLeft H.toLeft.toRight
  · by_cases hE : H.toRight ⊆ graphEdges G
    · have hevent : (fun ω ↦ H ⊆ sourceLeftRealizedCoordinates G (initial ω) (later ω) (reserve ω)) =
          ResidualReserveDistributionEvent initial later reserve H.toLeft.toLeft H.toLeft.toRight
            H.toRight H.toRight := by
        funext ω
        apply propext
        simp only [sourceLeft_subset_realized_iff, ResidualReserveDistributionEvent,
          ResidualDistributionEvent, hE, true_and]
        tauto
      rw [hevent, sourceLeft_weight_eq_prescription]
      apply (h H.toLeft.toLeft H.toLeft.toRight H.toRight H.toRight hcolors hE).trans
      apply mul_le_mul_of_nonneg_right _ zero_le
      rw [← pow_mul]
      apply pow_le_pow_right₀ hC
      have h1 := card_toLeft_add_card_toRight (u := H.toLeft)
      have h2 := card_toLeft_add_card_toRight (u := H)
      omega
    · have hz : L.probability (fun ω ↦ H ⊆ sourceLeftRealizedCoordinates G (initial ω) (later ω) (reserve ω)) ≤
          L.probability (fun _ ↦ False) := by
        apply L.probability_mono
        intro ω hω
        exact hE ((sourceLeft_subset_realized_iff G _ _ _ H).mp hω).2.2.1
      rw [L.probability_false] at hz
      exact hz.trans zero_le
  · have hz : L.probability (fun ω ↦ H ⊆ sourceLeftRealizedCoordinates G (initial ω) (later ω) (reserve ω)) ≤
        L.probability (fun _ ↦ False) := by
      apply L.probability_mono_of_supported hdis
      intro ω hd hω
      have hh := (sourceLeft_subset_realized_iff G _ _ _ H).mp hω
      exact hcolors (hd.mono hh.1 hh.2.1)
    rw [L.probability_false] at hz
    exact hz.trans zero_le

end

end Erdos207
