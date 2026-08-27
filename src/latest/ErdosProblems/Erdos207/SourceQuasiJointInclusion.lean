/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceQuasiWeight
import ErdosProblems.Erdos207.ResidualFutureDistribution
import ErdosProblems.Erdos207.SourceLinkRealizedCoordinates

/-! # The actual two-colour/residual-edge probability law -/

namespace Erdos207

open Finset
open scoped Classical NNReal

noncomputable section

def sourceQuasiRealizedCoordinates
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (I D : TripleSystemOn V) : Finset (SourceQuasiCoordinate V) :=
  (I.disjSum D).disjSum ((graphEdges G).filter fun e ↦ e ∉ (coveredGraph (I ∪ D)).edgeSet)

theorem sourceQuasi_subset_realized_iff
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (I D : TripleSystemOn V) (H : Finset (SourceQuasiCoordinate V)) :
    H ⊆ sourceQuasiRealizedCoordinates G I D ↔
      H.toLeft.toLeft ⊆ I ∧ H.toLeft.toRight ⊆ D ∧ H.toRight ⊆ graphEdges G ∧
        ∀ e ∈ H.toRight, e ∉ (coveredGraph (I ∪ D)).edgeSet := by
  simp only [sourceQuasiRealizedCoordinates, subset_disjSum]
  constructor
  · rintro ⟨⟨hI, hD⟩, hE⟩
    exact ⟨hI, hD, fun e he ↦ (mem_filter.mp (hE he)).1,
      fun e he ↦ (mem_filter.mp (hE he)).2⟩
  · rintro ⟨hI, hD, hG, hE⟩
    exact ⟨⟨hI, hD⟩, fun e he ↦ mem_filter.mpr ⟨hG he, hE e he⟩⟩

theorem sourceQuasi_weight_eq_prescription
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (k : Fin (ell + 1)) (p : ℝ≥0)
    (H : Finset (SourceQuasiCoordinate V)) :
    setWeight (sourceQuasiWeight (fun _ ↦ (Fintype.card V : ℝ≥0)⁻¹)
      (vortexTripleWeight (W.prefix k) p) p) H =
      p ^ H.toRight.card * (Fintype.card V : ℝ≥0)⁻¹ ^ H.toLeft.toLeft.card *
        laterTriangleScale W k p H.toLeft.toRight := by
  rw [sourceQuasiWeight_factor, laterTriangleScale_eq_prefix_weight]
  simp only [setWeight, prod_const]
  ring

theorem IsResidualGraphStronglyWellDistributed.sourceQuasi_joint_inclusion
    {Ω V : Type*} [Fintype Ω] [Fintype V] [DecidableEq V] {ell : ℕ}
    {L : FiniteLaw Ω} {W : Vortex V ell} {k : Fin (ell + 1)} {G : SimpleGraph V}
    {initial later : Ω → TripleSystemOn V} {p C b : ℝ≥0}
    (h : IsResidualGraphStronglyWellDistributed L W k G initial later p C b)
    (hdis : L.SupportedOn fun ω ↦ Disjoint (initial ω) (later ω))
    (H : Finset (SourceQuasiCoordinate V)) :
    L.probability (fun ω ↦ H ⊆ sourceQuasiRealizedCoordinates G (initial ω) (later ω)) ≤
      C ^ H.card * (setWeight (sourceQuasiWeight (fun _ ↦ (Fintype.card V : ℝ≥0)⁻¹)
        (vortexTripleWeight (W.prefix k) p) p) H + b) := by
  by_cases hcolors : Disjoint H.toLeft.toLeft H.toLeft.toRight
  · by_cases hE : H.toRight ⊆ graphEdges G
    · have hevent : (fun ω ↦ H ⊆ sourceQuasiRealizedCoordinates G (initial ω) (later ω)) =
          ResidualDistributionEvent initial later H.toLeft.toLeft H.toLeft.toRight H.toRight := by
        funext ω
        apply propext
        simp only [sourceQuasi_subset_realized_iff, ResidualDistributionEvent, hE, true_and]
      rw [hevent, sourceQuasi_weight_eq_prescription]
      have hcard : H.toLeft.toLeft.card + H.toLeft.toRight.card + H.toRight.card = H.card := by
        rw [card_toLeft_add_card_toRight, card_toLeft_add_card_toRight]
      simpa only [hcard] using h H.toLeft.toLeft H.toLeft.toRight H.toRight hcolors hE
    · have hz : L.probability (fun ω ↦ H ⊆ sourceQuasiRealizedCoordinates G (initial ω) (later ω)) ≤
          L.probability (fun _ ↦ False) := by
        apply L.probability_mono
        intro ω hω
        exact hE ((sourceQuasi_subset_realized_iff G _ _ H).mp hω).2.2.1
      rw [L.probability_false] at hz
      exact hz.trans zero_le
  · have hz : L.probability (fun ω ↦ H ⊆ sourceQuasiRealizedCoordinates G (initial ω) (later ω)) ≤
        L.probability (fun _ ↦ False) := by
      apply L.probability_mono_of_supported hdis
      intro ω hd hω
      have hh := (sourceQuasi_subset_realized_iff G _ _ H).mp hω
      exact hcolors (hd.mono hh.1 hh.2.1)
    rw [L.probability_false] at hz
    exact hz.trans zero_le

end

end Erdos207
