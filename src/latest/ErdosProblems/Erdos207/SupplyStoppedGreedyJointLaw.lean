/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.PreliminaryEdgeSupply

/-!
# Stopping the preliminary process at loss of local edge supply

The preliminary process must stop not only when its total available family
is too small, but also when a currently uncovered crossing edge loses its
uniform extension supply.  This module makes that stopping rule part of the
kernel and proves the exact selected/uncovered product estimate with the
terminal failure probability kept as an additive error.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- Active region for the preliminary mixed estimate. -/
def preliminarySupplyActive
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U : Finset V) (D d : ℕ)
    (S : GreedyStateOn V) : Prop :=
  D ≤ S.available.card ∧ HasPreliminaryEdgeSupply G U d S

/-- Ordinary uniform greedy choice while the global floor and every local
uncovered-edge supply hold; otherwise the state is frozen. -/
def supplyStoppedGreedyKernel
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (G : SimpleGraph V) (U : Finset V)
    (D d : ℕ) (S : GreedyStateOn V) : FiniteLaw (GreedyStateOn V) := by
  classical
  exact if preliminarySupplyActive G U D d S then
      greedyKernel F S
    else
      FiniteLaw.pure S

def supplyStoppedGreedyProcessLaw
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (G : SimpleGraph V) (U : Finset V)
    (D d fuel : ℕ) (S : GreedyStateOn V) :
    FiniteLaw (GreedyStateOn V) :=
  FiniteLaw.iterateKernel (supplyStoppedGreedyKernel F G U D d) fuel
    (FiniteLaw.pure S)

/-- Residual crossing edges are tracked only while the full preliminary
active predicate holds. -/
def supplyStoppedTrackedUncoveredEdges
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U : Finset V) (D d : ℕ)
    (S : GreedyStateOn V) : Finset (Sym2 V) := by
  classical
  exact if preliminarySupplyActive G U D d S then
      greedyUncoveredEdges (crossingEdges G U) S
    else
      ∅

theorem supplyStoppedGreedyKernel_monotone_singleInsertion
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (G : SimpleGraph V) (U : Finset V)
    (D d : ℕ) :
    IsMonotoneSingleInsertionKernel
      (supplyStoppedGreedyKernel F G U D d)
      (fun S : GreedyStateOn V ↦ S.chosen) := by
  classical
  intro S
  unfold supplyStoppedGreedyKernel
  split_ifs with hactive
  · exact greedyKernel_monotone_singleInsertion F S
  · exact FiniteLaw.supportedOn_pure _ ⟨Subset.rfl, by simp⟩

theorem supplyStoppedGreedyKernel_antitone_trackedUncovered
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (G : SimpleGraph V) (U : Finset V)
    (D d : ℕ) :
    IsAntitoneSetKernel (supplyStoppedGreedyKernel F G U D d)
      (supplyStoppedTrackedUncoveredEdges G U D d) := by
  classical
  intro S
  by_cases hactive : preliminarySupplyActive G U D d S
  · unfold supplyStoppedGreedyKernel
    rw [if_pos hactive]
    intro S' hmass
    by_cases hnext : preliminarySupplyActive G U D d S'
    · simp only [supplyStoppedTrackedUncoveredEdges,
        if_pos hactive, if_pos hnext]
      exact greedyUncoveredEdges_antitone (crossingEdges G U)
        ((greedyKernel_monotone_singleInsertion F S) S' hmass).1
    · simp [supplyStoppedTrackedUncoveredEdges, hnext]
  · unfold supplyStoppedGreedyKernel
    rw [if_neg hactive]
    intro S' hmass
    have hS' : S' = S := by
      have hpos : 0 < (FiniteLaw.pure S).mass S' := hmass
      simp only [FiniteLaw.pure_mass] at hpos
      by_cases heq : S' = S
      · exact heq
      · simp [heq] at hpos
    subst S'
    exact Subset.rfl

theorem supplyStoppedGreedyKernel_probability_new_triangle_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (G : SimpleGraph V) (U : Finset V)
    (D d : ℕ) (hD : 0 < D)
    (S : GreedyStateOn V) (T : TripleOn V) (hT : T ∉ S.chosen) :
    (supplyStoppedGreedyKernel F G U D d S).probability
        (fun S' ↦ T ∈ S'.chosen) ≤ (D : ℝ≥0)⁻¹ := by
  classical
  unfold supplyStoppedGreedyKernel
  split_ifs with hactive
  · exact greedyKernel_probability_new_triangle_le
      F S T D hD hactive.1 hT
  · rw [FiniteLaw.probability_pure]
    simp [hT]

/-- The local supply built into the active predicate gives the one-step
activity-gated residual contraction. -/
theorem supplyStoppedGreedyKernel_probability_trackedUncovered_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (G : SimpleGraph V) (U : Finset V)
    (D d : ℕ) (hD : 0 < D) (theta : ℝ≥0)
    (hscalar : ∀ S B, preliminarySupplyActive G U D d S →
      B ⊆ greedyUncoveredEdges (crossingEdges G U) S →
      ((S.available.card - B.card * d / 3 : ℕ) : ℝ≥0) *
          (S.available.card : ℝ≥0)⁻¹ ≤ theta ^ B.card)
    (S : GreedyStateOn V) (B : Finset (Sym2 V))
    (hB : B ⊆ supplyStoppedTrackedUncoveredEdges G U D d S) :
    (supplyStoppedGreedyKernel F G U D d S).probability (fun S' ↦
        B ⊆ supplyStoppedTrackedUncoveredEdges G U D d S') ≤
      theta ^ B.card := by
  classical
  by_cases hactive : preliminarySupplyActive G U D d S
  · have hA : S.available.Nonempty :=
      card_pos.mp (lt_of_lt_of_le hD hactive.1)
    have hBactual : B ⊆
        greedyUncoveredEdges (crossingEdges G U) S := by
      simpa [supplyStoppedTrackedUncoveredEdges, hactive] using hB
    unfold supplyStoppedGreedyKernel
    rw [if_pos hactive]
    calc
      (greedyKernel F S).probability (fun S' ↦
          B ⊆ supplyStoppedTrackedUncoveredEdges G U D d S') ≤
          (greedyKernel F S).probability (fun S' ↦
            B ⊆ greedyUncoveredEdges (crossingEdges G U) S') := by
        apply (greedyKernel F S).probability_mono
        intro S' htracked
        by_cases hnext : preliminarySupplyActive G U D d S'
        · simpa [supplyStoppedTrackedUncoveredEdges, hnext] using htracked
        · have hBempty : B = ∅ := by
            apply subset_empty.mp
            simpa [supplyStoppedTrackedUncoveredEdges, hnext] using htracked
          simp [hBempty]
      _ = ((greedySurvivalChoices F (crossingEdges G U) S B).card : ℝ≥0) *
          (S.available.card : ℝ≥0)⁻¹ :=
        greedyKernel_probability_uncovered_eq
          F (crossingEdges G U) S B hA
      _ ≤ theta ^ B.card := by
        apply greedySurvivalChoices_ratio_le_of_edgeSupply
          F (crossingEdges G U) S B hBactual d
        · intro e heB
          exact hactive.2 e (hBactual heB)
        · exact hscalar S B hactive hBactual
  · have hBempty : B = ∅ := by
      apply subset_empty.mp
      simpa [supplyStoppedTrackedUncoveredEdges, hactive] using hB
    subst B
    simp [supplyStoppedGreedyKernel, hactive,
      FiniteLaw.probability_true]

/-- The mixed selected/uncovered product estimate while the global and local
supply conditions remain active. -/
theorem supplyStoppedGreedyProcess_probability_selectedTrackedUncovered_le_product
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (G : SimpleGraph V) (U : Finset V)
    (D d fuel : ℕ) (hD : 0 < D)
    (theta alpha eta : ℝ≥0) (S₀ : GreedyStateOn V)
    (Q : TripleSystemOn V) (B : Finset (Sym2 V))
    (hactive₀ : preliminarySupplyActive G U D d S₀)
    (hQ : Disjoint Q S₀.chosen)
    (hB : B ⊆ greedyUncoveredEdges (crossingEdges G U) S₀)
    (hscalar : ∀ S B, preliminarySupplyActive G U D d S →
      B ⊆ greedyUncoveredEdges (crossingEdges G U) S →
      ((S.available.card - B.card * d / 3 : ℕ) : ℝ≥0) *
          (S.available.card : ℝ≥0)⁻¹ ≤ theta ^ B.card)
    (hselected : (fuel : ℝ≥0) * (D : ℝ≥0)⁻¹ ≤ alpha)
    (hsurvived : theta ^ (fuel - Q.card) ≤ eta) :
    (supplyStoppedGreedyProcessLaw F G U D d fuel S₀).probability
        (fun S ↦ Q ⊆ S.chosen ∧
          B ⊆ supplyStoppedTrackedUncoveredEdges G U D d S) ≤
      alpha ^ Q.card * eta ^ B.card := by
  have hBtracked : B ⊆
      supplyStoppedTrackedUncoveredEdges G U D d S₀ := by
    simpa [supplyStoppedTrackedUncoveredEdges, hactive₀] using hB
  have hraw := iterateKernel_probability_selectedUncovered_le
    (supplyStoppedGreedyKernel F G U D d)
    (fun S : GreedyStateOn V ↦ S.chosen)
    (supplyStoppedTrackedUncoveredEdges G U D d)
    (D : ℝ≥0)⁻¹ theta
    (supplyStoppedGreedyKernel_monotone_singleInsertion F G U D d)
    (supplyStoppedGreedyKernel_antitone_trackedUncovered F G U D d)
    (supplyStoppedGreedyKernel_probability_trackedUncovered_le
      F G U D d hD theta hscalar)
    (fun S T hT B _hB ↦
      ((supplyStoppedGreedyKernel F G U D d S).probability_mono
        (fun _S' h ↦ h.1)).trans
          (supplyStoppedGreedyKernel_probability_new_triangle_le
            F G U D d hD S T hT))
    S₀ Q B hQ hBtracked fuel
  exact hraw.trans (selectedUncoveredEnvelope_le_product
    (D : ℝ≥0)⁻¹ theta alpha eta B.card fuel Q.card
      hselected hsurvived)

/-- Genuine residual edges differ from the tracked residual only on a
terminal state where the preliminary active predicate has failed. -/
theorem supplyStoppedGreedyProcess_probability_selectedUncovered_le_product_add_inactive
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (G : SimpleGraph V) (U : Finset V)
    (D d fuel : ℕ) (hD : 0 < D)
    (theta alpha eta epsilon : ℝ≥0) (S₀ : GreedyStateOn V)
    (Q : TripleSystemOn V) (B : Finset (Sym2 V))
    (hactive₀ : preliminarySupplyActive G U D d S₀)
    (hQ : Disjoint Q S₀.chosen)
    (hB : B ⊆ greedyUncoveredEdges (crossingEdges G U) S₀)
    (hscalar : ∀ S B, preliminarySupplyActive G U D d S →
      B ⊆ greedyUncoveredEdges (crossingEdges G U) S →
      ((S.available.card - B.card * d / 3 : ℕ) : ℝ≥0) *
          (S.available.card : ℝ≥0)⁻¹ ≤ theta ^ B.card)
    (hselected : (fuel : ℝ≥0) * (D : ℝ≥0)⁻¹ ≤ alpha)
    (hsurvived : theta ^ (fuel - Q.card) ≤ eta)
    (hinactive :
      (supplyStoppedGreedyProcessLaw F G U D d fuel S₀).probability
        (fun S ↦ ¬ preliminarySupplyActive G U D d S) ≤ epsilon) :
    (supplyStoppedGreedyProcessLaw F G U D d fuel S₀).probability
        (fun S ↦ Q ⊆ S.chosen ∧
          B ⊆ greedyUncoveredEdges (crossingEdges G U) S) ≤
      alpha ^ Q.card * eta ^ B.card + epsilon := by
  let L := supplyStoppedGreedyProcessLaw F G U D d fuel S₀
  calc
    L.probability (fun S ↦ Q ⊆ S.chosen ∧
        B ⊆ greedyUncoveredEdges (crossingEdges G U) S) ≤
        L.probability (fun S ↦
          (Q ⊆ S.chosen ∧
            B ⊆ supplyStoppedTrackedUncoveredEdges G U D d S) ∨
          ¬ preliminarySupplyActive G U D d S) := by
      apply L.probability_mono
      intro S h
      by_cases hactive : preliminarySupplyActive G U D d S
      · left
        exact ⟨h.1, by
          simpa [supplyStoppedTrackedUncoveredEdges, hactive] using h.2⟩
      · exact Or.inr hactive
    _ ≤ L.probability (fun S ↦
          Q ⊆ S.chosen ∧
            B ⊆ supplyStoppedTrackedUncoveredEdges G U D d S) +
        L.probability (fun S ↦
          ¬ preliminarySupplyActive G U D d S) :=
      L.probability_or_le _ _
    _ ≤ alpha ^ Q.card * eta ^ B.card + epsilon := by
      exact add_le_add
        (supplyStoppedGreedyProcess_probability_selectedTrackedUncovered_le_product
          F G U D d fuel hD theta alpha eta S₀ Q B hactive₀ hQ hB
            hscalar hselected hsurvived)
        hinactive

end

end Erdos207
