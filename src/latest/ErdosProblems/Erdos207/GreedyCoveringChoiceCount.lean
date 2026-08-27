/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.StoppedGreedyUncoveredSurvival

/-!
# Counting greedy choices which cover prescribed edges

Every available triangle contains exactly three graph edges.  Double
counting incidences between a prescribed edge family and the available
triangles therefore converts a uniform per-edge candidate supply into a
lower bound for the number of choices which hit at least one prescribed
edge.  This is the finite counting input to the survival factor in (8.7).
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- Available triangles containing one fixed graph edge. -/
def greedyChoicesCoveringEdge
    {V : Type*} [Fintype V] [DecidableEq V]
    (S : GreedyStateOn V) (e : Sym2 V) : Finset S.available := by
  classical
  exact Finset.univ.filter fun T ↦ e ∈ tripleEdgeFinset T.1

lemma card_greedyChoicesCoveringEdge_eq_sum
    {V : Type*} [Fintype V] [DecidableEq V]
    (S : GreedyStateOn V) (e : Sym2 V) :
    (greedyChoicesCoveringEdge S e).card =
      ∑ T : S.available, if e ∈ tripleEdgeFinset T.1 then 1 else 0 := by
  classical
  simp [greedyChoicesCoveringEdge]

lemma sum_card_greedyChoicesCoveringEdge_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (S : GreedyStateOn V) (B : Finset (Sym2 V)) :
    ∑ e ∈ B, (greedyChoicesCoveringEdge S e).card =
      ∑ T : S.available,
        (B.filter fun e ↦ e ∈ tripleEdgeFinset T.1).card := by
  classical
  simp_rw [card_greedyChoicesCoveringEdge_eq_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro T _hT
  rw [← Finset.sum_filter]
  simp [Finset.filter_mem_eq_inter]

lemma filtered_prescribedEdges_card_le_three
    {V : Type*} [Fintype V] [DecidableEq V]
    (B : Finset (Sym2 V)) (T : TripleOn V) :
    (B.filter fun e ↦ e ∈ tripleEdgeFinset T).card ≤ 3 := by
  calc
    (B.filter fun e ↦ e ∈ tripleEdgeFinset T).card ≤
        (tripleEdgeFinset T).card := by
      apply card_le_card
      intro e he
      exact (mem_filter.mp he).2
    _ = 3 := card_tripleEdgeFinset T

lemma filtered_prescribedEdges_eq_empty_of_not_covering
    {V : Type*} [Fintype V] [DecidableEq V]
    (B : Finset (Sym2 V)) (T : TripleOn V)
    (hT : Disjoint B (tripleEdgeFinset T)) :
    B.filter (fun e ↦ e ∈ tripleEdgeFinset T) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro e he
  exact disjoint_left.mp hT (mem_filter.mp he).1 (mem_filter.mp he).2

/-- Each hitting triangle is charged at most three times in the edge-choice
incidence sum. -/
theorem sum_card_greedyChoicesCoveringEdge_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (S : GreedyStateOn V) (B : Finset (Sym2 V)) :
    ∑ e ∈ B, (greedyChoicesCoveringEdge S e).card ≤
      3 * (greedyCoveringChoices S B).card := by
  classical
  rw [sum_card_greedyChoicesCoveringEdge_eq]
  calc
    (∑ T : S.available,
        (B.filter fun e ↦ e ∈ tripleEdgeFinset T.1).card) ≤
        ∑ T : S.available,
          if T ∈ greedyCoveringChoices S B then 3 else 0 := by
      apply Finset.sum_le_sum
      intro T _hT
      by_cases hcover : T ∈ greedyCoveringChoices S B
      · rw [if_pos hcover]
        exact filtered_prescribedEdges_card_le_three B T.1
      · rw [if_neg hcover]
        have hdisj : Disjoint B (tripleEdgeFinset T.1) := by
          simpa [greedyCoveringChoices] using hcover
        rw [filtered_prescribedEdges_eq_empty_of_not_covering B T.1 hdisj]
        simp
    _ = 3 * (greedyCoveringChoices S B).card := by
      have hsum :
          (∑ T : S.available,
              if ¬ Disjoint B (tripleEdgeFinset T.1) then 3 else 0) =
            3 * (greedyCoveringChoices S B).card := by
        rw [← Finset.sum_filter]
        simp [greedyCoveringChoices, Finset.sum_const,
          nsmul_eq_mul, mul_comm]
      simpa [greedyCoveringChoices] using hsum

/-- Uniform supply `d` through every prescribed edge yields at least
`|B| d / 3` available triangles which cover some prescribed edge. -/
theorem card_mul_div_three_le_greedyCoveringChoices
    {V : Type*} [Fintype V] [DecidableEq V]
    (S : GreedyStateOn V) (B : Finset (Sym2 V)) (d : ℕ)
    (hsupply : ∀ e ∈ B, d ≤ (greedyChoicesCoveringEdge S e).card) :
    B.card * d / 3 ≤ (greedyCoveringChoices S B).card := by
  have hlower : B.card * d ≤
      ∑ e ∈ B, (greedyChoicesCoveringEdge S e).card := by
    calc
      B.card * d = ∑ _e ∈ B, d := by simp [mul_comm]
      _ ≤ ∑ e ∈ B, (greedyChoicesCoveringEdge S e).card := by
        apply sum_le_sum
        intro e he
        exact hsupply e he
  have hthree : B.card * d ≤
      3 * (greedyCoveringChoices S B).card :=
    hlower.trans (sum_card_greedyChoicesCoveringEdge_le S B)
  exact Nat.div_le_of_le_mul hthree

/-- A uniform supply through every prescribed edge gives the stopped
one-step survival estimate once the corresponding scalar estimate is
verified.  The loss is rounded down only once, after double counting the
edge--triangle incidences. -/
theorem greedySurvivalChoices_ratio_le_of_edgeSupply
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (E : Finset (Sym2 V))
    (S : GreedyStateOn V) (B : Finset (Sym2 V))
    (hB : B ⊆ greedyUncoveredEdges E S) (d : ℕ)
    (hsupply : ∀ e ∈ B, d ≤ (greedyChoicesCoveringEdge S e).card)
    (theta : ℝ≥0)
    (hscalar :
      ((S.available.card - B.card * d / 3 : ℕ) : ℝ≥0) *
          (S.available.card : ℝ≥0)⁻¹ ≤ theta ^ B.card) :
    ((greedySurvivalChoices F E S B).card : ℝ≥0) *
        (S.available.card : ℝ≥0)⁻¹ ≤ theta ^ B.card := by
  apply greedySurvivalChoices_ratio_le_of_covering
    F E S B hB (B.card * d / 3)
  · exact card_mul_div_three_le_greedyCoveringChoices S B d hsupply
  · exact hscalar

/-- Per-edge supply, uniformly over all active states, is enough for the
one-step activity-gated residual estimate. -/
theorem stoppedGreedyKernel_probability_trackedUncovered_le_of_edgeSupply
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (D : ℕ) (hD : 0 < D)
    (E : Finset (Sym2 V)) (d : ℕ) (theta : ℝ≥0)
    (hsupply : ∀ S B, D ≤ S.available.card →
      B ⊆ greedyUncoveredEdges E S →
      ∀ e ∈ B, d ≤ (greedyChoicesCoveringEdge S e).card)
    (hscalar : ∀ S B, D ≤ S.available.card →
      B ⊆ greedyUncoveredEdges E S →
      ((S.available.card - B.card * d / 3 : ℕ) : ℝ≥0) *
          (S.available.card : ℝ≥0)⁻¹ ≤ theta ^ B.card)
    (S : GreedyStateOn V) (B : Finset (Sym2 V))
    (hB : B ⊆ stoppedGreedyTrackedUncoveredEdges D E S) :
    (stoppedGreedyKernel F D S).probability (fun S' ↦
        B ⊆ stoppedGreedyTrackedUncoveredEdges D E S') ≤
      theta ^ B.card := by
  apply stoppedGreedyKernel_probability_trackedUncovered_le
    F D hD E theta
  intro S' B' hactive hB'
  exact greedySurvivalChoices_ratio_le_of_edgeSupply
    F E S' B' hB' d (hsupply S' B' hactive hB') theta
      (hscalar S' B' hactive hB')
  exact hB

/-- Product-form mixed estimate for a stopped greedy trajectory, expressed
only in terms of the uniform supply through each prescribed uncovered
edge. -/
theorem stoppedGreedyProcess_probability_selectedTrackedUncovered_le_product_of_edgeSupply
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (D fuel : ℕ) (hD : 0 < D)
    (d : ℕ) (theta alpha eta : ℝ≥0) (E : Finset (Sym2 V))
    (S₀ : GreedyStateOn V) (Q : TripleSystemOn V)
    (B : Finset (Sym2 V))
    (hactive₀ : D ≤ S₀.available.card)
    (hQ : Disjoint Q S₀.chosen)
    (hB : B ⊆ greedyUncoveredEdges E S₀)
    (hsupply : ∀ S B, D ≤ S.available.card →
      B ⊆ greedyUncoveredEdges E S →
      ∀ e ∈ B, d ≤ (greedyChoicesCoveringEdge S e).card)
    (hscalar : ∀ S B, D ≤ S.available.card →
      B ⊆ greedyUncoveredEdges E S →
      ((S.available.card - B.card * d / 3 : ℕ) : ℝ≥0) *
          (S.available.card : ℝ≥0)⁻¹ ≤ theta ^ B.card)
    (hselected : (fuel : ℝ≥0) * (D : ℝ≥0)⁻¹ ≤ alpha)
    (hsurvived : theta ^ (fuel - Q.card) ≤ eta) :
    (stoppedGreedyProcessLaw F D fuel S₀).probability (fun S ↦
        Q ⊆ S.chosen ∧
          B ⊆ stoppedGreedyTrackedUncoveredEdges D E S) ≤
      alpha ^ Q.card * eta ^ B.card := by
  apply stoppedGreedyProcess_probability_selectedTrackedUncovered_le_product
    F D fuel hD theta alpha eta E S₀ Q B hactive₀ hQ hB
  · intro S' B' hactive hB'
    exact greedySurvivalChoices_ratio_le_of_edgeSupply
      F E S' B' hB' d (hsupply S' B' hactive hB') theta
        (hscalar S' B' hactive hB')
  · exact hselected
  · exact hsurvived

/-- Full mixed selected/uncovered estimate from uniform per-edge supply.
The only remaining probabilistic input is the separately controlled chance
that the stopped process drops below its availability floor. -/
theorem stoppedGreedyProcess_probability_selectedUncovered_le_product_add_inactive_of_edgeSupply
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (D fuel : ℕ) (hD : 0 < D)
    (d : ℕ) (theta alpha eta epsilon : ℝ≥0)
    (E : Finset (Sym2 V)) (S₀ : GreedyStateOn V)
    (Q : TripleSystemOn V) (B : Finset (Sym2 V))
    (hactive₀ : D ≤ S₀.available.card)
    (hQ : Disjoint Q S₀.chosen)
    (hB : B ⊆ greedyUncoveredEdges E S₀)
    (hsupply : ∀ S B, D ≤ S.available.card →
      B ⊆ greedyUncoveredEdges E S →
      ∀ e ∈ B, d ≤ (greedyChoicesCoveringEdge S e).card)
    (hscalar : ∀ S B, D ≤ S.available.card →
      B ⊆ greedyUncoveredEdges E S →
      ((S.available.card - B.card * d / 3 : ℕ) : ℝ≥0) *
          (S.available.card : ℝ≥0)⁻¹ ≤ theta ^ B.card)
    (hselected : (fuel : ℝ≥0) * (D : ℝ≥0)⁻¹ ≤ alpha)
    (hsurvived : theta ^ (fuel - Q.card) ≤ eta)
    (hinactive :
      (stoppedGreedyProcessLaw F D fuel S₀).probability (fun S ↦
        ¬ D ≤ S.available.card) ≤ epsilon) :
    (stoppedGreedyProcessLaw F D fuel S₀).probability (fun S ↦
        Q ⊆ S.chosen ∧ B ⊆ greedyUncoveredEdges E S) ≤
      alpha ^ Q.card * eta ^ B.card + epsilon := by
  apply stoppedGreedyProcess_probability_selectedUncovered_le_product_add_inactive
    F D fuel hD theta alpha eta epsilon E S₀ Q B hactive₀ hQ hB
  · intro S' B' hactive hB'
    exact greedySurvivalChoices_ratio_le_of_edgeSupply
      F E S' B' hB' d (hsupply S' B' hactive hB') theta
        (hscalar S' B' hactive hB')
  · exact hselected
  · exact hsurvived
  · exact hinactive

end

end Erdos207
