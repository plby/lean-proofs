/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.InitialPairAverage
import ErdosProblems.Erdos207.RegularizationGraphEncoding

/-! # Triangle regularization supplies the pair half of actual initial regularity -/

namespace Erdos207

open Finset

noncomputable section

theorem regularized_pair_initial_bounds
    {V : Type*} [Fintype V] [DecidableEq V]
    (S : GreedyStateOn V) (Q : Finset (Finset V)) (target theta : ℝ)
    (hQ : ∀ P ∈ Q, P.card = 2)
    (hcover : ∀ P : Finset V, P.card = 2 → (availableTrianglesContainingPair S P).Nonempty → P ∈ Q)
    (hQpos : 0 < Q.card) (htarget : 0 < target) (htheta : 0 ≤ theta) (htheta1 : theta ≤ 1 / 2)
    (hdegree : ∀ P ∈ Q, |((availableTrianglesContainingPair S P).card : ℝ) - target| ≤ theta * target) :
    0 < (S.available.card : ℝ) ∧
      target / 6 ≤ (S.available.card : ℝ) / Q.card ∧ (S.available.card : ℝ) / Q.card ≤ target / 2 ∧
      ∀ P ∈ Q, |((availableTrianglesContainingPair S P).card : ℝ) -
        3 * (S.available.card : ℝ) / Q.card| ≤ (4 * theta) * (3 * (S.available.card : ℝ) / Q.card) := by
  have havg := initial_pair_average_interval S Q ((1 + theta) * target) (2 * theta * target)
    hQ hcover hQpos (by
      intro P hP
      have hp := abs_le.mp (hdegree P hP)
      constructor <;> nlinarith only [hp.1, hp.2])
  have hthetaTarget : theta * target ≤ target / 2 := by
    nlinarith only [mul_le_mul_of_nonneg_right htheta1 htarget.le]
  have hmeanLower : target / 2 ≤ 3 * (S.available.card : ℝ) / Q.card := by
    nlinarith only [havg.1.1, hthetaTarget]
  have hmeanUpper : 3 * (S.available.card : ℝ) / Q.card ≤ 3 * target / 2 := by
    nlinarith only [havg.1.2, hthetaTarget]
  have hid : 3 * (S.available.card : ℝ) / Q.card = 3 * ((S.available.card : ℝ) / Q.card) := by ring
  have hratio : target / 6 ≤ (S.available.card : ℝ) / Q.card ∧ (S.available.card : ℝ) / Q.card ≤ target / 2 := by
    rw [hid] at hmeanLower hmeanUpper
    constructor <;> linarith only [hmeanLower, hmeanUpper]
  have hA : 0 < (S.available.card : ℝ) := by
    by_contra h
    have hz : (S.available.card : ℝ) = 0 := le_antisymm (not_lt.mp h) (Nat.cast_nonneg _)
    rw [hz, mul_zero, zero_div] at hmeanLower
    linarith only [hmeanLower, htarget]
  refine ⟨hA, hratio.1, hratio.2, fun P hP ↦ ?_⟩
  have htargetMean : target ≤ 2 * (3 * (S.available.card : ℝ) / Q.card) := by linarith only [hmeanLower]
  have hmul := mul_le_mul_of_nonneg_left htargetMean (show 0 ≤ 2 * theta by positivity)
  exact (havg.2 P hP).trans (by nlinarith only [hmul])

theorem graphPairFamily_covers_available
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (S : GreedyStateOn V) (hA : ∀ T ∈ S.available, tripleEdgeFinset T ⊆ graphEdges G)
    (P : Finset V) (hP : P.card = 2) (hstar : (availableTrianglesContainingPair S P).Nonempty) :
    P ∈ graphPairFamily G := by
  obtain ⟨T, hT⟩ := hstar
  have hm := mem_availableTrianglesContainingPair_iff.mp hT
  exact graphPairFamily_contains_triangle_pairs G S.available hA T.1
    ((mem_triangleVertexFamily_val_iff S.available T).2 hm.1) (mem_powersetCard.mpr ⟨hm.2, hP⟩)

theorem regularized_graph_pair_initial_bounds
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (S : GreedyStateOn V) (target theta : ℝ)
    (hA : ∀ T ∈ S.available, tripleEdgeFinset T ⊆ graphEdges G)
    (hEpos : 0 < (graphEdges G).card) (htarget : 0 < target) (htheta : 0 ≤ theta) (htheta1 : theta ≤ 1 / 2)
    (hdegree : ∀ e ∈ graphEdges G, |((S.available.filter fun T ↦ e ∈ tripleEdgeFinset T).card : ℝ) - target| ≤ theta * target) :
    0 < (S.available.card : ℝ) ∧
      target / 6 ≤ (S.available.card : ℝ) / (graphEdges G).card ∧
      (S.available.card : ℝ) / (graphEdges G).card ≤ target / 2 ∧
      ∀ P ∈ graphPairFamily G, |((availableTrianglesContainingPair S P).card : ℝ) -
        3 * (S.available.card : ℝ) / (graphEdges G).card| ≤
          (4 * theta) * (3 * (S.available.card : ℝ) / (graphEdges G).card) := by
  have h := regularized_pair_initial_bounds S (graphPairFamily G) target theta (graphPairFamily_uniform G)
    (graphPairFamily_covers_available G S hA) (by simpa only [graphPairFamily_card] using hEpos)
    htarget htheta htheta1 (by
      intro P hP
      obtain ⟨e, he, rfl⟩ := mem_image.mp hP
      change |((S.available.filter fun T ↦ e.toFinset ⊆ T.1).card : ℝ) - target| ≤ theta * target
      rw [← triangleVertexFamily_incident_card, triangleVertexFamily_edge_card S.available e
        (G.not_isDiag_of_mem_edgeSet (mem_graphEdges_iff.mp he))]
      exact hdegree e he)
  simpa only [graphPairFamily_card] using h

end

end Erdos207
