/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.InternalEdgeResidualError
import ErdosProblems.Erdos207.JointInclusionFactorialTail
import ErdosProblems.Erdos207.OuterOnlyResidualDegree
import ErdosProblems.Erdos207.SupportedGraphDegreeSum

/-! # Preliminary leftover stars: fixed moments with the actual support size -/

namespace Erdos207

open Finset
open scoped Classical NNReal

noncomputable section

theorem IsGraphMixedProductBound.residual_test_tail
    {Ω V : Type*} [Fintype Ω] [Fintype V] [DecidableEq V]
    {L : FiniteLaw Ω} {selected : Ω → TripleSystemOn V} {G : SimpleGraph V}
    {survival point C error : ℝ≥0}
    (h : IsGraphMixedProductBound L selected G survival point C error)
    (U : Finset V) (S : Finset (Sym2 V)) (s D : ℕ) (hD : 0 < D) (hs : 2 * s ≤ D) :
    L.probability (fun omega ↦ D ≤ (S ∩ preliminaryResidualOuterEdges G U (selected omega)).card) ≤
      (2 * (S.card : ℝ≥0) * C * survival / D) ^ s + (2 * (S.card : ℝ≥0) * C / D) ^ s * error := by
  have hb := L.probability_card_inter_ge_le_powerMoment
    (fun omega ↦ preliminaryResidualOuterEdges G U (selected omega)) S s D
    ((C * survival) ^ s + C ^ s * error) hD hs (fun E hE ↦ by
      have hcard := (mem_powersetCard.mp hE).2
      simpa only [empty_subset, true_and, card_empty, pow_zero, one_mul, zero_add, hcard]
        using h.preliminaryResidualOuter_le U ∅ E)
  apply hb.trans_eq
  simp only [mul_add, mul_pow, div_pow]
  ring

def PreliminaryResidualDegreeGood
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U : Finset V) (selected : TripleSystemOn V) (d : ℕ) : Prop :=
  ∀ v : V, (scheduledEdgesAt (graphEdges G) v ∩ preliminaryResidualOuterEdges G U selected).card ≤ d

theorem card_scheduledGraphStar_le_support
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (current : Finset V) (hsupp : GraphSupportedOn G (current : Set V)) (v : V) :
    (scheduledEdgesAt (graphEdges G) v).card ≤ current.card := by
  let _ : DecidableRel G.Adj := Classical.decRel _
  rw [card_scheduledEdgesAt_graphEdges, ← SimpleGraph.card_neighborFinset_eq_degree,
    ← neighborsIn_eq_neighborFinset_of_supported G current hsupp v]
  exact card_le_card (filter_subset _ _)

theorem IsGraphMixedProductBound.preliminary_degree_failure_le
    {Ω V : Type*} [Fintype Ω] [Fintype V] [DecidableEq V]
    {L : FiniteLaw Ω} {selected : Ω → TripleSystemOn V} {G : SimpleGraph V}
    {survival point C error : ℝ≥0}
    (h : IsGraphMixedProductBound L selected G survival point C error)
    (current U : Finset V) (hsupp : GraphSupportedOn G (current : Set V))
    (s d : ℕ) (hs : 2 * s ≤ d + 1) :
    L.probability (fun omega ↦ ¬ PreliminaryResidualDegreeGood G U (selected omega) d) ≤
      (Fintype.card V : ℝ≥0) * ((2 * (current.card : ℝ≥0) * C * survival / (d + 1)) ^ s +
        (2 * (current.card : ℝ≥0) * C / (d + 1)) ^ s * error) := by
  let Bad := fun v omega ↦ d + 1 ≤
    (scheduledEdgesAt (graphEdges G) v ∩ preliminaryResidualOuterEdges G U (selected omega)).card
  have hbad : ∀ v : V, L.probability (Bad v) ≤
      (2 * (current.card : ℝ≥0) * C * survival / (d + 1)) ^ s + (2 * (current.card : ℝ≥0) * C / (d + 1)) ^ s * error := by
    intro v
    have hb := h.residual_test_tail U (scheduledEdgesAt (graphEdges G) v) s (d + 1) (by omega) hs
    simp only [Nat.cast_add, Nat.cast_one] at hb
    have hc : ((scheduledEdgesAt (graphEdges G) v).card : ℝ≥0) ≤ current.card := by
      exact_mod_cast card_scheduledGraphStar_le_support G current hsupp v
    apply hb.trans
    gcongr
  calc
    _ ≤ L.probability (fun omega ↦ ∃ v ∈ (univ : Finset V), Bad v omega) := by
      apply L.probability_mono
      intro omega hnot
      by_contra hnone
      apply hnot
      intro v
      have : ¬ Bad v omega := fun hv ↦ hnone ⟨v, mem_univ _, hv⟩
      dsimp only [Bad] at this
      omega
    _ ≤ ∑ v : V, L.probability (Bad v) := L.probability_exists_le univ Bad
    _ ≤ ∑ _v : V, ((2 * (current.card : ℝ≥0) * C * survival / (d + 1)) ^ s +
        (2 * (current.card : ℝ≥0) * C / (d + 1)) ^ s * error) := sum_le_sum (fun v _ ↦ hbad v)
    _ = _ := by simp only [sum_const, card_univ, nsmul_eq_mul]

end

end Erdos207
