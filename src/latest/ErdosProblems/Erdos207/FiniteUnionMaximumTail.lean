/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.FiniteHypergraphMaximumTail
import ErdosProblems.Erdos207.ForbiddenFamilyDegreeUnion

/-! # Simultaneous maximum-degree tails for finite unions of families -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem finiteHypergraphMaxDegree_biUnion_probability_le
    {Ω V I : Type*} [Fintype Ω] [Fintype V] [DecidableEq V] [DecidableEq I]
    (L : FiniteLaw Ω) (indices : Finset I) (F : I → Ω → Finset (Finset V))
    (K epsilon : I → ℝ≥0)
    (htail : ∀ i ∈ indices, L.probability
      (fun ω ↦ K i ≤ (finiteHypergraphMaxDegree (F i ω) : ℝ≥0)) ≤ epsilon i) :
    L.probability (fun ω ↦ (∑ i ∈ indices, K i) <
      (finiteHypergraphMaxDegree (indices.biUnion (fun i ↦ F i ω)) : ℝ≥0)) ≤
      ∑ i ∈ indices, epsilon i := by
  classical
  have hcover : L.probability (fun ω ↦ (∑ i ∈ indices, K i) <
      (finiteHypergraphMaxDegree (indices.biUnion (fun i ↦ F i ω)) : ℝ≥0)) ≤
      L.probability (fun ω ↦ ∃ i ∈ indices, K i ≤ (finiteHypergraphMaxDegree (F i ω) : ℝ≥0)) := by
    apply L.probability_mono
    intro ω hω
    by_contra hnot
    push Not at hnot
    have hsum : (∑ i ∈ indices, (finiteHypergraphMaxDegree (F i ω) : ℝ≥0)) ≤
        ∑ i ∈ indices, K i := sum_le_sum (fun i hi ↦ (hnot i hi).le)
    have hmax : (finiteHypergraphMaxDegree (indices.biUnion (fun i ↦ F i ω)) : ℝ≥0) ≤
        ∑ i ∈ indices, (finiteHypergraphMaxDegree (F i ω) : ℝ≥0) := by
      exact_mod_cast finiteHypergraphMaxDegree_biUnion_le indices (fun i ↦ F i ω)
    exact (not_lt_of_ge (hmax.trans hsum)) hω
  exact hcover.trans ((L.probability_exists_le indices
    (fun i ω ↦ K i ≤ (finiteHypergraphMaxDegree (F i ω) : ℝ≥0))).trans (sum_le_sum htail))

end

end Erdos207
