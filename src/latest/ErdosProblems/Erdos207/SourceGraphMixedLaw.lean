/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.GraphRestrictedUnionDistribution
import ErdosProblems.Erdos207.SourceNibbleMixedWeights

/-! # The actual mixed selected/residual set of a graph-restricted master law -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

def sourceGraphMixedSelected
    {Ω V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (initial later : Ω → TripleSystemOn V) (ω : Ω) : Finset (SourceNibbleCoordinate V) := by
  classical
  exact (initial ω ∪ later ω).disjSum
    ((graphEdges G).filter (fun e ↦ e ∉ (coveredGraph (initial ω)).edgeSet))

theorem sourceGraphMixedSelected_subset_iff
    {Ω V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (initial later : Ω → TripleSystemOn V) (ω : Ω) (A : Finset (SourceNibbleCoordinate V)) :
    A ⊆ sourceGraphMixedSelected G initial later ω ↔
      A.toLeft ⊆ initial ω ∪ later ω ∧ A.toRight ⊆ graphEdges G ∧
        ∀ e ∈ A.toRight, e ∉ (coveredGraph (initial ω)).edgeSet := by
  classical
  rw [sourceGraphMixedSelected, subset_disjSum]
  constructor
  · intro h
    exact ⟨h.1, fun e he ↦ (mem_filter.mp (h.2 he)).1, fun e he ↦ (mem_filter.mp (h.2 he)).2⟩
  · intro h
    exact ⟨h.1, fun e he ↦ mem_filter.mpr ⟨h.2.1 he, h.2.2 e he⟩⟩

theorem IsGraphStronglyWellDistributed.mixed_joint_inclusion
    {Ω V : Type*} [Fintype Ω] [Fintype V] [DecidableEq V] {ell : ℕ}
    {L : FiniteLaw Ω} {W : Vortex V ell} {k : Fin (ell + 1)} {G : SimpleGraph V}
    {initial later : Ω → TripleSystemOn V} {p C b : ℝ≥0}
    (h : IsGraphStronglyWellDistributed L W k G initial later p C b)
    (hp : p ≤ 1) (hnonempty : ∀ i, (W.U i).Nonempty) (A : Finset (SourceNibbleCoordinate V)) :
    L.probability (fun ω ↦ A ⊆ sourceGraphMixedSelected G initial later ω) ≤
      (2 * C) ^ A.card * (setWeight (sourceNibbleMixedWeight (W.prefix k) 2 p) A + b) := by
  classical
  by_cases hE : A.toRight ⊆ graphEdges G
  · have hmono : L.probability (fun ω ↦ A ⊆ sourceGraphMixedSelected G initial later ω) ≤
        L.probability (fun ω ↦ A.toLeft ⊆ initial ω ∪ later ω ∧
          ∀ e ∈ A.toRight, e ∉ (coveredGraph (initial ω)).edgeSet) := by
      apply L.probability_mono
      intro ω hω
      have hm := (sourceGraphMixedSelected_subset_iff G initial later ω A).mp hω
      exact ⟨hm.1, hm.2.2⟩
    apply hmono.trans
    have hbound := h.probability_union_and_edges_prefix_le hp hnonempty A.toLeft A.toRight hE
    rw [sourceNibbleMixedWeight_factor]
    simpa only [card_toLeft_add_card_toRight, mul_comm] using hbound
  · have hzero : L.probability (fun ω ↦ A ⊆ sourceGraphMixedSelected G initial later ω) ≤
        L.probability (fun _ ↦ False) := by
      apply L.probability_mono
      intro ω hω
      exact hE ((sourceGraphMixedSelected_subset_iff G initial later ω A).mp hω).2.1
    rw [L.probability_false] at hzero
    exact hzero.trans zero_le

theorem IsGraphStronglyWellDistributed.mixed_bounded_joint_inclusion
    {Ω V : Type*} [Fintype Ω] [Fintype V] [DecidableEq V] {ell : ℕ}
    {L : FiniteLaw Ω} {W : Vortex V ell} {k : Fin (ell + 1)} {G : SimpleGraph V}
    {initial later : Ω → TripleSystemOn V} {p C b : ℝ≥0}
    (h : IsGraphStronglyWellDistributed L W k G initial later p C b)
    (hp : p ≤ 1) (hC : 1 ≤ C) (hnonempty : ∀ i, (W.U i).Nonempty)
    (d : ℕ) (A : Finset (SourceNibbleCoordinate V)) (hA : A.card ≤ d) :
    L.probability (fun ω ↦ A ⊆ sourceGraphMixedSelected G initial later ω) ≤
      (2 * C) ^ d * setWeight (sourceNibbleMixedWeight (W.prefix k) 2 p) A + (2 * C) ^ d * b := by
  apply (h.mixed_joint_inclusion hp hnonempty A).trans
  rw [← mul_add]
  apply mul_le_mul_of_nonneg_right _ zero_le
  exact pow_le_pow_right₀ (one_le_mul_of_one_le_of_one_le (by norm_num) hC) hA

end

end Erdos207
