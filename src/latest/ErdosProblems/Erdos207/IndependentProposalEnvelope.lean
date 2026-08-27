/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.CoupledEnvelopeProcess
import ErdosProblems.Erdos207.BatchKernelJointInclusion

/-! # Joint-inclusion bounds for the state-independent proposal envelope -/

namespace Erdos207.FiniteLaw

open Finset
open scoped NNReal

noncomputable section

def independentProposalLaw
    {I : Type*} [Fintype I] [DecidableEq I]
    (p : I → ℝ≥0) (hp : ∀ i, p i ≤ 1) : FiniteLaw (Finset I) :=
  map selectedByBits (independentBits p hp)

theorem independentProposalLaw_probability_subset
    {I : Type*} [Fintype I] [DecidableEq I]
    (p : I → ℝ≥0) (hp : ∀ i, p i ≤ 1) (U : Finset I) :
    (independentProposalLaw p hp).probability (fun B ↦ U ⊆ B) = setWeight p U := by
  rw [independentProposalLaw, probability_map, independentBits_probability_subset_selected]
  rfl

theorem proposalUnionKernel_joint_new_le
    {I : Type*} [Fintype I] [DecidableEq I]
    (p : I → ℝ≥0) (hp : ∀ i, p i ≤ 1) (R U : Finset I) (hdis : Disjoint U R) :
    (proposalUnionKernel (independentProposalLaw p hp) R).probability (fun B ↦ U ⊆ B) ≤
      setWeight p U := by
  rw [proposalUnionKernel, probability_map, ← independentProposalLaw_probability_subset p hp U]
  apply probability_mono
  intro B hU i hi
  rcases mem_union.mp (hU hi) with hR | hB
  · exact (disjoint_left.mp hdis hi hR).elim
  · exact hB

theorem independentProposalEnvelope_joint_inclusion
    {I : Type*} [Fintype I] [DecidableEq I]
    (p : ℕ → I → ℝ≥0) (hp : ∀ t i, p t i ≤ 1) (t : ℕ) (U : Finset I) :
    (evolveKernels (fun n ↦ proposalUnionKernel (independentProposalLaw (p n) (hp n)))
      t (pure ∅)).probability (fun R ↦ U ⊆ R) ≤
      setWeight (cumulativePointHazard p t) U := by
  exact evolveKernels_batch_joint_inclusion
    (fun n ↦ proposalUnionKernel (independentProposalLaw (p n) (hp n))) id p
    (fun n R U hdis ↦ proposalUnionKernel_joint_new_le (p n) (hp n) R U hdis)
    ∅ rfl t U

theorem independentProposalEnvelope_joint_inclusion_uniform
    {I : Type*} [Fintype I] [DecidableEq I]
    (p : ℕ → I → ℝ≥0) (hp : ∀ t i, p t i ≤ 1) (t : ℕ) (a : ℝ≥0)
    (ha : ∀ i, ∑ n ∈ range t, p n i ≤ a) (U : Finset I) :
    (evolveKernels (fun n ↦ proposalUnionKernel (independentProposalLaw (p n) (hp n)))
      t (pure ∅)).probability (fun R ↦ U ⊆ R) ≤ a ^ U.card := by
  apply (independentProposalEnvelope_joint_inclusion p hp t U).trans
  change (∏ i ∈ U, ∑ n ∈ range t, p n i) ≤ a ^ U.card
  rw [← prod_const]
  exact prod_le_prod' (fun i _ ↦ ha i)

end

end Erdos207.FiniteLaw
