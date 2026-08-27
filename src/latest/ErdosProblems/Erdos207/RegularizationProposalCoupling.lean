/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.IndependentProposalEnvelope
import ErdosProblems.Erdos207.RegularizationJointInclusion

/-! # Independent geometric proposals for the actual stopped regularizer -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

def geometricProposalProbability (beta : ℝ≥0) (t : ℕ) : ℝ≥0 :=
  min 1 (beta / (2 : ℝ≥0) ^ t)

theorem geometricProposalProbability_le_one (beta : ℝ≥0) (t : ℕ) :
    geometricProposalProbability beta t ≤ 1 := min_le_left _ _

theorem cumulative_geometricProposalProbability_le (beta : ℝ≥0) (t : ℕ) :
    ∑ n ∈ range t, geometricProposalProbability beta n ≤ 2 * beta := by
  calc
    _ ≤ ∑ n ∈ range t, beta / (2 : ℝ≥0) ^ n :=
      sum_le_sum (fun n _ ↦ min_le_right _ _)
    _ = beta * ∑ n ∈ range t, ((2 : ℝ≥0) ^ n)⁻¹ := by
      simp only [div_eq_mul_inv, mul_sum]
    _ ≤ beta * 2 := mul_le_mul_of_nonneg_left (sum_inv_two_pow_le_two t) zero_le
    _ = _ := mul_comm _ _

def regularizationSamplingProbability
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] {k : ℕ}
    (G0 H0 : Finset (Finset V)) (b t : ℕ) (S : HypergraphRegularizationState V k)
    (E : UniformHyperedge V k) : ℝ≥0 := by
  classical
  exact if RegularizationActive G0 H0 b t S then
    uniformEdgeProbability (finiteHypergraphRegularizationWeight (regularizationCurrentFamily G0 S)) k E.1
  else 0

def regularizationSamplingUpdate
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] {k : ℕ}
    (G0 H0 : Finset (Finset V)) (b t : ℕ) (S : HypergraphRegularizationState V k)
    (x : UniformHyperedge V k → Bool) : HypergraphRegularizationState V k := by
  classical
  exact if RegularizationActive G0 H0 b t S then
    regularizationBatchOutcome (regularizationCurrentFamily G0 S) (regularizationCurrentFamily H0 S) S x
  else S

theorem regularizationSamplingProbability_le_proposal
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] {k : ℕ}
    (G0 H0 : Finset (Finset V)) (hGH : G0 ⊆ H0) (hk : 2 ≤ k)
    (hsize : 16 * 2 ^ (k - 1) * (k - 1) ≤ Fintype.card V)
    (beta : ℝ≥0) (hbeta : regularizationBaseHazard G0 k ≤ beta)
    (b t : ℕ) (S : HypergraphRegularizationState V k) (E : UniformHyperedge V k) :
    regularizationSamplingProbability G0 H0 b t S E ≤ geometricProposalProbability beta t := by
  classical
  unfold regularizationSamplingProbability
  split_ifs with hA
  · apply le_min
    · exact (hypergraphRegularizationParameters (regularizationCurrentFamily G0 S)
        (regularizationCurrentFamily H0 S) (regularizationCurrentFamily_mono_base hGH S)
        hk (Nat.zero_lt_of_lt hA.2.1) hsize hA.2.2.2).probability_le_one E
    · exact (hA.edge_probability_le hk E).trans
        (div_le_div_of_nonneg_right hbeta zero_le)
  · exact zero_le

theorem regularizationSamplingUpdate_added_subset
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] {k : ℕ}
    (G0 H0 : Finset (Finset V)) (b t : ℕ) (S : HypergraphRegularizationState V k)
    (x : UniformHyperedge V k → Bool) :
    (regularizationSamplingUpdate G0 H0 b t S x).1 ⊆ S.1 ∪ FiniteLaw.selectedByBits x := by
  classical
  unfold regularizationSamplingUpdate
  split_ifs
  · exact regularizationBatchOutcome_added_subset _ _ S x
  · exact subset_union_left

theorem regularizationKernel_eq_sampling_update
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] {k : ℕ}
    (G0 H0 : Finset (Finset V)) (hGH : G0 ⊆ H0) (hk : 2 ≤ k)
    (hsize : 16 * 2 ^ (k - 1) * (k - 1) ≤ Fintype.card V)
    (b t : ℕ) (S : HypergraphRegularizationState V k)
    (hp : ∀ E, regularizationSamplingProbability G0 H0 b t S E ≤ 1) :
    regularizationKernel G0 H0 hGH hk hsize b t S =
      FiniteLaw.map (regularizationSamplingUpdate G0 H0 b t S)
        (FiniteLaw.independentBits (regularizationSamplingProbability G0 H0 b t S) hp) := by
  classical
  by_cases hA : RegularizationActive G0 H0 b t S
  · rw [regularizationKernel_active G0 H0 hGH hk hsize b t S hA]
    have hu : regularizationSamplingUpdate G0 H0 b t S =
        regularizationBatchOutcome (regularizationCurrentFamily G0 S) (regularizationCurrentFamily H0 S) S := by
      funext x
      exact if_pos hA
    rw [hu]
    apply congrArg (FiniteLaw.map _)
    apply FiniteLaw.ext
    intro x
    change (∏ E, FiniteLaw.bernoulliBitMass
        (uniformEdgeProbability (finiteHypergraphRegularizationWeight (regularizationCurrentFamily G0 S)) k E.1) (x E)) =
      ∏ E, FiniteLaw.bernoulliBitMass (regularizationSamplingProbability G0 H0 b t S E) (x E)
    apply prod_congr rfl
    intro E _
    have hpE : regularizationSamplingProbability G0 H0 b t S E =
        uniformEdgeProbability (finiteHypergraphRegularizationWeight (regularizationCurrentFamily G0 S)) k E.1 := if_pos hA
    rw [hpE]
  · rw [regularizationKernel_inactive G0 H0 hGH hk hsize b t S hA]
    have hu : regularizationSamplingUpdate G0 H0 b t S = fun _ ↦ S := by
      funext x
      exact if_neg hA
    rw [hu]
    exact (FiniteLaw.map_const _ S).symm

def regularizationProposalCoupling
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] {k : ℕ}
    (G0 H0 : Finset (Finset V)) (hGH : G0 ⊆ H0) (hk : 2 ≤ k)
    (hsize : 16 * 2 ^ (k - 1) * (k - 1) ≤ Fintype.card V)
    (beta : ℝ≥0) (hbeta : regularizationBaseHazard G0 k ≤ beta)
    (b t : ℕ) (S : HypergraphRegularizationState V k) :
    FiniteLaw (Finset (UniformHyperedge V k) × HypergraphRegularizationState V k) :=
  FiniteLaw.coupledBitUpdate (regularizationSamplingProbability G0 H0 b t S)
    (fun _ ↦ geometricProposalProbability beta t)
    (regularizationSamplingProbability_le_proposal G0 H0 hGH hk hsize beta hbeta b t S)
    (fun _ ↦ geometricProposalProbability_le_one beta t)
    (regularizationSamplingUpdate G0 H0 b t S)

theorem regularizationProposalCoupling_proposal
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] {k : ℕ}
    (G0 H0 : Finset (Finset V)) (hGH : G0 ⊆ H0) (hk : 2 ≤ k)
    (hsize : 16 * 2 ^ (k - 1) * (k - 1) ≤ Fintype.card V)
    (beta : ℝ≥0) (hbeta : regularizationBaseHazard G0 k ≤ beta)
    (b t : ℕ) (S : HypergraphRegularizationState V k) :
    FiniteLaw.map Prod.fst (regularizationProposalCoupling G0 H0 hGH hk hsize beta hbeta b t S) =
      FiniteLaw.independentProposalLaw (fun _ : UniformHyperedge V k ↦ geometricProposalProbability beta t)
        (fun _ ↦ geometricProposalProbability_le_one beta t) := by
  exact FiniteLaw.coupledBitUpdate_proposal _ _ _ _ _

theorem regularizationProposalCoupling_actual
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] {k : ℕ}
    (G0 H0 : Finset (Finset V)) (hGH : G0 ⊆ H0) (hk : 2 ≤ k)
    (hsize : 16 * 2 ^ (k - 1) * (k - 1) ≤ Fintype.card V)
    (beta : ℝ≥0) (hbeta : regularizationBaseHazard G0 k ≤ beta)
    (b t : ℕ) (S : HypergraphRegularizationState V k) :
    FiniteLaw.map Prod.snd (regularizationProposalCoupling G0 H0 hGH hk hsize beta hbeta b t S) =
      regularizationKernel G0 H0 hGH hk hsize b t S := by
  unfold regularizationProposalCoupling
  rw [FiniteLaw.coupledBitUpdate_actual]
  exact (regularizationKernel_eq_sampling_update G0 H0 hGH hk hsize b t S _).symm

theorem regularizationProposalCoupling_supported
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] {k : ℕ}
    (G0 H0 : Finset (Finset V)) (hGH : G0 ⊆ H0) (hk : 2 ≤ k)
    (hsize : 16 * 2 ^ (k - 1) * (k - 1) ≤ Fintype.card V)
    (beta : ℝ≥0) (hbeta : regularizationBaseHazard G0 k ≤ beta)
    (b t : ℕ) (S : HypergraphRegularizationState V k) :
    (regularizationProposalCoupling G0 H0 hGH hk hsize beta hbeta b t S).SupportedOn
      (fun z ↦ z.2.1 ⊆ S.1 ∪ z.1) := by
  exact FiniteLaw.coupledBitUpdate_supported _ _ _ _ _ Prod.fst S.1
    (regularizationSamplingUpdate_added_subset G0 H0 b t S)

end

end Erdos207
