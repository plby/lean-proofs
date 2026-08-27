/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.RegularizationState
import ErdosProblems.Erdos207.BatchKernelJointInclusion

/-! # The actual stopped adaptive weighted-regularization kernel -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

def regularizationBatchOutcome
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] {k : ℕ}
    (G H : Finset (Finset V)) (S : HypergraphRegularizationState V k)
    (ω : UniformHyperedge V k → Bool) : HypergraphRegularizationState V k := by
  classical
  exact if WeightedRegularizationStepGood (fun v ↦ finiteHypergraphDegree G v)
      (finiteHypergraphDegreeGap G) H ω then regularizationAccept S H ω else regularizationReject S

def RegularizationActive
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] {k : ℕ}
    (G0 H0 : Finset (Finset V)) (b t : ℕ) (S : HypergraphRegularizationState V k) : Prop :=
  S.2 = false ∧ b < finiteHypergraphDegreeGap (regularizationCurrentFamily G0 S) ∧
    2 ^ t * finiteHypergraphDegreeGap (regularizationCurrentFamily G0 S) ≤ finiteHypergraphDegreeGap G0 ∧
    (2 : ℝ≥0) ^ k * finiteHypergraphMaxDegree (regularizationCurrentFamily H0 S) ≤
      (1 / 4 : ℝ≥0) * Nat.choose (Fintype.card V) (k - 1)

def regularizationKernel
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] {k : ℕ}
    (G0 H0 : Finset (Finset V)) (hGH : G0 ⊆ H0) (hk : 2 ≤ k)
    (hsize : 16 * 2 ^ (k - 1) * (k - 1) ≤ Fintype.card V)
    (b t : ℕ) (S : HypergraphRegularizationState V k) : FiniteLaw (HypergraphRegularizationState V k) := by
  classical
  exact if hA : RegularizationActive G0 H0 b t S then
    FiniteLaw.map
      (regularizationBatchOutcome (regularizationCurrentFamily G0 S) (regularizationCurrentFamily H0 S) S)
      (hypergraphRegularizationParameters (regularizationCurrentFamily G0 S) (regularizationCurrentFamily H0 S)
        (regularizationCurrentFamily_mono_base hGH S) hk
        (Nat.zero_lt_of_lt hA.2.1) hsize hA.2.2.2).law
  else FiniteLaw.pure S

theorem regularizationKernel_inactive
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] {k : ℕ}
    (G0 H0 : Finset (Finset V)) (hGH : G0 ⊆ H0) (hk : 2 ≤ k)
    (hsize : 16 * 2 ^ (k - 1) * (k - 1) ≤ Fintype.card V)
    (b t : ℕ) (S : HypergraphRegularizationState V k)
    (hA : ¬ RegularizationActive G0 H0 b t S) :
    regularizationKernel G0 H0 hGH hk hsize b t S = FiniteLaw.pure S := by
  simp only [regularizationKernel, dif_neg hA]

theorem regularizationKernel_active
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] {k : ℕ}
    (G0 H0 : Finset (Finset V)) (hGH : G0 ⊆ H0) (hk : 2 ≤ k)
    (hsize : 16 * 2 ^ (k - 1) * (k - 1) ≤ Fintype.card V)
    (b t : ℕ) (S : HypergraphRegularizationState V k)
    (hA : RegularizationActive G0 H0 b t S) :
    regularizationKernel G0 H0 hGH hk hsize b t S =
      FiniteLaw.map
        (regularizationBatchOutcome (regularizationCurrentFamily G0 S) (regularizationCurrentFamily H0 S) S)
        (hypergraphRegularizationParameters (regularizationCurrentFamily G0 S) (regularizationCurrentFamily H0 S)
          (regularizationCurrentFamily_mono_base hGH S) hk
          (Nat.zero_lt_of_lt hA.2.1) hsize hA.2.2.2).law := by
  simp only [regularizationKernel, dif_pos hA]

theorem regularizationBatchOutcome_added_subset
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] {k : ℕ}
    (G H : Finset (Finset V)) (S : HypergraphRegularizationState V k)
    (ω : UniformHyperedge V k → Bool) :
    (regularizationBatchOutcome G H S ω).1 ⊆ S.1 ∪ FiniteLaw.selectedByBits ω := by
  classical
  unfold regularizationBatchOutcome
  split_ifs
  · apply union_subset_union Subset.rfl
    intro E hE
    exact FiniteLaw.mem_selectedByBits_iff.mpr (mem_filter.mp hE).2.1
  · exact subset_union_left

theorem regularizationBatchOutcome_failed_iff
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] {k : ℕ}
    (G H : Finset (Finset V)) (S : HypergraphRegularizationState V k)
    (ω : UniformHyperedge V k → Bool) :
    (regularizationBatchOutcome G H S ω).2 = true ↔
      ¬ WeightedRegularizationStepGood (fun v ↦ finiteHypergraphDegree G v)
        (finiteHypergraphDegreeGap G) H ω := by
  classical
  unfold regularizationBatchOutcome
  split_ifs <;> simp_all [regularizationAccept, regularizationReject]

end

end Erdos207
