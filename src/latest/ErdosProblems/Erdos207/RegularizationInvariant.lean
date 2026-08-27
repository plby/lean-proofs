/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.RegularizationKernel

/-! # Deterministic invariants of the actual adaptive regularization process -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

structure RegularizationInvariant
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] {k : ℕ}
    (G0 H0 : Finset (Finset V)) (b t : ℕ) (S : HypergraphRegularizationState V k) : Prop where
  avoid : Disjoint (regularizationAcceptedEdges S) H0
  graph_potential : finiteHypergraphMaxDegree (regularizationCurrentFamily G0 S) +
    8 * finiteHypergraphDegreeGap (regularizationCurrentFamily G0 S) ≤
      finiteHypergraphMaxDegree G0 + 8 * finiteHypergraphDegreeGap G0
  forbidden_potential : finiteHypergraphMaxDegree (regularizationCurrentFamily H0 S) +
    8 * finiteHypergraphDegreeGap (regularizationCurrentFamily G0 S) ≤
      finiteHypergraphMaxDegree H0 + 8 * finiteHypergraphDegreeGap G0
  clock : S.2 = false → b < finiteHypergraphDegreeGap (regularizationCurrentFamily G0 S) →
    2 ^ t * finiteHypergraphDegreeGap (regularizationCurrentFamily G0 S) ≤ finiteHypergraphDegreeGap G0

theorem regularizationInvariant_initial
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] {k : ℕ}
    (G0 H0 : Finset (Finset V)) (b : ℕ) :
    RegularizationInvariant G0 H0 b 0 (regularizationInitialState V k) := by
  constructor
  · simp [regularizationInitialState, regularizationAcceptedEdges]
  · simp
  · simp
  · intro _hf _hb
    simp

theorem RegularizationInvariant.density
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] {k b t : ℕ}
    {G0 H0 : Finset (Finset V)} {S : HypergraphRegularizationState V k}
    (h : RegularizationInvariant G0 H0 b t S) (hGH : G0 ⊆ H0)
    (hdensity : (2 : ℝ≥0) ^ k * finiteHypergraphMaxDegree H0 ≤
      (1 / 36 : ℝ≥0) * Nat.choose (Fintype.card V) (k - 1)) :
    (2 : ℝ≥0) ^ k * finiteHypergraphMaxDegree (regularizationCurrentFamily H0 S) ≤
      (1 / 4 : ℝ≥0) * Nat.choose (Fintype.card V) (k - 1) := by
  have hgap : finiteHypergraphDegreeGap G0 ≤ finiteHypergraphMaxDegree H0 :=
    (Nat.sub_le _ _).trans (finiteHypergraphMaxDegree_mono hGH)
  have hmax : finiteHypergraphMaxDegree (regularizationCurrentFamily H0 S) ≤
      9 * finiteHypergraphMaxDegree H0 := by
    have := h.forbidden_potential
    omega
  have hmaxNN : (finiteHypergraphMaxDegree (regularizationCurrentFamily H0 S) : ℝ≥0) ≤
      9 * finiteHypergraphMaxDegree H0 := by exact_mod_cast hmax
  calc
    _ ≤ (2 : ℝ≥0) ^ k * (9 * finiteHypergraphMaxDegree H0) :=
      mul_le_mul_of_nonneg_left hmaxNN zero_le
    _ = 9 * ((2 : ℝ≥0) ^ k * finiteHypergraphMaxDegree H0) := by ring
    _ ≤ 9 * ((1 / 36 : ℝ≥0) * Nat.choose (Fintype.card V) (k - 1)) :=
      mul_le_mul_of_nonneg_left hdensity zero_le
    _ = _ := by apply NNReal.eq; push_cast; ring

theorem RegularizationInvariant.active
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] {k b t : ℕ}
    {G0 H0 : Finset (Finset V)} {S : HypergraphRegularizationState V k}
    (h : RegularizationInvariant G0 H0 b t S) (hGH : G0 ⊆ H0)
    (hdensity : (2 : ℝ≥0) ^ k * finiteHypergraphMaxDegree H0 ≤
      (1 / 36 : ℝ≥0) * Nat.choose (Fintype.card V) (k - 1))
    (hf : S.2 = false) (hb : b < finiteHypergraphDegreeGap (regularizationCurrentFamily G0 S)) :
    RegularizationActive G0 H0 b t S :=
  ⟨hf, hb, h.clock hf hb, h.density hGH hdensity⟩

theorem RegularizationInvariant.reject
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] {k b t : ℕ}
    {G0 H0 : Finset (Finset V)} {S : HypergraphRegularizationState V k}
    (h : RegularizationInvariant G0 H0 b t S) :
    RegularizationInvariant G0 H0 b (t + 1) (regularizationReject S) := by
  refine ⟨h.avoid, h.graph_potential, h.forbidden_potential, ?_⟩
  intro hf
  simp [regularizationReject] at hf

theorem RegularizationInvariant.inactive_advance
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] {k b t : ℕ}
    {G0 H0 : Finset (Finset V)} {S : HypergraphRegularizationState V k}
    (h : RegularizationInvariant G0 H0 b t S) (hGH : G0 ⊆ H0)
    (hdensity : (2 : ℝ≥0) ^ k * finiteHypergraphMaxDegree H0 ≤
      (1 / 36 : ℝ≥0) * Nat.choose (Fintype.card V) (k - 1))
    (hA : ¬ RegularizationActive G0 H0 b t S) :
    RegularizationInvariant G0 H0 b (t + 1) S := by
  refine ⟨h.avoid, h.graph_potential, h.forbidden_potential, ?_⟩
  intro hf hb
  exact (hA (h.active hGH hdensity hf hb)).elim

theorem RegularizationInvariant.accept
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] {k b t : ℕ}
    {G0 H0 : Finset (Finset V)} {S : HypergraphRegularizationState V k}
    (h : RegularizationInvariant G0 H0 b t S) (hGH : G0 ⊆ H0)
    (hA : RegularizationActive G0 H0 b t S) (ω : UniformHyperedge V k → Bool)
    (hgood : WeightedRegularizationStepGood
      (fun v ↦ finiteHypergraphDegree (regularizationCurrentFamily G0 S) v)
      (finiteHypergraphDegreeGap (regularizationCurrentFamily G0 S)) (regularizationCurrentFamily H0 S) ω) :
    RegularizationInvariant G0 H0 b (t + 1)
      (regularizationAccept S (regularizationCurrentFamily H0 S) ω) := by
  have hGH' := regularizationCurrentFamily_mono_base hGH S
  constructor
  · exact regularizationAccept_preserves_disjoint H0 S h.avoid ω
  · simp only [regularizationCurrentFamily_accept]
    exact (hypergraph_regularization_potential_le _ _ hGH' ω hgood).trans h.graph_potential
  · simp only [regularizationCurrentFamily_accept]
    exact (hypergraph_regularization_forbidden_potential_le _ _ hGH' ω hgood).trans h.forbidden_potential
  · intro _hf _hb
    simp only [regularizationCurrentFamily_accept]
    have hg := hypergraph_degree_gap_lt_of_step_good _ _ hGH'
      (finiteHypergraphDegreeGap (regularizationCurrentFamily G0 S)) ω hgood
    have hhalf : 2 * finiteHypergraphDegreeGap
        (regularizationCurrentFamily G0 S ∪ sampledFreshUniformHypergraph (regularizationCurrentFamily H0 S) ω) ≤
        finiteHypergraphDegreeGap (regularizationCurrentFamily G0 S) := by
      exact_mod_cast (show (2 : ℝ) * finiteHypergraphDegreeGap
        (regularizationCurrentFamily G0 S ∪ sampledFreshUniformHypergraph (regularizationCurrentFamily H0 S) ω) ≤
        finiteHypergraphDegreeGap (regularizationCurrentFamily G0 S) by linarith)
    calc
      _ = 2 ^ t * (2 * finiteHypergraphDegreeGap
          (regularizationCurrentFamily G0 S ∪ sampledFreshUniformHypergraph (regularizationCurrentFamily H0 S) ω)) := by
        rw [pow_succ]; ring
      _ ≤ 2 ^ t * finiteHypergraphDegreeGap (regularizationCurrentFamily G0 S) := Nat.mul_le_mul_left _ hhalf
      _ ≤ _ := hA.2.2.1

theorem RegularizationInvariant.kernel_supported
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] {k b t : ℕ}
    {G0 H0 : Finset (Finset V)} {S : HypergraphRegularizationState V k}
    (h : RegularizationInvariant G0 H0 b t S) (hGH : G0 ⊆ H0) (hk : 2 ≤ k)
    (hsize : 16 * 2 ^ (k - 1) * (k - 1) ≤ Fintype.card V)
    (hdensity : (2 : ℝ≥0) ^ k * finiteHypergraphMaxDegree H0 ≤
      (1 / 36 : ℝ≥0) * Nat.choose (Fintype.card V) (k - 1)) :
    (regularizationKernel G0 H0 hGH hk hsize b t S).SupportedOn (RegularizationInvariant G0 H0 b (t + 1)) := by
  classical
  by_cases hA : RegularizationActive G0 H0 b t S
  · rw [regularizationKernel_active G0 H0 hGH hk hsize b t S hA]
    refine FiniteLaw.SupportedOn.map (P := fun _ ↦ True) (fun _ _ ↦ trivial) _ ?_
    intro ω _hω
    unfold regularizationBatchOutcome
    split_ifs with hgood
    · exact h.accept hGH hA ω hgood
    · exact h.reject
  · rw [regularizationKernel_inactive G0 H0 hGH hk hsize b t S hA]
    exact FiniteLaw.supportedOn_pure _ (h.inactive_advance hGH hdensity hA)

end

end Erdos207
