/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.WeightedHypergraphMeanLower

/-! # One common independent-bit law for all weighted uniform-hypergraph degrees -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

abbrev UniformHyperedge (V : Type*) [Fintype V] [DecidableEq V] (k : ℕ) :=
  ((univ : Finset V).powersetCard k)

structure WeightedUniformSamplerParameters
    {V : Type*} [Fintype V] [DecidableEq V] (w : V → ℝ≥0) (a : ℝ≥0) (k : ℕ) : Prop where
  order : 2 ≤ k
  scale_pos : 0 < a
  weight_lower : ∀ v, a ≤ w v
  weight_upper : ∀ v, w v ≤ 2 * a
  normalizer_order : k - 1 ≤ Fintype.card V
  probability_budget : (2 : ℝ≥0) ^ k * a ≤ Nat.choose (Fintype.card V) (k - 1)

theorem WeightedUniformSamplerParameters.probability_le_one
    {V : Type*} [Fintype V] [DecidableEq V] {w : V → ℝ≥0} {a : ℝ≥0} {k : ℕ}
    (P : WeightedUniformSamplerParameters w a k) (E : UniformHyperedge V k) :
    uniformEdgeProbability w k E.1 ≤ 1 := by
  have hC : (0 : ℝ≥0) < Nat.choose (Fintype.card V) (k - 1) := by
    exact_mod_cast Nat.choose_pos P.normalizer_order
  exact (uniformEdgeProbability_le w a (by have := P.order; omega) P.scale_pos
    P.weight_lower P.weight_upper (mem_powersetCard.mp E.2).2).trans
      ((div_le_one₀ hC).mpr P.probability_budget)

def WeightedUniformSamplerParameters.law
    {V : Type*} [Fintype V] [DecidableEq V] {w : V → ℝ≥0} {a : ℝ≥0} {k : ℕ}
    (P : WeightedUniformSamplerParameters w a k) : FiniteLaw (UniformHyperedge V k → Bool) :=
  FiniteLaw.independentBits (fun E ↦ uniformEdgeProbability w k E.1) P.probability_le_one

def uniformFreshIncidentIndex
    {V : Type*} [Fintype V] [DecidableEq V] (k : ℕ) (H : Finset (Finset V)) (v : V) :
    Finset (UniformHyperedge V k) :=
  univ.filter fun E ↦ v ∈ E.1 ∧ E.1 ∉ H

theorem sum_uniformFreshIncidentIndex
    {V β : Type*} [Fintype V] [DecidableEq V] [AddCommMonoid β]
    (k : ℕ) (H : Finset (Finset V)) (v : V) (f : Finset V → β) :
    ∑ E ∈ uniformFreshIncidentIndex k H v, f E.1 =
      ∑ E ∈ uniformIncidentSets k v \ H, f E := by
  calc
    _ = ∑ E ∈ (univ : Finset V).powersetCard k,
        if v ∈ E ∧ E ∉ H then f E else 0 := by
      rw [uniformFreshIncidentIndex, sum_filter]
      exact (Finset.sum_subtype ((univ : Finset V).powersetCard k)
        (p := fun E ↦ E ∈ (univ : Finset V).powersetCard k) (fun _ ↦ Iff.rfl)
        (fun E ↦ if v ∈ E ∧ E ∉ H then f E else 0)).symm
    _ = ∑ E ∈ (((univ : Finset V).powersetCard k).filter fun E ↦ v ∈ E ∧ E ∉ H), f E :=
      (sum_filter _ _).symm
    _ = _ := by
      apply sum_congr _ (fun _ _ ↦ rfl)
      ext E
      simp [uniformIncidentSets, and_assoc]

def sampledFreshUniformDegree
    {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ}
    (H : Finset (Finset V)) (v : V) (ω : UniformHyperedge V k → Bool) : ℕ :=
  ((uniformFreshIncidentIndex k H v).filter fun E ↦ ω E = true).card

theorem WeightedUniformSamplerParameters.fresh_mean_bounds
    {V : Type*} [Fintype V] [DecidableEq V] {w : V → ℝ≥0} {a : ℝ≥0} {k : ℕ}
    (P : WeightedUniformSamplerParameters w a k) (H : Finset (Finset V)) (v : V)
    (hnormal : (2 : ℝ≥0) ^ (k - 1) * Nat.choose (Fintype.card V - 1) (k - 2) ≤
      (1 / 16 : ℝ≥0) * Nat.choose (Fintype.card V) (k - 1))
    (hblocked : (2 : ℝ≥0) ^ (k - 1) * (uniformIncidentSets k v ∩ H).card ≤
      (1 / 8 : ℝ≥0) * Nat.choose (Fintype.card V) (k - 1)) :
    13 * (w v : ℝ) / 16 ≤
      (∑ E ∈ uniformFreshIncidentIndex k H v, (uniformEdgeProbability w k E.1 : ℝ)) ∧
    (∑ E ∈ uniformFreshIncidentIndex k H v, (uniformEdgeProbability w k E.1 : ℝ)) ≤ w v := by
  rw [sum_uniformFreshIncidentIndex k H v (fun E ↦ (uniformEdgeProbability w k E : ℝ))]
  have hb := uniformFresh_probability_sum_bounds w a (1 / 16) (1 / 8) H P.order v
    P.scale_pos P.weight_lower P.weight_upper P.normalizer_order hnormal hblocked
  have hu : (∑ E ∈ uniformIncidentSets k v \ H, (uniformEdgeProbability w k E : ℝ)) ≤ w v := by
    exact_mod_cast hb.1
  have hl : (w v : ℝ) ≤ (∑ E ∈ uniformIncidentSets k v \ H, (uniformEdgeProbability w k E : ℝ)) +
      (1 / 16 + 1 / 8) * (w v : ℝ) := by exact_mod_cast hb.2
  exact ⟨by linarith, hu⟩

end

end Erdos207
