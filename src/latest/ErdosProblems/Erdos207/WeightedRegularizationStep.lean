/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.WeightedUniformSampler
import ErdosProblems.Erdos207.RegularizationContraction

/-! # Actual one-step weighted regularization with an explicit common failure bound -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

def WeightedRegularizationStepGood
    {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ}
    (d : V → ℝ) (a : ℝ≥0) (H : Finset (Finset V)) (ω : UniformHyperedge V k → Bool) : Prop :=
  (∀ v u, |(d v + sampledFreshUniformDegree H v ω) -
      (d u + sampledFreshUniformDegree H u ω)| < (a : ℝ) / 2) ∧
    ∀ v, (sampledFreshUniformDegree H v ω : ℝ) ≤ 4 * (a : ℝ)

theorem WeightedUniformSamplerParameters.step_good_of_centered
    {V : Type*} [Fintype V] [DecidableEq V] {w : V → ℝ≥0} {a : ℝ≥0} {k : ℕ}
    (P : WeightedUniformSamplerParameters w a k) (H : Finset (Finset V))
    (d : V → ℝ) (D : ℝ) (hcenter : ∀ v, d v + (w v : ℝ) = D + (a : ℝ))
    (hnormal : (2 : ℝ≥0) ^ (k - 1) * Nat.choose (Fintype.card V - 1) (k - 2) ≤
      (1 / 16 : ℝ≥0) * Nat.choose (Fintype.card V) (k - 1))
    (hblocked : ∀ v, (2 : ℝ≥0) ^ (k - 1) * (uniformIncidentSets k v ∩ H).card ≤
      (1 / 8 : ℝ≥0) * Nat.choose (Fintype.card V) (k - 1))
    (ω : UniformHyperedge V k → Bool)
    (hdev : ∀ v, |centeredBernoulliSum (fun E ↦ uniformEdgeProbability w k E.1)
      (uniformFreshIncidentIndex k H v) ω| ≤ (a : ℝ) / 32) :
    WeightedRegularizationStepGood d a H ω := by
  let mu := fun v ↦ ∑ E ∈ uniformFreshIncidentIndex k H v, (uniformEdgeProbability w k E.1 : ℝ)
  have hmean : ∀ v, 13 * (w v : ℝ) / 16 ≤ mu v ∧ mu v ≤ w v :=
    fun v ↦ P.fresh_mean_bounds H v hnormal (hblocked v)
  have hdev' : ∀ v, |(sampledFreshUniformDegree H v ω : ℝ) - mu v| ≤ (a : ℝ) / 32 := by
    intro v
    simpa only [centeredBernoulliSum_eq_card_sub, sampledFreshUniformDegree, mu] using hdev v
  have hweight : ∀ v, (w v : ℝ) ≤ 2 * (a : ℝ) := by
    intro v
    exact_mod_cast P.weight_upper v
  constructor
  · intro v u
    exact regularization_degree_gap_lt_half D a (d v) (d u) (w v) (w u) (mu v) (mu u)
      (sampledFreshUniformDegree H v ω) (sampledFreshUniformDegree H u ω)
      (by exact_mod_cast P.scale_pos) (hcenter v) (hcenter u) (hweight v) (hweight u)
      (hmean v).1 (hmean v).2 (hmean u).1 (hmean u).2 (hdev' v) (hdev' u)
  · intro v
    have hx := (abs_le.mp (hdev' v)).2
    have hm := (hmean v).2.trans (hweight v)
    have ha : (0 : ℝ) ≤ a := NNReal.coe_nonneg _
    linarith

theorem WeightedUniformSamplerParameters.step_failure_probability
    {V : Type*} [Fintype V] [DecidableEq V] {w : V → ℝ≥0} {a : ℝ≥0} {k : ℕ}
    (P : WeightedUniformSamplerParameters w a k) (H : Finset (Finset V))
    (d : V → ℝ) (D : ℝ) (hcenter : ∀ v, d v + (w v : ℝ) = D + (a : ℝ))
    (hnormal : (2 : ℝ≥0) ^ (k - 1) * Nat.choose (Fintype.card V - 1) (k - 2) ≤
      (1 / 16 : ℝ≥0) * Nat.choose (Fintype.card V) (k - 1))
    (hblocked : ∀ v, (2 : ℝ≥0) ^ (k - 1) * (uniformIncidentSets k v ∩ H).card ≤
      (1 / 8 : ℝ≥0) * Nat.choose (Fintype.card V) (k - 1)) :
    (P.law.probability (fun ω ↦ ¬ WeightedRegularizationStepGood d a H ω) : ℝ) ≤
      2 * Fintype.card V * Real.exp (-(a : ℝ) / 8192) := by
  let p := fun E : UniformHyperedge V k ↦ uniformEdgeProbability w k E.1
  have hmean : ∀ v, (∑ E ∈ uniformFreshIncidentIndex k H v, (p E : ℝ)) ≤ 2 * (a : ℝ) := by
    intro v
    have hw : (w v : ℝ) ≤ 2 * (a : ℝ) := by exact_mod_cast P.weight_upper v
    exact (P.fresh_mean_bounds H v hnormal (hblocked v)).2.trans hw
  have hmono : P.law.probability (fun ω ↦ ¬ WeightedRegularizationStepGood d a H ω) ≤
      P.law.probability (fun ω ↦ ∃ v,
        (a : ℝ) / 32 < |centeredBernoulliSum p (uniformFreshIncidentIndex k H v) ω|) := by
    apply P.law.probability_mono
    intro ω hbad
    by_contra hno
    apply hbad
    apply P.step_good_of_centered H d D hcenter hnormal hblocked ω
    intro v
    exact le_of_not_gt (fun hv ↦ hno ⟨v, hv⟩)
  have hmonoReal : (P.law.probability (fun ω ↦ ¬ WeightedRegularizationStepGood d a H ω) : ℝ) ≤
      (P.law.probability (fun ω ↦ ∃ v,
        (a : ℝ) / 32 < |centeredBernoulliSum p (uniformFreshIncidentIndex k H v) ω|) : ℝ) := by
    exact_mod_cast hmono
  exact hmonoReal.trans (FiniteLaw.independentBits_probability_any_abs_centered_gt
    p P.probability_le_one (uniformFreshIncidentIndex k H) a hmean)

end

end Erdos207
