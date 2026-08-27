/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.RegularizationConfigurationEnvelope

/-! # Recovering genuine auxiliary regularizers from common-space outputs -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

def RegularizationOutputWitness
    {I J : Type*} [Fintype I] [DecidableEq I] [Nonempty I] [DecidableEq J]
    (e : I ↪ J) (G H : Finset (Finset I)) (k b : ℕ) (R : Finset (Finset J)) : Prop :=
  ∃ A : Finset (Finset I), A.image (Finset.map e) = R ∧
    Disjoint A H ∧ (∀ E ∈ A, E.card = k) ∧
    finiteHypergraphMaxDegree (G ∪ A) ≤ 9 * finiteHypergraphMaxDegree G ∧
    finiteHypergraphDegreeGap (G ∪ A) ≤ b

theorem regularizationOutputWitness_of_state
    {I J : Type*} [Fintype I] [DecidableEq I] [Nonempty I] [DecidableEq J] {k b : ℕ}
    (e : I ↪ J) (G H : Finset (Finset I)) (S : HypergraphRegularizationState I k)
    (havoid : Disjoint (regularizationAcceptedEdges S) H)
    (hmax : finiteHypergraphMaxDegree (regularizationCurrentFamily G S) ≤ 9 * finiteHypergraphMaxDegree G)
    (hgap : finiteHypergraphDegreeGap (regularizationCurrentFamily G S) ≤ b) :
    RegularizationOutputWitness e G H k b (regularizationImageEdges e S) :=
  ⟨regularizationAcceptedEdges S, rfl, havoid, regularizationAcceptedEdges_uniform S, hmax, hgap⟩

theorem regularizationProcessLaw_output_failure
    {I J : Type*} [Fintype I] [DecidableEq I] [Nonempty I] [DecidableEq J] {k : ℕ}
    (e : I ↪ J) (G H : Finset (Finset I)) (hGH : G ⊆ H) (hk : 2 ≤ k)
    (hsize : 16 * 2 ^ (k - 1) * (k - 1) ≤ Fintype.card I)
    (hdensity : (2 : ℝ≥0) ^ k * finiteHypergraphMaxDegree H ≤
      (1 / 36 : ℝ≥0) * Nat.choose (Fintype.card I) (k - 1)) (b : ℕ) :
    ((regularizationProcessLaw G H hGH hk hsize b).probability
      (fun S ↦ ¬ RegularizationOutputWitness e G H k b (regularizationImageEdges e S)) : ℝ) ≤
      finiteHypergraphDegreeGap G * (2 * Fintype.card I * Real.exp (-(b : ℝ) / 8192)) := by
  have hprob := (regularizationProcessLaw G H hGH hk hsize b).probability_mono_of_supported
    (regularizationProcessLaw_avoids_and_bounded G H hGH hk hsize hdensity b)
    (P := fun S ↦ ¬ RegularizationOutputWitness e G H k b (regularizationImageEdges e S))
    (Q := fun S ↦ b < finiteHypergraphDegreeGap (regularizationCurrentFamily G S))
    (fun S hs hbad ↦ by
      by_contra hnot
      exact hbad (regularizationOutputWitness_of_state e G H S hs.1 hs.2.2 (not_lt.mp hnot)))
  have hreal : ((regularizationProcessLaw G H hGH hk hsize b).probability
      (fun S ↦ ¬ RegularizationOutputWitness e G H k b (regularizationImageEdges e S)) : ℝ) ≤
      ((regularizationProcessLaw G H hGH hk hsize b).probability
        (fun S ↦ b < finiteHypergraphDegreeGap (regularizationCurrentFamily G S)) : ℝ) := by
    exact_mod_cast hprob
  exact hreal.trans (regularizationProcessLaw_gap_failure G H hGH hk hsize hdensity b)

theorem regularizationConfigurationEnvelope_output_failure
    {I J : Type*} [Fintype I] [DecidableEq I] [Nonempty I] [Fintype J] [DecidableEq J] {k : ℕ}
    (e : I ↪ J) (G H : Finset (Finset I)) (hGH : G ⊆ H) (hk : 2 ≤ k)
    (hsize : 16 * 2 ^ (k - 1) * (k - 1) ≤ Fintype.card I)
    (hdensity : (2 : ℝ≥0) ^ k * finiteHypergraphMaxDegree H ≤
      (1 / 36 : ℝ≥0) * Nat.choose (Fintype.card I) (k - 1))
    (beta : ℝ≥0) (hbeta : regularizationBaseHazard G k ≤ beta)
    (b t : ℕ) (ht : finiteHypergraphDegreeGap G ≤ t) :
    ((regularizationConfigurationEnvelope e G H hGH hk hsize beta hbeta b t).probability
      (fun z ↦ ¬ RegularizationOutputWitness e G H k b z.2) : ℝ) ≤
      finiteHypergraphDegreeGap G * (2 * Fintype.card I * Real.exp (-(b : ℝ) / 8192)) := by
  have heq := congrArg (fun L : FiniteLaw (Finset (Finset J)) ↦
      L.probability (fun R ↦ ¬ RegularizationOutputWitness e G H k b R))
    (regularizationConfigurationEnvelope_actual e G H hGH hk hsize beta hbeta b t ht)
  simp only [FiniteLaw.probability_map] at heq
  rw [heq]
  exact regularizationProcessLaw_output_failure e G H hGH hk hsize hdensity b

end

end Erdos207
