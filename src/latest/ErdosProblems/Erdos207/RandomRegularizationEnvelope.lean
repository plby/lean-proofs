/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.RegularizationOutputWitness
import ErdosProblems.Erdos207.FiniteJointConditioning
import ErdosProblems.Erdos207.FixedShellSourceEnvelope

/-! # One common envelope over a law of varying auxiliary regularization problems -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

def geometricConfigurationEnvelopeLaw
    {J : Type*} [Fintype J] [DecidableEq J] (beta : ℝ≥0) (t : ℕ) : FiniteLaw (Finset (Finset J)) :=
  FiniteLaw.evolveKernels (fun n ↦ FiniteLaw.proposalUnionKernel
    (FiniteLaw.independentProposalLaw (fun _ : Finset J ↦ geometricProposalProbability beta n)
      (fun _ ↦ geometricProposalProbability_le_one beta n))) t (FiniteLaw.pure ∅)

theorem geometricConfigurationEnvelopeLaw_joint_inclusion
    {J : Type*} [Fintype J] [DecidableEq J] (beta : ℝ≥0) (t : ℕ) (U : Finset (Finset J)) :
    (geometricConfigurationEnvelopeLaw beta t).probability (fun R ↦ U ⊆ R) ≤ (2 * beta) ^ U.card :=
  FiniteLaw.independentProposalEnvelope_joint_inclusion_uniform _
    (fun n _ ↦ geometricProposalProbability_le_one beta n) t (2 * beta)
    (fun _ ↦ cumulative_geometricProposalProbability_le beta t) U

variable {D J : Type*} [Fintype D] [DecidableEq D] [Fintype J] [DecidableEq J]
  {I : D → Type*} [∀ d, Fintype (I d)] [∀ d, DecidableEq (I d)] [∀ d, Nonempty (I d)]
  {k : ℕ} (P : FiniteLaw D) (e : (d : D) → I d ↪ J)
  (G H : (d : D) → Finset (Finset (I d))) (hGH : ∀ d, G d ⊆ H d) (hk : 2 ≤ k)
  (hsize : ∀ d, 16 * 2 ^ (k - 1) * (k - 1) ≤ Fintype.card (I d))
  (beta : ℝ≥0) (hbeta : ∀ d, regularizationBaseHazard (G d) k ≤ beta) (b t : ℕ)

def randomRegularizationEnvelopeLaw : FiniteLaw (D × (Finset (Finset J) × Finset (Finset J))) :=
  P.jointBind (fun d ↦ regularizationConfigurationEnvelope (e d) (G d) (H d) (hGH d) hk (hsize d)
    beta (hbeta d) b t)

theorem randomRegularizationEnvelopeLaw_independent :
    FiniteLaw.map (fun z ↦ (z.1, z.2.1)) (randomRegularizationEnvelopeLaw P e G H hGH hk hsize beta hbeta b t) =
      P.jointBind (fun _ ↦ geometricConfigurationEnvelopeLaw beta t) := by
  have h := FiniteLaw.map_jointBind_independent P
    (fun d ↦ regularizationConfigurationEnvelope (e d) (G d) (H d) (hGH d) hk (hsize d) beta (hbeta d) b t)
    id Prod.fst (geometricConfigurationEnvelopeLaw beta t)
    (fun d ↦ regularizationConfigurationEnvelope_proposal (e d) (G d) (H d) (hGH d) hk (hsize d)
      beta (hbeta d) b t)
  rw [FiniteLaw.map_id] at h
  exact h

theorem randomRegularizationEnvelopeLaw_supported
    (ht : ∀ d, finiteHypergraphDegreeGap (G d) ≤ t)
    (hdensity : ∀ d, (2 : ℝ≥0) ^ k * finiteHypergraphMaxDegree (H d) ≤
      (1 / 36 : ℝ≥0) * Nat.choose (Fintype.card (I d)) (k - 1))
    (C : Finset (Finset J))
    (hbad : ∀ d (E : Finset (I d)), E.card = k → E.map (e d) ∉ C → E ∈ H d) :
    (randomRegularizationEnvelopeLaw P e G H hGH hk hsize beta hbeta b t).SupportedOn
      (fun z ↦ z.2.2 ⊆ z.2.1 ∧ z.2.2 ⊆ C) := by
  have hP : P.SupportedOn (fun _ ↦ True) := fun _ _ ↦ True.intro
  have h := hP.jointBind
    (K := fun d ↦ regularizationConfigurationEnvelope (e d) (G d) (H d) (hGH d) hk (hsize d)
      beta (hbeta d) b t)
    (Q := fun _ z ↦ z.2 ⊆ z.1 ∧ z.2 ⊆ C)
    (fun d _ ↦ regularizationConfigurationEnvelope_candidate_support (e d) (G d) (H d) (hGH d)
      hk (hsize d) beta (hbeta d) b t (ht d) (hdensity d) C (hbad d))
  intro z hz
  exact (h z hz).2

theorem randomRegularizationEnvelopeLaw_failure
    (ht : ∀ d, finiteHypergraphDegreeGap (G d) ≤ t)
    (hdensity : ∀ d, (2 : ℝ≥0) ^ k * finiteHypergraphMaxDegree (H d) ≤
      (1 / 36 : ℝ≥0) * Nat.choose (Fintype.card (I d)) (k - 1))
    (epsilon : ℝ≥0)
    (hepsilon : ∀ d, (finiteHypergraphDegreeGap (G d) : ℝ) *
      (2 * Fintype.card (I d) * Real.exp (-(b : ℝ) / 8192)) ≤ epsilon) :
    (randomRegularizationEnvelopeLaw P e G H hGH hk hsize beta hbeta b t).probability
      (fun z ↦ ¬ RegularizationOutputWitness (e z.1) (G z.1) (H z.1) k b z.2.2) ≤ epsilon := by
  unfold randomRegularizationEnvelopeLaw
  apply P.jointBind_probability_not_le
    (fun d ↦ regularizationConfigurationEnvelope (e d) (G d) (H d) (hGH d) hk (hsize d)
      beta (hbeta d) b t)
    (fun d (z : Finset (Finset J) × Finset (Finset J)) ↦
      RegularizationOutputWitness (e d) (G d) (H d) k b z.2) epsilon
  intro d
  have h := (regularizationConfigurationEnvelope_output_failure (e d) (G d) (H d) (hGH d)
    hk (hsize d) (hdensity d) beta (hbeta d) b t (ht d)).trans (hepsilon d)
  exact_mod_cast h

end

end Erdos207
