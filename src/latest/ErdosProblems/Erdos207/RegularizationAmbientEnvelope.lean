/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.RegularizationProposalCoupling
import ErdosProblems.Erdos207.CoupledEmbeddedBitUpdate

/-! # Exact regularization marginals under a fixed ambient proposal envelope -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
  [Fintype I] [DecidableEq I] {k : ℕ}
  (e : UniformHyperedge V k ↪ I)
  (G0 H0 : Finset (Finset V)) (hGH : G0 ⊆ H0) (hk : 2 ≤ k)
  (hsize : 16 * 2 ^ (k - 1) * (k - 1) ≤ Fintype.card V)
  (beta : ℝ≥0) (hbeta : regularizationBaseHazard G0 k ≤ beta) (b : ℕ)

def regularizationAmbientCoupling (t : ℕ) (S : HypergraphRegularizationState V k) :
    FiniteLaw (Finset I × HypergraphRegularizationState V k) :=
  FiniteLaw.coupledEmbeddedBitUpdate e (regularizationSamplingProbability G0 H0 b t S)
    (fun _ ↦ geometricProposalProbability beta t)
    (regularizationSamplingProbability_le_proposal G0 H0 hGH hk hsize beta hbeta b t S)
    (fun _ ↦ geometricProposalProbability_le_one beta t)
    (regularizationSamplingUpdate G0 H0 b t S)

theorem regularizationAmbientCoupling_proposal (t : ℕ) (S : HypergraphRegularizationState V k) :
    FiniteLaw.map Prod.fst (regularizationAmbientCoupling e G0 H0 hGH hk hsize beta hbeta b t S) =
      FiniteLaw.independentProposalLaw (fun _ : I ↦ geometricProposalProbability beta t)
        (fun _ ↦ geometricProposalProbability_le_one beta t) :=
  FiniteLaw.coupledEmbeddedBitUpdate_proposal _ _ _ _ _ _

theorem regularizationAmbientCoupling_actual (t : ℕ) (S : HypergraphRegularizationState V k) :
    FiniteLaw.map Prod.snd (regularizationAmbientCoupling e G0 H0 hGH hk hsize beta hbeta b t S) =
      regularizationKernel G0 H0 hGH hk hsize b t S := by
  unfold regularizationAmbientCoupling
  rw [FiniteLaw.coupledEmbeddedBitUpdate_actual]
  exact (regularizationKernel_eq_sampling_update G0 H0 hGH hk hsize b t S _).symm

theorem regularizationAmbientCoupling_supported (t : ℕ) (S : HypergraphRegularizationState V k) :
    (regularizationAmbientCoupling e G0 H0 hGH hk hsize beta hbeta b t S).SupportedOn
      (fun z ↦ z.2.1.map e ⊆ S.1.map e ∪ z.1) :=
  FiniteLaw.coupledEmbeddedBitUpdate_supported _ _ _ _ _ _ Prod.fst S.1
    (regularizationSamplingUpdate_added_subset G0 H0 b t S)

def regularizationAmbientEnvelope (t : ℕ) :
    FiniteLaw (Finset I × HypergraphRegularizationState V k) :=
  FiniteLaw.coupledEnvelopeProcess (regularizationAmbientCoupling e G0 H0 hGH hk hsize beta hbeta b)
    t (FiniteLaw.pure (regularizationInitialState V k))

theorem regularizationAmbientEnvelope_proposal (t : ℕ) :
    FiniteLaw.map Prod.fst (regularizationAmbientEnvelope e G0 H0 hGH hk hsize beta hbeta b t) =
      FiniteLaw.evolveKernels (fun n ↦ FiniteLaw.proposalUnionKernel
        (FiniteLaw.independentProposalLaw (fun _ : I ↦ geometricProposalProbability beta n)
          (fun _ ↦ geometricProposalProbability_le_one beta n))) t (FiniteLaw.pure ∅) :=
  FiniteLaw.coupledEnvelopeProcess_proposal _ _
    (regularizationAmbientCoupling_proposal e G0 H0 hGH hk hsize beta hbeta b) t _

theorem regularizationAmbientEnvelope_actual (t : ℕ) :
    FiniteLaw.map Prod.snd (regularizationAmbientEnvelope e G0 H0 hGH hk hsize beta hbeta b t) =
      FiniteLaw.evolveKernels (regularizationKernel G0 H0 hGH hk hsize b) t
        (FiniteLaw.pure (regularizationInitialState V k)) :=
  FiniteLaw.coupledEnvelopeProcess_actual _ _
    (regularizationAmbientCoupling_actual e G0 H0 hGH hk hsize beta hbeta b) t _

theorem regularizationAmbientEnvelope_supported (t : ℕ) :
    (regularizationAmbientEnvelope e G0 H0 hGH hk hsize beta hbeta b t).SupportedOn
      (fun z ↦ z.2.1.map e ⊆ z.1) := by
  unfold regularizationAmbientEnvelope
  apply FiniteLaw.coupledEnvelopeProcess_supported
    (regularizationAmbientCoupling e G0 H0 hGH hk hsize beta hbeta b)
    (fun S : HypergraphRegularizationState V k ↦ S.1.map e)
    (regularizationAmbientCoupling_supported e G0 H0 hGH hk hsize beta hbeta b) t
    (FiniteLaw.pure (regularizationInitialState V k))
  exact FiniteLaw.supportedOn_pure _ (by simp [regularizationInitialState])

theorem regularizationAmbientEnvelope_joint_inclusion (t : ℕ) (U : Finset I) :
    (regularizationAmbientEnvelope e G0 H0 hGH hk hsize beta hbeta b t).probability
      (fun z ↦ U ⊆ z.1) ≤ (2 * beta) ^ U.card := by
  rw [← FiniteLaw.probability_map Prod.fst, regularizationAmbientEnvelope_proposal]
  exact FiniteLaw.independentProposalEnvelope_joint_inclusion_uniform
    (fun n _ ↦ geometricProposalProbability beta n)
    (fun n _ ↦ geometricProposalProbability_le_one beta n) t (2 * beta)
    (fun _ ↦ cumulative_geometricProposalProbability_le beta t) U

end

end Erdos207
