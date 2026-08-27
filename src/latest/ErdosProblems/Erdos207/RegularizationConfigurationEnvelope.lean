/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.RegularizationAmbientEnvelope
import ErdosProblems.Erdos207.RegularizationFixedHorizon
import ErdosProblems.Erdos207.RegularizationDecodedLaw
import ErdosProblems.Erdos207.FiniteLawSupportPullback

/-! # Common configuration-space outputs of auxiliary regularizers -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

def uniformHyperedgeMapEmbedding
    {I J : Type*} [Fintype I] [DecidableEq I] [DecidableEq J] (k : ℕ) (e : I ↪ J) :
    UniformHyperedge I k ↪ Finset J :=
  ⟨fun E ↦ E.1.map e, (Finset.map_injective e).comp Subtype.val_injective⟩

theorem regularizationImageEdges_eq_map
    {I J : Type*} [Fintype I] [DecidableEq I] [DecidableEq J] {k : ℕ}
    (e : I ↪ J) (S : HypergraphRegularizationState I k) :
    regularizationImageEdges e S = S.1.map (uniformHyperedgeMapEmbedding k e) := by
  rw [regularizationImageEdges_eq, map_eq_image]
  rfl

variable {I J : Type*} [Fintype I] [DecidableEq I] [Nonempty I] [Fintype J] [DecidableEq J] {k : ℕ}
  (e : I ↪ J) (G0 H0 : Finset (Finset I)) (hGH : G0 ⊆ H0) (hk : 2 ≤ k)
  (hsize : 16 * 2 ^ (k - 1) * (k - 1) ≤ Fintype.card I)
  (beta : ℝ≥0) (hbeta : regularizationBaseHazard G0 k ≤ beta) (b t : ℕ)

def regularizationConfigurationEnvelope : FiniteLaw (Finset (Finset J) × Finset (Finset J)) :=
  FiniteLaw.map (fun z ↦ (z.1, regularizationImageEdges e z.2))
    (regularizationAmbientEnvelope (uniformHyperedgeMapEmbedding k e) G0 H0 hGH hk hsize beta hbeta b t)

theorem regularizationConfigurationEnvelope_proposal :
    FiniteLaw.map Prod.fst (regularizationConfigurationEnvelope e G0 H0 hGH hk hsize beta hbeta b t) =
      FiniteLaw.evolveKernels (fun n ↦ FiniteLaw.proposalUnionKernel
        (FiniteLaw.independentProposalLaw (fun _ : Finset J ↦ geometricProposalProbability beta n)
          (fun _ ↦ geometricProposalProbability_le_one beta n))) t (FiniteLaw.pure ∅) := by
  unfold regularizationConfigurationEnvelope
  rw [FiniteLaw.map_comp]
  exact regularizationAmbientEnvelope_proposal _ _ _ _ _ _ _ _ _ _

theorem regularizationConfigurationEnvelope_actual
    (ht : finiteHypergraphDegreeGap G0 ≤ t) :
    FiniteLaw.map Prod.snd (regularizationConfigurationEnvelope e G0 H0 hGH hk hsize beta hbeta b t) =
      FiniteLaw.map (regularizationImageEdges e) (regularizationProcessLaw G0 H0 hGH hk hsize b) := by
  unfold regularizationConfigurationEnvelope
  rw [FiniteLaw.map_comp, ← regularizationEvolve_eq_processLaw_of_gap_le G0 H0 hGH hk hsize b t ht,
    ← regularizationAmbientEnvelope_actual (uniformHyperedgeMapEmbedding k e) G0 H0 hGH hk hsize beta hbeta b t,
    FiniteLaw.map_comp]
  rfl

theorem regularizationConfigurationEnvelope_containment :
    (regularizationConfigurationEnvelope e G0 H0 hGH hk hsize beta hbeta b t).SupportedOn
      (fun z ↦ z.2 ⊆ z.1) := by
  unfold regularizationConfigurationEnvelope
  apply (regularizationAmbientEnvelope_supported (uniformHyperedgeMapEmbedding k e)
    G0 H0 hGH hk hsize beta hbeta b t).map
    (Q := fun z ↦ z.2 ⊆ z.1) (fun z ↦ (z.1, regularizationImageEdges e z.2))
  intro z hz
  simpa only [regularizationImageEdges_eq_map] using hz

theorem regularizationConfigurationEnvelope_candidate_support
    (ht : finiteHypergraphDegreeGap G0 ≤ t)
    (hdensity : (2 : ℝ≥0) ^ k * finiteHypergraphMaxDegree H0 ≤
      (1 / 36 : ℝ≥0) * Nat.choose (Fintype.card I) (k - 1))
    (C : Finset (Finset J)) (hbad : ∀ E : Finset I, E.card = k → E.map e ∉ C → E ∈ H0) :
    (regularizationConfigurationEnvelope e G0 H0 hGH hk hsize beta hbeta b t).SupportedOn
      (fun z ↦ z.2 ⊆ z.1 ∧ z.2 ⊆ C) := by
  have hC : (FiniteLaw.map Prod.snd
      (regularizationConfigurationEnvelope e G0 H0 hGH hk hsize beta hbeta b t)).SupportedOn
      (fun R ↦ R ⊆ C) := by
    rw [regularizationConfigurationEnvelope_actual e G0 H0 hGH hk hsize beta hbeta b t ht]
    apply (regularizationProcessLaw_avoids_and_bounded G0 H0 hGH hk hsize hdensity b).map
      (Q := fun R ↦ R ⊆ C) (regularizationImageEdges e)
    intro S hS
    exact regularizationImageEdges_subset_of_avoid e C H0 S hS.1 hbad
  intro z hz
  exact ⟨regularizationConfigurationEnvelope_containment e G0 H0 hGH hk hsize beta hbeta b t z hz,
    hC.of_map z hz⟩

end

end Erdos207
