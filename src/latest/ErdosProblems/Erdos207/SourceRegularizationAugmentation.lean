/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.RegularizationDecodedLaw
import ErdosProblems.Erdos207.SourceJointAugmentation

/-! # Source augmentation for the actual adaptive regularization law -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem regularizationImageLaw_source_joint_bound
    {V I : Type*} [Fintype V] [DecidableEq V]
    [Fintype I] [DecidableEq I] [Nonempty I] {ell j : ℕ}
    (W : Vortex V ell) (G0 H0 : Finset (Finset I)) (hGH : G0 ⊆ H0)
    (hk : 2 ≤ j - 2)
    (hsize : 16 * 2 ^ (j - 2 - 1) * (j - 2 - 1) ≤ Fintype.card I)
    (b : ℕ) (e : I ↪ TripleOn V) (delta : ℝ≥0)
    (hprob : 2 * regularizationBaseHazard G0 (j - 2) ≤
      sourceRandomConfigurationProbability W.terminalSize delta j) :
    HasSourceConfigurationJointBound W j delta
      (regularizationImageLaw G0 H0 hGH hk hsize b e) := by
  intro U
  apply (regularizationImageLaw_joint_inclusion G0 H0 hGH hk hsize b e U).trans
  simpa only [setWeight, prod_const] using pow_le_pow_left' hprob U.card

theorem sampleTerminalConfigurations_regularizationImageBits
    {V I : Type*} [Fintype V] [DecidableEq V]
    [Fintype I] [DecidableEq I] {ell j k : ℕ}
    (W : Vortex V ell) (e : I ↪ TripleOn V) (S : HypergraphRegularizationState I k)
    (hsub : regularizationImageEdges e S ⊆ terminalRandomConfigurations W j) :
    sampleTerminalConfigurations W j (regularizationImageBits e S) = regularizationImageEdges e S := by
  ext C
  simp only [sampleTerminalConfigurations, mem_filter, regularizationImageBits_eq_true]
  exact ⟨And.right, fun h ↦ ⟨hsub h, h⟩⟩

theorem regularizationProcessLaw_source_augmentation_failure
    {V I : Type*} [Fintype V] [DecidableEq V]
    [Fintype I] [DecidableEq I] [Nonempty I] {ell j s : ℕ}
    {W : Vortex V ell} {delta a : ℝ≥0}
    (P : SourceRandomConfigurationParameters W j delta a s)
    (G0 H0 : Finset (Finset I)) (hGH : G0 ⊆ H0)
    (hk : 2 ≤ j - 2)
    (hsize : 16 * 2 ^ (j - 2 - 1) * (j - 2 - 1) ≤ Fintype.card I)
    (hdensity : (2 : ℝ≥0) ^ (j - 2) * finiteHypergraphMaxDegree H0 ≤
      (1 / 36 : ℝ≥0) * Nat.choose (Fintype.card I) (j - 2 - 1))
    (b : ℕ) (e : I ↪ TripleOn V)
    (hbad : ∀ E : Finset I, E.card = j - 2 →
      E.map e ∉ terminalRandomConfigurations W j → E ∈ H0)
    (hprob : 2 * regularizationBaseHazard G0 (j - 2) ≤
      sourceRandomConfigurationProbability W.terminalSize delta j)
    (F : ForbiddenFamilyOn V) (y z : ℝ≥0) (hF : SourceVortexWellSpread W j F y z)
    (hdeltaY : delta * y ≤ W.terminalSize) :
    (regularizationProcessLaw G0 H0 hGH hk hsize b).probability
      (fun S ↦ ¬ SourceVortexWellSpread W j (F ∪ regularizationImageEdges e S) (y + a) (z + 3 * a)) ≤
      sourceRandomFailureCoefficient W j * ((2 : ℝ≥0) ^ s)⁻¹ := by
  classical
  have hsource := P.joint_augmentation_failure_probability
    (regularizationImageLaw G0 H0 hGH hk hsize b e)
    (regularizationImageLaw_source_joint_bound W G0 H0 hGH hk hsize b e delta hprob)
    F y z hF hdeltaY
  rw [regularizationImageLaw, FiniteLaw.probability_map] at hsource
  apply le_trans _ hsource
  apply FiniteLaw.probability_mono_of_supported _
    (regularizationProcessLaw_avoids_and_bounded G0 H0 hGH hk hsize hdensity b)
  intro S hS hfail hgood
  have hsub := regularizationImageEdges_subset_of_avoid e (terminalRandomConfigurations W j) H0 S hS.1 hbad
  rw [sampleTerminalConfigurations_regularizationImageBits W e S hsub] at hgood
  exact hfail hgood

end

end Erdos207
