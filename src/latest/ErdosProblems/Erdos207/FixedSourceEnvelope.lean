/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.IndependentSeedConditioning
import ErdosProblems.Erdos207.SourceJointAugmentation
import ErdosProblems.Erdos207.SourceAugmentationCounts

/-! # Fixing a well-spread source envelope without changing prior random data -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

def configurationEnvelopeBits
    {V : Type*} [DecidableEq V] (R : ForbiddenFamilyOn V) : TripleSystemOn V → Bool :=
  fun E ↦ decide (E ∈ R)

@[simp] theorem configurationEnvelopeBits_eq_true
    {V : Type*} [DecidableEq V] (R : ForbiddenFamilyOn V) (E : TripleSystemOn V) :
    configurationEnvelopeBits R E = true ↔ E ∈ R := by simp [configurationEnvelopeBits]

theorem sampleTerminalConfigurations_envelopeBits
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (j : ℕ) (R : ForbiddenFamilyOn V) :
    sampleTerminalConfigurations W j (configurationEnvelopeBits R) = terminalRandomConfigurations W j ∩ R := by
  ext E
  simp [sampleTerminalConfigurations]

theorem configurationEnvelopeBits_source_joint_bound
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (j : ℕ) (delta : ℝ≥0) (Q : FiniteLaw (ForbiddenFamilyOn V))
    (hQ : ∀ U, Q.probability (fun R ↦ U ⊆ R) ≤
      sourceRandomConfigurationProbability W.terminalSize delta j ^ U.card) :
    HasSourceConfigurationJointBound W j delta (FiniteLaw.map configurationEnvelopeBits Q) := by
  intro U
  rw [FiniteLaw.probability_map]
  simp only [configurationEnvelopeBits_eq_true]
  change Q.probability (fun R ↦ U ⊆ R) ≤ _
  simpa only [setWeight, prod_const] using hQ U

theorem configurationEnvelope_goodCounts_failure
    {V : Type*} [Fintype V] [DecidableEq V] {ell j s : ℕ}
    {W : Vortex V ell} {delta a : ℝ≥0}
    (P : SourceRandomConfigurationParameters W j delta a s)
    (Q : FiniteLaw (ForbiddenFamilyOn V))
    (hQ : ∀ U, Q.probability (fun R ↦ U ⊆ R) ≤
      sourceRandomConfigurationProbability W.terminalSize delta j ^ U.card)
    (F : ForbiddenFamilyOn V) (y z : ℝ≥0) (hF : SourceVortexWellSpread W j F y z)
    (hdeltaY : delta * y ≤ W.terminalSize) :
    Q.probability (fun R ↦ ¬ SourceRandomCountsGood W j F a (configurationEnvelopeBits R)) ≤
      sourceRandomFailureCoefficient W j * ((2 : ℝ≥0) ^ s)⁻¹ := by
  have h := P.joint_goodCounts_failure_probability (FiniteLaw.map configurationEnvelopeBits Q)
    (configurationEnvelopeBits_source_joint_bound W j delta Q hQ) F y z hF hdeltaY
  simpa only [FiniteLaw.probability_map] using h

theorem exists_fixed_source_envelope
    {Ω D V : Type*} [Fintype Ω] [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
    {ell j s : ℕ} {W : Vortex V ell} {delta a : ℝ≥0}
    (params : SourceRandomConfigurationParameters W j delta a s)
    (L : FiniteLaw Ω) (data : Ω → D) (seed : Ω → ForbiddenFamilyOn V)
    (P : FiniteLaw D) (Q : FiniteLaw (ForbiddenFamilyOn V))
    (hind : FiniteLaw.map (fun x ↦ (data x, seed x)) L = P.jointBind (fun _ ↦ Q))
    (hQ : ∀ U, Q.probability (fun R ↦ U ⊆ R) ≤
      sourceRandomConfigurationProbability W.terminalSize delta j ^ U.card)
    (F : ForbiddenFamilyOn V) (y z : ℝ≥0) (hF : SourceVortexWellSpread W j F y z)
    (hdeltaY : delta * y ≤ W.terminalSize)
    (accepted : Ω → ForbiddenFamilyOn V)
    (hsupport : L.SupportedOn (fun x ↦ accepted x ⊆ seed x ∧ accepted x ⊆ terminalRandomConfigurations W j))
    (Bad : Ω → Prop) (epsilon rho : ℝ≥0) (hrho : 0 < rho)
    (hbad : L.probability Bad ≤ epsilon)
    (hbudget : sourceRandomFailureCoefficient W j * ((2 : ℝ≥0) ^ s)⁻¹ + epsilon / rho < 1) :
    ∃ R : ForbiddenFamilyOn V, ∃ M : FiniteLaw Ω,
      R ⊆ terminalRandomConfigurations W j ∧
      SourceVortexWellSpread W j (F ∪ R) (y + a) (z + 3 * a) ∧
      SourceAugmentationCounts j W.terminalSize F R a ∧
      FiniteLaw.map data M = P ∧
      M.SupportedOn (fun x ↦ accepted x ⊆ R) ∧
      (∀ A : Ω → Prop, L.SupportedOn A → M.SupportedOn A) ∧
      M.probability Bad < rho := by
  classical
  obtain ⟨r, hr, hg, hdata, hseed, hfail⟩ := FiniteLaw.exists_fixed_independent_seed L data seed P Q hind
    Bad (fun R ↦ SourceRandomCountsGood W j F a (configurationEnvelopeBits R))
    epsilon (sourceRandomFailureCoefficient W j * ((2 : ℝ≥0) ^ s)⁻¹) rho hrho hbad
    (configurationEnvelope_goodCounts_failure params Q hQ F y z hF hdeltaY) hbudget
  let R := sampleTerminalConfigurations W j (configurationEnvelopeBits r)
  let M := L.conditionOn (fun x ↦ seed x = r) hr
  refine ⟨R, M, ?_, hg.sourceWellSpread hF, hg.augmentationCounts, hdata, ?_, ?_, hfail⟩
  · change sampleTerminalConfigurations W j (configurationEnvelopeBits r) ⊆ _
    rw [sampleTerminalConfigurations_envelopeBits]
    exact inter_subset_left
  · intro x hx
    have haccepted := hsupport.conditionOn hr x hx
    have hsr := hseed x hx
    change accepted x ⊆ sampleTerminalConfigurations W j (configurationEnvelopeBits r)
    rw [sampleTerminalConfigurations_envelopeBits]
    exact subset_inter haccepted.2 (hsr ▸ haccepted.1)
  · intro A hA
    exact hA.conditionOn hr

end

end Erdos207
