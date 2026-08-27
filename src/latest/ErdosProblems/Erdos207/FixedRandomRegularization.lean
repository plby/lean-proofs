/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.RandomRegularizationEnvelope

/-! # A fixed source envelope for actual regularization over random prior data -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem exists_fixed_random_regularization
    {D V : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
    {I : D → Type*} [∀ d, Fintype (I d)] [∀ d, DecidableEq (I d)] [∀ d, Nonempty (I d)]
    {ell j s : ℕ} {W : Vortex V ell} {delta a : ℝ≥0}
    (params : SourceRandomConfigurationParameters W j delta a s)
    (P : FiniteLaw D) (e : (d : D) → I d ↪ TripleOn V)
    (G H : (d : D) → Finset (Finset (I d))) (hGH : ∀ d, G d ⊆ H d)
    (hsize : ∀ d, 16 * 2 ^ (j - 2 - 1) * (j - 2 - 1) ≤ Fintype.card (I d))
    (hdensity : ∀ d, (2 : ℝ≥0) ^ (j - 2) * finiteHypergraphMaxDegree (H d) ≤
      (1 / 36 : ℝ≥0) * Nat.choose (Fintype.card (I d)) (j - 2 - 1))
    (beta : ℝ≥0) (hbeta : ∀ d, regularizationBaseHazard (G d) (j - 2) ≤ beta)
    (hsource : 2 * beta ≤ sourceRandomConfigurationProbability W.terminalSize delta j)
    (b t : ℕ) (ht : ∀ d, finiteHypergraphDegreeGap (G d) ≤ t)
    (C : ForbiddenFamilyOn V) (hC : C ⊆ terminalRandomConfigurations W j)
    (hblocked : ∀ d (E : Finset (I d)), E.card = j - 2 → E.map (e d) ∉ C → E ∈ H d)
    (F : ForbiddenFamilyOn V) (y z : ℝ≥0) (hF : SourceVortexWellSpread W j F y z)
    (hdeltaY : delta * y ≤ W.terminalSize)
    (epsilon rho : ℝ≥0) (hrho : 0 < rho)
    (hepsilon : ∀ d, (finiteHypergraphDegreeGap (G d) : ℝ) *
      (2 * Fintype.card (I d) * Real.exp (-(b : ℝ) / 8192)) ≤ epsilon)
    (hbudget : sourceRandomFailureCoefficient W j * ((2 : ℝ≥0) ^ s)⁻¹ + epsilon / rho < 1) :
    ∃ R : ForbiddenFamilyOn V,
    ∃ M : FiniteLaw (D × (ForbiddenFamilyOn V × ForbiddenFamilyOn V)),
      R ⊆ C ∧
      SourceVortexWellSpread W j (F ∪ R) (y + a) (z + 3 * a) ∧
      SourceAugmentationCounts j W.terminalSize F R a ∧
      FiniteLaw.map Prod.fst M = P ∧
      M.SupportedOn (fun x ↦ x.2.2 ⊆ R) ∧
      M.probability (fun x ↦ ¬ RegularizationOutputWitness (e x.1) (G x.1) (H x.1) (j - 2) b x.2.2) < rho := by
  have hk : 2 ≤ j - 2 := by have := params.order; omega
  let L := randomRegularizationEnvelopeLaw P e G H hGH hk hsize beta hbeta b t
  let Q : FiniteLaw (ForbiddenFamilyOn V) := geometricConfigurationEnvelopeLaw beta t
  have hjoint : ∀ U, Q.probability (fun R ↦ U ⊆ R) ≤
      sourceRandomConfigurationProbability W.terminalSize delta j ^ U.card := by
    intro U
    exact (geometricConfigurationEnvelopeLaw_joint_inclusion beta t U).trans
      (pow_le_pow_left' hsource U.card)
  obtain ⟨R, M, hRC, hspread, hcounts, hdata, hsupport, _, hfail⟩ :=
    exists_fixed_shell_source_envelope params L Prod.fst (fun x ↦ x.2.1) P Q
      (randomRegularizationEnvelopeLaw_independent P e G H hGH hk hsize beta hbeta b t)
      hjoint F y z hF hdeltaY C hC (fun x ↦ x.2.2)
      (randomRegularizationEnvelopeLaw_supported P e G H hGH hk hsize beta hbeta b t ht hdensity C hblocked)
      (fun x ↦ ¬ RegularizationOutputWitness (e x.1) (G x.1) (H x.1) (j - 2) b x.2.2)
      epsilon rho hrho
      (randomRegularizationEnvelopeLaw_failure P e G H hGH hk hsize beta hbeta b t ht hdensity epsilon hepsilon)
      hbudget
  exact ⟨R, M, hRC, hspread, hcounts, hdata, hsupport, hfail⟩

end

end Erdos207
