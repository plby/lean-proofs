/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceRegularizationAugmentation
import ErdosProblems.Erdos207.FiniteFailureCombination

/-! # Simultaneous degree regularity and source well-spreadness -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I] [Nonempty I] {ell j s : ℕ}
  {W : Vortex V ell} {delta a : ℝ≥0}

theorem regularizationProcessLaw_gap_source_failure
    (P : SourceRandomConfigurationParameters W j delta a s)
    (G0 H0 : Finset (Finset I)) (hGH : G0 ⊆ H0) (hk : 2 ≤ j - 2)
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
    ((regularizationProcessLaw G0 H0 hGH hk hsize b).probability (fun S ↦ ¬
      (finiteHypergraphDegreeGap (regularizationCurrentFamily G0 S) ≤ b ∧
       SourceVortexWellSpread W j (F ∪ regularizationImageEdges e S) (y + a) (z + 3 * a))) : ℝ) ≤
      finiteHypergraphDegreeGap G0 * (2 * Fintype.card I * Real.exp (-(b : ℝ) / 8192)) +
      (sourceRandomFailureCoefficient W j : ℝ) * ((2 : ℝ) ^ s)⁻¹ := by
  apply finiteLaw_failure_and_le
    (regularizationProcessLaw G0 H0 hGH hk hsize b)
    (fun S ↦ finiteHypergraphDegreeGap (regularizationCurrentFamily G0 S) ≤ b)
    (fun S ↦ SourceVortexWellSpread W j (F ∪ regularizationImageEdges e S) (y + a) (z + 3 * a))
  · simpa only [not_le] using regularizationProcessLaw_gap_failure G0 H0 hGH hk hsize hdensity b
  · exact_mod_cast regularizationProcessLaw_source_augmentation_failure P G0 H0 hGH hk hsize hdensity
      b e hbad hprob F y z hF hdeltaY

theorem exists_source_regularizing_augmentation
    (P : SourceRandomConfigurationParameters W j delta a s)
    (G0 H0 : Finset (Finset I)) (hGH : G0 ⊆ H0) (hk : 2 ≤ j - 2)
    (hsize : 16 * 2 ^ (j - 2 - 1) * (j - 2 - 1) ≤ Fintype.card I)
    (hdensity : (2 : ℝ≥0) ^ (j - 2) * finiteHypergraphMaxDegree H0 ≤
      (1 / 36 : ℝ≥0) * Nat.choose (Fintype.card I) (j - 2 - 1))
    (b : ℕ) (e : I ↪ TripleOn V)
    (hbad : ∀ E : Finset I, E.card = j - 2 →
      E.map e ∉ terminalRandomConfigurations W j → E ∈ H0)
    (hprob : 2 * regularizationBaseHazard G0 (j - 2) ≤
      sourceRandomConfigurationProbability W.terminalSize delta j)
    (F : ForbiddenFamilyOn V) (y z : ℝ≥0) (hF : SourceVortexWellSpread W j F y z)
    (hdeltaY : delta * y ≤ W.terminalSize)
    (hsmall : finiteHypergraphDegreeGap G0 * (2 * Fintype.card I * Real.exp (-(b : ℝ) / 8192)) +
      (sourceRandomFailureCoefficient W j : ℝ) * ((2 : ℝ) ^ s)⁻¹ < 1) :
    ∃ R : Finset (Finset I),
      Disjoint R H0 ∧ (∀ E ∈ R, E.card = j - 2) ∧
      R.image (Finset.map e) ⊆ terminalRandomConfigurations W j ∧
      finiteHypergraphMaxDegree (G0 ∪ R) ≤ 9 * finiteHypergraphMaxDegree G0 ∧
      finiteHypergraphDegreeGap (G0 ∪ R) ≤ b ∧
      SourceVortexWellSpread W j (F ∪ R.image (Finset.map e)) (y + a) (z + 3 * a) := by
  let L := regularizationProcessLaw G0 H0 hGH hk hsize b
  let Good := fun S : HypergraphRegularizationState I (j - 2) ↦
    finiteHypergraphDegreeGap (regularizationCurrentFamily G0 S) ≤ b ∧
    SourceVortexWellSpread W j (F ∪ regularizationImageEdges e S) (y + a) (z + 3 * a)
  have hfail : (L.probability (fun S ↦ ¬ Good S) : ℝ) < 1 :=
    (regularizationProcessLaw_gap_source_failure P G0 H0 hGH hk hsize hdensity
      b e hbad hprob F y z hF hdeltaY).trans_lt hsmall
  have hpos : 0 < L.probability Good := by
    by_contra hnot
    have hz : L.probability Good = 0 := le_antisymm (not_lt.mp hnot) zero_le
    rw [L.probability_not Good, hz, tsub_zero] at hfail
    norm_num at hfail
  obtain ⟨S, hmass, hgood⟩ := L.exists_supported_of_probability_pos hpos
  have hs := regularizationProcessLaw_avoids_and_bounded G0 H0 hGH hk hsize hdensity b S hmass
  exact ⟨regularizationAcceptedEdges S, hs.1, hs.2.1,
    regularizationImageEdges_subset_of_avoid e (terminalRandomConfigurations W j) H0 S hs.1 hbad,
    hs.2.2, hgood.1, hgood.2⟩

end

end Erdos207
