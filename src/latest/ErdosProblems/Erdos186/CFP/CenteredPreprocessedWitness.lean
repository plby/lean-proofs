/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.CenteredIdentification
import ErdosProblems.Erdos186.CFP.PreprocessedWitness

/-!
# Centered preprocessing to the fixed-scale CFP witness

The random-partition and generator-completion stages use coordinates based
at the source origin.  This module is the terminal preprocessing adapter for
that choice: it invokes the centered form of Lemma 2.38 and passes its actual
strong-stability output to the concrete reserve/coverage constructor.
-/

namespace Erdos186.CFP

noncomputable section

/-- Post-preprocessing reserve/coverage boundary for centered canonical
coordinates.  Its conclusion is the same concrete finite certificate as in
`PreprocessedReserveCoverageInput`; only the stability map is corrected to
send the distinguished source origin to the lattice origin. -/
abbrev CenteredPreprocessedReserveCoverageInput (A : Finset ℤ)
    (stableBudget D n C0 s extraLoss scaleNum scaleDen : ℕ) : Prop :=
  ∀ (W B : Finset ℤ) (relevant : Finset ℕ)
    (hproper : Stability.RelevantBoxesProper W relevant),
    B ⊆ W → W ⊆ A → 0 ∈ B →
    Stability.StronglyStableFor B (Stability.minimalBoxFamily W)
      stableBudget D (n ^ 2) relevant
      (Stability.centeredMinimalIdentificationFamily hproper) C0 →
    Stability.WeaklyStableMinimalFor B stableBudget D n →
    Nonempty
      (PreprocessedReserveCertificate B s D extraLoss scaleNum scaleDen)

/-- Join centered HApproximation preprocessing to its concrete post-random
reserve/coverage certificate. -/
theorem exists_fixedScaleWitness_of_centeredPreprocessing
    {A : Finset ℤ}
    {stableBudget D n C0 preprocessingScaleNum preprocessingScaleDen
      s extraLoss scaleNum scaleDen : ℕ}
    (hzero : 0 ∈ A) (hC0 : 0 < C0)
    (hA : ∀ z ∈ A, 0 ≤ z ∧ z < (n : ℤ))
    (happrox : PreprocessingBilu.PreprocessingHApproximationArgument A
      stableBudget D n C0 preprocessingScaleNum preprocessingScaleDen)
    (hcoverage : CenteredPreprocessedReserveCoverageInput A stableBudget D n C0
      s extraLoss scaleNum scaleDen) :
    ∃ k, Nonempty
      (FixedScaleWitness (Stability.integerPoints A) s D k
        (preprocessingCardinalityLoss A stableBudget D + extraLoss)
        scaleNum scaleDen) := by
  obtain ⟨W, B, relevant, hproper, hBW, hWA, hzeroB, hcard, hstable⟩ :=
    Preprocessing.preprocessing_lemma238_centered hzero hC0 hA happrox
  have hcanonical :
      Stability.WeaklyStableMinimalFor B stableBudget D n :=
    Greedy.weaklyStableMinimalFor_of_fixed_minimalBox hBW hstable.weaklyStable
  let C := Classical.choice
    (hcoverage W B relevant hproper hBW hWA hzeroB hstable hcanonical)
  refine ⟨C.k, ⟨C.fixed (hBW.trans hWA) ?_⟩⟩
  simpa only [preprocessingCardinalityLoss, Nat.add_assoc] using hcard

/-- Uniform Bilu--Freiman constructor with centered coordinates throughout
the span-pruning, random-partition, and generator-completion handoff. -/
theorem exists_uniform_centeredPreprocessedFixedScaleWitness_of_biluFreiman
    (hBF : BiluFreiman.BiluFreimanStatement)
    (D : ℕ) (hD : 2 ≤ D)
    (s extraLoss scaleNum scaleDen : ℕ) :
    ∃ first horizonFactor propernessDenominator C0 : ℕ,
      0 < first ∧ 0 < horizonFactor ∧ 0 < propernessDenominator ∧
      0 < C0 ∧
      C0 = PreprocessingBilu.preprocessingRobustnessDenominator D
        propernessDenominator ∧
      ∀ {A : Finset ℤ} {n h last stableBudget : ℕ},
        0 ∈ A →
        A ⊆ Finset.Icc (0 : ℤ) ((n : ℤ) - 1) →
        h = horizonFactor * 2 ^ last →
        h ≤ n →
        n ≤ h ^ (D - 1) →
        first < last →
        (2 * D + 1) * first +
            2 * horizonFactor * (D - 1) < last →
        PreprocessingBilu.preprocessingIndexBound D
            propernessDenominator ≤ h →
        CenteredPreprocessedReserveCoverageInput A stableBudget D n C0 s
          extraLoss scaleNum scaleDen →
        ∃ k, Nonempty
          (FixedScaleWitness (Stability.integerPoints A) s D k
            (preprocessingCardinalityLoss A stableBudget D + extraLoss)
            scaleNum scaleDen) := by
  obtain ⟨first, horizonFactor, propernessDenominator, C0, hfirst,
      hhorizon, hdenominator, hC0, hC0eq, happrox⟩ :=
    PreprocessingBilu.exists_preprocessingHApproximationArgument_of_biluFreiman
      hBF D hD
  refine ⟨first, horizonFactor, propernessDenominator, C0, hfirst,
    hhorizon, hdenominator, hC0, hC0eq, ?_⟩
  intro A n h last stableBudget hzero hinterval hh hhle hnpower
    hfirstLast hlastLarge hlarge hcoverage
  apply exists_fixedScaleWitness_of_centeredPreprocessing
    (A := A) (stableBudget := stableBudget) (D := D) (n := n) (C0 := C0)
    (preprocessingScaleNum := 1)
    (preprocessingScaleDen :=
      PreprocessingBilu.preprocessingScaleDen propernessDenominator)
    (s := s) (extraLoss := extraLoss) (scaleNum := scaleNum)
    (scaleDen := scaleDen)
    hzero hC0
  · intro z hz
    have hzIcc := Finset.mem_Icc.mp (hinterval hz)
    exact ⟨hzIcc.1, by omega⟩
  · exact happrox hzero hinterval hh hhle hnpower hfirstLast hlastLarge hlarge
  · exact hcoverage

end

end Erdos186.CFP

#print axioms Erdos186.CFP.exists_fixedScaleWitness_of_centeredPreprocessing
#print axioms
  Erdos186.CFP.exists_uniform_centeredPreprocessedFixedScaleWitness_of_biluFreiman
