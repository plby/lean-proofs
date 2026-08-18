/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.CenteredPreprocessedWitness
import ErdosProblems.Erdos186.CFP.IntegerTheoremTerminal

/-!
# Outer assembly of the large-input integer CFP theorem

This file performs every source-facing uniform choice around the concrete
random-partition/dense-box construction.  The sole remaining combinatorial
callback is a centered post-preprocessing reserve certificate.  In
particular, the Bilu--Freiman horizon, natural source exponent, stable
deletion budget, scale constants, input cutoff, and final loss coefficient
are all selected before the input set.
-/

namespace Erdos186.CFP

noncomputable section

/-- The exact remaining centered reserve-coverage theorem after all outer
parameters relevant to it have been fixed.  Its hypotheses are properties
of the current source input that are proved internally by the terminal
assembly below. -/
def UniformCenteredLargeInputCoverage : Prop :=
  ∀ (D C0 horizonCoefficient : ℕ) (eta : ℝ),
    2 ≤ D → 0 < C0 → 0 < eta → eta < 1 →
    ∃ scaleNum scaleDen extraLossCoefficient cutoff : ℕ,
      0 < scaleNum ∧ 0 < scaleDen ∧ scaleNum ≤ scaleDen ∧
      2 ≤ cutoff ∧
      ∀ {A : Finset ℤ} {h s : ℕ},
        A.Nonempty → cutoff ≤ A.card →
        A ⊆ Finset.Icc 1 ((h : ℤ) - 1) →
        Nat.log 2 h + 1 ≤
          horizonCoefficient * (Nat.log 2 A.card + 1) →
        Real.rpow (A.card : ℝ) eta ≤ (s : ℝ) →
        (scaleDen : ℝ) * (s : ℝ) *
              Real.logb 2 (A.card : ℝ) ≤
            (scaleNum : ℝ) * (A.card : ℝ) →
        CenteredPreprocessedReserveCoverageInput (insert 0 A)
          (s / (Nat.log 2 A.card + 1)) D h C0 s
          (extraLossCoefficient * s) scaleNum scaleDen

/-- Bilu--Freiman plus the concrete centered reserve-coverage theorem gives
the exact large-input endpoint used by `nonemptyIntegerTheorem15_of_largeInput`.
No horizon, approximation-family, coloring, or numerical premise remains at
the `LargeInputNonemptyIntegerTheorem15` boundary. -/
theorem largeInputNonemptyIntegerTheorem15_of_biluFreiman_of_centeredCoverage
    (hBF : BiluFreiman.BiluFreimanStatement)
    (hcoverage : UniformCenteredLargeInputCoverage) :
    LargeInputNonemptyIntegerTheorem15 := by
  intro beta eta hbeta heta heta1
  obtain ⟨betaNat, hbetaNat, hbetaLe⟩ :=
    IntegerTheoremAssembly.exists_natExponent_ge beta hbeta
  let D : ℕ := 2
  have hD : 2 ≤ D := by simp [D]
  obtain ⟨first, horizonFactor, propernessDenominator, C0,
      hfirst, hhorizonFactor, hpropernessDenominator, hC0, hC0eq,
      happrox⟩ :=
    PreprocessingBilu.exists_preprocessingHApproximationArgument_of_biluFreiman
      hBF D hD
  let indexBound :=
    PreprocessingBilu.preprocessingIndexBound D propernessDenominator
  let horizonCoefficient :=
    IntegerTheoremAssembly.preprocessingHorizonLogCoefficient
      first horizonFactor D indexBound betaNat
  obtain ⟨scaleNum, scaleDen, extraLossCoefficient, cutoff,
      hscaleNum, hscaleDen, hscale, hcutoff, hcover⟩ :=
    hcoverage D C0 horizonCoefficient eta hD hC0 heta heta1
  let preprocessingLossCoefficient :=
    6 * D * horizonCoefficient + 1
  let lossCoefficient := preprocessingLossCoefficient + extraLossCoefficient
  have hlossCoefficient : 0 < lossCoefficient := by
    dsimp only [lossCoefficient, preprocessingLossCoefficient]
    omega
  refine ⟨scaleNum, scaleDen, D, lossCoefficient, cutoff,
    hscaleNum, hscaleDen, hscale, hlossCoefficient, hcutoff, ?_⟩
  intro n A s hA hcutoffA hAinterval hn hslow hscaleCard
  have hcardPos : 0 < A.card := hA.card_pos
  have hnNat : n ≤ A.card ^ betaNat :=
    IntegerTheoremAssembly.sourceEndpoint_le_card_pow_nat
      hcardPos hbetaLe hn
  obtain ⟨last, h, hh, hnh, hindex, hfirstLast, hlastLarge, hlog⟩ :=
    IntegerTheoremAssembly.exists_preprocessingDyadicHorizon_with_logBound
      first horizonFactor D n indexBound betaNat A.card
      hhorizonFactor (by omega) hnNat
  have hhpos : 0 < h := by
    rw [hh]
    exact Nat.mul_pos hhorizonFactor (by positivity)
  have hhpower : h ≤ h ^ (D - 1) :=
    (IntegerTheoremAssembly.preprocessingHorizon_powerBounds hhpos hD).2
  have hanchoredInterval : insert 0 A ⊆
      Finset.Icc (0 : ℤ) ((h : ℤ) - 1) :=
    IntegerTheoremAssembly.insert_zero_subset_preprocessingInterval
      hAinterval hnh
  have hsourceInterval : A ⊆ Finset.Icc 1 ((h : ℤ) - 1) := by
    intro z hz
    have hzSource := Finset.mem_Icc.mp (hAinterval hz)
    have hnhInt : (n : ℤ) < (h : ℤ) := by exact_mod_cast hnh
    exact Finset.mem_Icc.mpr ⟨hzSource.1, by omega⟩
  let stableBudget := s / (Nat.log 2 A.card + 1)
  have hpreprocessing :
      PreprocessingBilu.PreprocessingHApproximationArgument
        (insert 0 A) stableBudget D h C0 1
          (PreprocessingBilu.preprocessingScaleDen propernessDenominator) := by
    apply happrox (A := insert 0 A) (n := h) (h := h) (last := last)
      (stableBudget := stableBudget)
    · exact Finset.mem_insert_self 0 A
    · exact hanchoredInterval
    · exact hh
    · exact le_rfl
    · exact hhpower
    · exact hfirstLast
    · exact hlastLarge
    · simpa only [indexBound] using hindex
  have hconcreteCoverage : CenteredPreprocessedReserveCoverageInput
      (insert 0 A) stableBudget D h C0 s
        (extraLossCoefficient * s) scaleNum scaleDen := by
    apply hcover hA hcutoffA hsourceInterval hlog hslow hscaleCard
  have hanchoredBounds : ∀ z ∈ insert 0 A, 0 ≤ z ∧ z < (h : ℤ) := by
    intro z hz
    have hzIcc := Finset.mem_Icc.mp (hanchoredInterval hz)
    exact ⟨hzIcc.1, by omega⟩
  obtain ⟨k, hW⟩ := exists_fixedScaleWitness_of_centeredPreprocessing
    (A := insert 0 A) (stableBudget := stableBudget) (D := D) (n := h)
    (C0 := C0) (preprocessingScaleNum := 1)
    (preprocessingScaleDen :=
      PreprocessingBilu.preprocessingScaleDen propernessDenominator)
    (s := s) (extraLoss := extraLossCoefficient * s)
    (scaleNum := scaleNum) (scaleDen := scaleDen)
    (Finset.mem_insert_self 0 A) hC0 hanchoredBounds hpreprocessing
    hconcreteCoverage
  let W := Classical.choice hW
  have hzeroA : 0 ∉ A :=
    IntegerTheoremAssembly.zero_not_mem_of_subset_Icc_one hAinterval
  let Wsource : FixedScaleWitness (integerPoints A) s D k
      (preprocessingCardinalityLoss (insert 0 A) stableBudget D +
        extraLossCoefficient * s) scaleNum scaleDen :=
    W.eraseZero_stabilityIntegerPoints hzeroA
  refine ⟨k,
    preprocessingCardinalityLoss (insert 0 A) stableBudget D +
      extraLossCoefficient * s,
    ⟨Wsource⟩, ?_⟩
  have hpreLoss :
      preprocessingCardinalityLoss (insert 0 A) stableBudget D ≤
        preprocessingLossCoefficient * s := by
    apply preprocessingCardinalityLoss_le_scale
      (A := insert 0 A) (n := h) (m := A.card)
      (s := s) (D := D) (horizonCoefficient := horizonCoefficient)
    · exact Finset.mem_insert_self 0 A
    · exact hanchoredBounds
    · exact hlog
  calc
    preprocessingCardinalityLoss (insert 0 A) stableBudget D +
          extraLossCoefficient * s ≤
        preprocessingLossCoefficient * s + extraLossCoefficient * s :=
      Nat.add_le_add_right hpreLoss _
    _ = lossCoefficient * s := by
      dsimp only [lossCoefficient]
      ring

end

end Erdos186.CFP

#print axioms
  Erdos186.CFP.largeInputNonemptyIntegerTheorem15_of_biluFreiman_of_centeredCoverage
