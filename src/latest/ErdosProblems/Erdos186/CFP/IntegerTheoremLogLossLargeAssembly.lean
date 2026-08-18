/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.CenteredPreprocessingRangePackage
import ErdosProblems.Erdos186.CFP.IntegerTheoremLogLossTerminal
import ErdosProblems.Erdos186.CFP.IntegerTheoremSourcePower

/-!
# Outer assembly with the source logarithmic loss

This is the source-faithful counterpart of `IntegerTheoremLargeAssembly`.
The finite coverage theorem chooses its colour count and only then its exact
dyadic preprocessing fold.  In particular, no input-dependent retained core
or prematurely fixed fold appears in the uniform boundary.
-/

namespace Erdos186.CFP

noncomputable section

set_option autoImplicit false

/-- Uniform centered reserve coverage with the full source stability budget.

The whole-range producer is deliberately quantified over its ambient endpoint:
the finite construction first fixes its colour and density constants, then
chooses an exact dyadic fold, sets an ambient endpoint containing both the
source interval and that fold, and reconstructs retained preprocessing from
the resulting exact-fold family.  The conclusion is already a source
`FixedScaleWitness`, so the deterministic preprocessing loss and the reserve
loss are accounted for together. -/
def UniformCenteredLargeInputLogLossCoverage : Prop :=
  ∀ (D first horizonFactor propernessDenominator C0
      horizonCoefficient : ℕ) (eta : ℝ),
    3 ≤ D → 0 < first → 0 < horizonFactor →
    0 < propernessDenominator → 0 < C0 →
    0 < horizonCoefficient → 0 < eta → eta < 1 →
    ∃ scaleNum scaleDen lossCoefficient cutoff : ℕ,
      0 < scaleNum ∧ 0 < scaleDen ∧ scaleNum ≤ scaleDen ∧
      0 < lossCoefficient ∧ 2 ≤ cutoff ∧
      ∀ {A : Finset ℤ} {n s : ℕ},
        A.Nonempty → cutoff ≤ A.card →
        A ⊆ Finset.Icc 1 (n : ℤ) →
        n + 1 ≤ A.card ^ horizonCoefficient →
        n ≤ s ^ (D - 2) →
        Real.rpow (A.card : ℝ) eta ≤ (s : ℝ) →
        (scaleDen : ℝ) * (s : ℝ) *
              Real.logb 2 (A.card : ℝ) ≤
            (scaleNum : ℝ) * (A.card : ℝ) →
        (∀ {N low high : ℕ},
          insert 0 A ⊆ Finset.Icc (0 : ℤ) ((N : ℤ) - 1) →
          PreprocessingBilu.DyadicRangeWindow N low high first
              horizonFactor D propernessDenominator →
            PreprocessingBilu.DyadicRangeSourceHApproximationFamily
              (insert 0 A) low high D 1
                (PreprocessingBilu.preprocessingScaleDen
                  propernessDenominator)) →
        ∃ k loss : ℕ,
          Nonempty (FixedScaleWitness
            (integerPoints (insert 0 A)) s D k loss scaleNum scaleDen) ∧
          loss ≤ lossCoefficient * s * (Nat.log 2 A.card + 1)

/-- Bilu--Freiman plus the concrete centered log-loss reserve theorem gives
the exact large-input endpoint consumed by
`nonemptyIntegerTheorem15_of_largeInputLogLoss`. -/
theorem largeInputLogLossNonemptyIntegerTheorem15_of_biluFreiman_of_centeredCoverage
    (hBF : BiluFreiman.BiluFreimanStatement)
    (hcoverage : UniformCenteredLargeInputLogLossCoverage) :
    LargeInputLogLossNonemptyIntegerTheorem15 := by
  intro beta eta hbeta heta heta1
  obtain ⟨betaNat, hbetaNat, hbetaLe⟩ :=
    IntegerTheoremAssembly.exists_natExponent_ge beta hbeta
  obtain ⟨D₀, hD₀, hbetaD₀⟩ :=
    IntegerTheoremAssembly.exists_natRank_ge_exponentRatio beta eta heta
  let D : ℕ := D₀ + 1
  have hD : 3 ≤ D := by dsimp only [D]; omega
  obtain ⟨first, horizonFactor, propernessDenominator, C0,
      hfirst, hhorizonFactor, hpropernessDenominator, hC0, _hC0eq,
      _hpreprocessingPackage, hrangePackage⟩ :=
    PreprocessingBilu.exists_retainedDyadicPreprocessingAndRangePackage_of_biluFreiman
      hBF D (by omega)
  let horizonCoefficient := betaNat + 1
  have hhorizonCoefficient : 0 < horizonCoefficient := by
    dsimp only [horizonCoefficient]
    omega
  obtain ⟨scaleNum, scaleDen, lossCoefficient, cutoff,
      hscaleNum, hscaleDen, hscale, hlossCoefficient, hcutoff, hcover⟩ :=
    hcoverage D first horizonFactor propernessDenominator C0
      horizonCoefficient eta hD hfirst hhorizonFactor
      hpropernessDenominator hC0 hhorizonCoefficient heta heta1
  refine ⟨scaleNum, scaleDen, D, lossCoefficient, cutoff,
    hscaleNum, hscaleDen, hscale, hlossCoefficient, hcutoff, ?_⟩
  intro n A s hA hcutoffA hAinterval hn hslow hscaleCard
  have hcardPos : 0 < A.card := hA.card_pos
  have hcardTwo : 2 ≤ A.card := hcutoff.trans hcutoffA
  have hnNat : n ≤ A.card ^ betaNat :=
    IntegerTheoremAssembly.sourceEndpoint_le_card_pow_nat
      hcardPos hbetaLe hn
  have hnSucc : n + 1 ≤ A.card ^ horizonCoefficient := by
    dsimp only [horizonCoefficient]
    calc
      n + 1 ≤ A.card ^ betaNat + 1 := Nat.add_le_add_right hnNat 1
      _ ≤ A.card ^ betaNat * A.card := by
        have hp : 1 ≤ A.card ^ betaNat := by
          exact Nat.one_le_iff_ne_zero.mpr
            (pow_ne_zero _ (Nat.ne_of_gt hcardPos))
        calc
          A.card ^ betaNat + 1 ≤
              A.card ^ betaNat + A.card ^ betaNat :=
            Nat.add_le_add_left hp _
          _ = A.card ^ betaNat * 2 := by ring
          _ ≤ A.card ^ betaNat * A.card :=
            Nat.mul_le_mul_left _ hcardTwo
      _ = A.card ^ (betaNat + 1) := (pow_succ _ _).symm
  have hnScalePower₀ : n ≤ s ^ (D₀ - 1) :=
    IntegerTheoremAssembly.sourceEndpoint_le_scale_pow
      (show 1 ≤ A.card by omega) hbetaD₀ hn hslow
  have hnScalePower : n ≤ s ^ (D - 2) := by
    have hsub : D - 2 = D₀ - 1 := by dsimp only [D]; omega
    simpa only [hsub] using hnScalePower₀
  have hfamilies : ∀ {N low high : ℕ},
      insert 0 A ⊆ Finset.Icc (0 : ℤ) ((N : ℤ) - 1) →
      PreprocessingBilu.DyadicRangeWindow N low high first horizonFactor D
          propernessDenominator →
        PreprocessingBilu.DyadicRangeSourceHApproximationFamily
          (insert 0 A) low high D 1
            (PreprocessingBilu.preprocessingScaleDen
              propernessDenominator) := by
    intro N low high hanchored hwindow
    exact hrangePackage (Finset.mem_insert_self 0 A) hanchored hwindow
  obtain ⟨k, loss, hW, hloss⟩ :=
    hcover hA hcutoffA hAinterval hnSucc hnScalePower hslow
      hscaleCard hfamilies
  have hzeroA : 0 ∉ A :=
    IntegerTheoremAssembly.zero_not_mem_of_subset_Icc_one hAinterval
  let W := Classical.choice hW
  let Wsource : FixedScaleWitness (integerPoints A) s D k loss
      scaleNum scaleDen := W.eraseZero_stabilityIntegerPoints hzeroA
  exact ⟨k, loss, ⟨Wsource⟩, hloss⟩

end

end Erdos186.CFP

#print axioms
  Erdos186.CFP.largeInputLogLossNonemptyIntegerTheorem15_of_biluFreiman_of_centeredCoverage
