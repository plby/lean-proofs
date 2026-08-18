/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.CenteredPreprocessingSource

/-!
# One Bilu package for preprocessing and every color scale

The final construction uses one retained approximation scale for the
preprocessed core and a whole exact-dyadic range for the independently run
colors.  This module keeps both outputs under the same uniform Bilu--Freiman
constants, in particular the same scale denominator.
-/

namespace Erdos186.CFP.PreprocessingBilu

open Erdos186.CFP

noncomputable section

/-- A retained single-fold package supplies the exact dyadic family on any
numerical range lying in its source window. -/
theorem dyadicRangeSourceHApproximationFamily_of_retainedPackage
    {first horizonFactor propernessDenominator C0 D : ℕ}
    (hhorizonFactor : 0 < horizonFactor)
    (hpackage :
      ∀ {A : Finset ℤ} {n horizon fold last stableBudget : ℕ},
        0 ∈ A →
        A ⊆ Finset.Icc (0 : ℤ) ((n : ℤ) - 1) →
        horizon = horizonFactor * 2 ^ last →
        horizon ≤ fold →
        fold < horizonFactor * 2 ^ (last + 1) →
        fold ≤ n →
        n ≤ horizon ^ (D - 1) →
        first < last →
        (2 * D + 1) * first +
            2 * horizonFactor * (D - 1) < last →
        preprocessingIndexBound D propernessDenominator ≤ fold →
        RetainedDyadicPreprocessingHApproximationArgument A stableBudget D n
            C0 1 (preprocessingScaleDen propernessDenominator) fold ∧
          DyadicSourceHApproximationFamily A fold D 1
            (preprocessingScaleDen propernessDenominator))
    {A : Finset ℤ} {n low high : ℕ}
    (hzero : 0 ∈ A)
    (hA : A ⊆ Finset.Icc (0 : ℤ) ((n : ℤ) - 1))
    (hwindow : DyadicRangeWindow n low high first horizonFactor D
      propernessDenominator) :
    DyadicRangeSourceHApproximationFamily A low high D 1
      (preprocessingScaleDen propernessDenominator) := by
  intro level hlow hhigh
  let offset := Nat.clog 2 horizonFactor
  let last := level - offset
  let horizon := horizonFactor * 2 ^ last
  have hoffsetLevel : offset ≤ level :=
    hwindow.offset_le_low.trans hlow
  have hlevel : offset + last = level := by
    dsimp only [last]
    exact Nat.add_sub_of_le hoffsetLevel
  have hdyadic := dyadicFold_window (last := last) hhorizonFactor
  have hhorizonFold : horizon ≤ 2 ^ level := by
    rw [← hlevel]
    simpa only [pow_add, horizon, offset] using hdyadic.1
  have hfoldUpper : 2 ^ level < horizonFactor * 2 ^ (last + 1) := by
    rw [← hlevel]
    simpa only [pow_add, offset] using hdyadic.2
  have hresult := hpackage (A := A) (n := n) (horizon := horizon)
    (fold := 2 ^ level) (last := last) (stableBudget := 0)
    hzero hA rfl hhorizonFold hfoldUpper
    (hwindow.fold_le_n level hlow hhigh)
    (by simpa only [horizon, last, offset] using
      hwindow.n_le_horizon_pow level hlow hhigh)
    (by simpa only [last, offset] using
      hwindow.first_lt_last level hlow hhigh)
    (by simpa only [last, offset] using
      hwindow.last_large level hlow hhigh)
    (hwindow.index_le_fold level hlow hhigh)
  intro S hSA hzeroS hnontrivial
  exact hresult.2 hSA hzeroS hnontrivial

/-- Bilu--Freiman constants shared by retained centered preprocessing and
every color-dependent exact dyadic scale. -/
theorem exists_retainedDyadicPreprocessingAndRangePackage_of_biluFreiman
    (hBF : BiluFreiman.BiluFreimanStatement) (D : ℕ) (hD : 2 ≤ D) :
    ∃ first horizonFactor propernessDenominator C0 : ℕ,
      0 < first ∧ 0 < horizonFactor ∧ 0 < propernessDenominator ∧
      0 < C0 ∧
      C0 = preprocessingRobustnessDenominator D propernessDenominator ∧
      (∀ {A : Finset ℤ} {n horizon fold last stableBudget : ℕ},
        0 ∈ A →
        A ⊆ Finset.Icc (0 : ℤ) ((n : ℤ) - 1) →
        horizon = horizonFactor * 2 ^ last →
        horizon ≤ fold →
        fold < horizonFactor * 2 ^ (last + 1) →
        fold ≤ n →
        n ≤ horizon ^ (D - 1) →
        first < last →
        (2 * D + 1) * first +
            2 * horizonFactor * (D - 1) < last →
        preprocessingIndexBound D propernessDenominator ≤ fold →
        RetainedDyadicPreprocessingHApproximationArgument A stableBudget D n
            C0 1 (preprocessingScaleDen propernessDenominator) fold ∧
          DyadicSourceHApproximationFamily A fold D 1
            (preprocessingScaleDen propernessDenominator)) ∧
      (∀ {A : Finset ℤ} {n low high : ℕ},
        0 ∈ A →
        A ⊆ Finset.Icc (0 : ℤ) ((n : ℤ) - 1) →
        DyadicRangeWindow n low high first horizonFactor D
          propernessDenominator →
        DyadicRangeSourceHApproximationFamily A low high D 1
          (preprocessingScaleDen propernessDenominator)) := by
  obtain ⟨first, horizonFactor, propernessDenominator, C0,
      hfirst, hhorizonFactor, hpropernessDenominator, hC0, hC0eq,
      hpackage⟩ :=
    exists_retainedDyadicPreprocessingPackage_of_biluFreiman hBF D hD
  refine ⟨first, horizonFactor, propernessDenominator, C0,
    hfirst, hhorizonFactor, hpropernessDenominator, hC0, hC0eq,
    hpackage, ?_⟩
  intro A n low high hzero hA hwindow
  exact dyadicRangeSourceHApproximationFamily_of_retainedPackage
    hhorizonFactor hpackage hzero hA hwindow

end

end Erdos186.CFP.PreprocessingBilu

#print axioms
  Erdos186.CFP.PreprocessingBilu.exists_retainedDyadicPreprocessingAndRangePackage_of_biluFreiman
