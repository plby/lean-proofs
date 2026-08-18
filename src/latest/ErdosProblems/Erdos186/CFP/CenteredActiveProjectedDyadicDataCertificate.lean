/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.CenteredActiveProjectedPopulatedDyadicCertificate
import ErdosProblems.Erdos186.CFP.CenteredPreprocessingSource

/-!
# Projected source witness from retained dyadic preprocessing data

This discharges the structural fields of the projected populated certificate
from `DyadicCenteredPreprocessingData`.  The result is already a source-line
`FixedScaleWitness`; no preprocessed-certificate or no-carry callback remains.
-/

namespace Erdos186.CFP

noncomputable section

namespace RandomPartition

/-- The nonempty-relevant branch of retained centered preprocessing, with all
coordinate and approximation fields discharged and projected properization
applied at the source line. -/
theorem exists_centeredActiveProjectedDyadicDataCertificateConstants
    {source : Finset ℤ} {stableBudget D n C0 fold : ℕ}
    (propernessDenominator M : ℕ)
    (hpropernessDenominator : 0 < propernessDenominator)
    (data : Preprocessing.DyadicCenteredPreprocessingData source stableBudget
      D n C0 1
        (PreprocessingBilu.preprocessingScaleDen propernessDenominator) fold)
    (hrelevant : data.relevant.Nonempty) :
    ∃ corWidthMax denseMax denseEllMax denseWidthMax : ℕ,
      0 < denseMax ∧
      ∀ {q cap low terminal s block : ℕ},
        PreprocessingBilu.DyadicRangeSourceHApproximationFamily
          source low terminal D 1
            (PreprocessingBilu.preprocessingScaleDen
              propernessDenominator) →
        0 < q → 2 ≤ n → D ≤ n → low < terminal →
        (∀ h, low ≤ h → h ≤ terminal → 2 ^ h ≤ n) →
        (∀ h, low ≤ h → h ≤ terminal →
          PreprocessingBilu.preprocessingIndexBound D
              propernessDenominator ≤ 2 ^ h) →
        (∀ z ∈ source, 0 ≤ z ∧ z < (n : ℤ)) →
        (2 * q + 1) *
            ((cap + 1) +
              (Nat.log 2
                ((n ^ obstaclePolynomialExponent D + 1) * (q + 1)) +
                  1)) ≤
          stableBudget / C0 + 1 →
        (2 * q + 1) *
            ((cap + 1) +
              (Nat.log 2
                ((n ^ obstaclePolynomialExponent D + 1) * (q + 1)) +
                  1)) ≤ data.core.card →
        2 ^ (low + 1) * (Nat.log 2 (2 ^ low * n + 1) + 1) +
            16 * Greedy.stableDyadicRatio D
              (PreprocessingBilu.preprocessingScaleDen
                propernessDenominator) * 2 ^ terminal + 1 < cap →
        fold ≤ M * 2 ^ terminal →
        rankFlexiblePhysicalComparisonCoefficient D M
            (PreprocessingBilu.preprocessingScaleDen
              propernessDenominator) ≤ fold + 1 →
        cap ≤ 2 * stableBudget →
        0 < block →
        denseEllMax ≤ q + 1 →
        max corWidthMax denseWidthMax ≤
          blockedColorSourceScale s q block →
        denseMax ≤ q + 1 →
        cap + rankFlexiblePhysicalDensityDenominator D M
            (PreprocessingBilu.preprocessingScaleDen
              propernessDenominator) ≤
          blockedColorSourceScale s q block →
        2 * block * (q + 1) ≤ s →
        blockedColorSourceScale s q block ≤ fold →
        ProjectedProperization.projectionFactor D ≤
          blockedColorSourceScale s q block * ((q + 1) / denseMax) →
        ∃ k : ℕ, Nonempty (FixedScaleWitness
          (Stability.integerPoints data.core) s D k 0 1
            ((4 * denseMax * block) *
              ProjectedProperization.projectionFactor D)) := by
  obtain ⟨d, hdrel⟩ := hrelevant
  let rd : {e // e ∈ data.relevant} := ⟨d, hdrel⟩
  obtain ⟨corWidthMax, denseMax, denseEllMax, denseWidthMax,
      hdenseMax, hcertificate⟩ :=
    exists_centeredActiveProjectedPopulatedDyadicCertificateConstants D M
      propernessDenominator hpropernessDenominator
  refine ⟨corWidthMax, denseMax, denseEllMax, denseWidthMax,
    hdenseMax, ?_⟩
  intro q cap low terminal s block hfamily hq hn hDn hlowTerminal hleveln
    hindex hinterval hcapacity hpopulation hcrossNumeric hfoldLevel
    hcomparison hcapStable hblock hell hwidth hCell hcapSource
    hroom hsFold hprojection
  let V : HDimension.HApproximation data.weakCore fold d 1
      (PreprocessingBilu.preprocessingScaleDen propernessDenominator) := by
    have hV := data.approximation rd
    rw [data.hAt_eq_fold rd] at hV
    exact Classical.choice hV
  have hfoldn : fold ≤ n := by
    have hle := data.horizon_le rd
    simpa only [data.hAt_eq_fold rd] using hle
  have hfoldLarge : PreprocessingBilu.preprocessingNoCarryIndexBound D
      (PreprocessingBilu.preprocessingScaleDen propernessDenominator) ≤
        fold := by
    have hlarge := data.horizon_large rd
    simpa only [data.hAt_eq_fold rd,
      PreprocessingBilu.preprocessingNoCarryIndexBound] using hlarge
  apply hcertificate data.boxesProper hdrel data.weakCore_subset_source
    data.core_subset_weakCore data.zero_mem_weakCore data.zero_mem_core
    (fun e he ↦ data.rank_le ⟨e, he⟩)
    data.stable data.weakCore_stable hfamily V hq hn hDn hfoldn
    hlowTerminal hleveln hindex
    (fun z hz ↦ hinterval z (data.weakCore_subset_source hz))
    hcapacity hpopulation hcrossNumeric hfoldLevel hcomparison hcapStable
    hfoldLarge hblock hell hwidth hCell hcapSource hroom hsFold
    hprojection

end RandomPartition

end

end Erdos186.CFP

#print axioms
  Erdos186.CFP.RandomPartition.exists_centeredActiveProjectedDyadicDataCertificateConstants
