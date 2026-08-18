/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.CenteredPopulatedDyadicCertificate
import ErdosProblems.Erdos186.CFP.CenteredPreprocessingSource

/-!
# Concrete certificate from retained centered preprocessing data

On the nonempty-relevant branch, the retained preprocessing package already
contains the global weak core, stable core, positive final rank, global
H-approximation, rank bounds, and the base no-carry hierarchy.  This adapter
feeds all of those fields into the populated dyadic structural join.
-/

namespace Erdos186.CFP

noncomputable section

namespace RandomPartition

/-- The nonempty-relevant branch of retained centered preprocessing, with
all structural fields discharged. -/
theorem exists_centeredDyadicDataCertificateConstants
    {source : Finset ℤ} {stableBudget D n C0 fold : ℕ}
    (propernessDenominator M : ℕ)
    (hpropernessDenominator : 0 < propernessDenominator)
    (data : Preprocessing.DyadicCenteredPreprocessingData source stableBudget
      D n C0 1
        (PreprocessingBilu.preprocessingScaleDen propernessDenominator) fold)
    (hrelevant : data.relevant.Nonempty) :
    ∃ rd : {d // d ∈ data.relevant},
    ∃ corConstant corWidth denseConstant denseEll denseWidth : ℕ,
      0 < rd.1 ∧
      0 < corConstant ∧ 0 < denseConstant ∧
      ∀ {q cap low terminal s : ℕ},
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
        denseEll ≤ q + 1 →
        max corWidth denseWidth ≤
            (Preprocessing.centeredCoordinateAxisBox
            (BoundingBox.dBoundingBox data.weakCore rd.1
              (data.boxesProper.positive rd.2)).progression
            (colorSourceScale s q)).minWidth →
        denseConstant ≤ q + 1 →
        0 < colorSourceScale s q →
        cap + rankFlexiblePhysicalDensityDenominator D M
            (PreprocessingBilu.preprocessingScaleDen
              propernessDenominator) ≤ colorSourceScale s q →
        2 * (q + 1) ≤ s →
        colorSourceScale s q ≤ fold →
        let noCarryScale :=
          ((q + 1) / denseConstant) * corConstant *
            (2 * colorSourceScale s q)
        PreprocessingBilu.preprocessingNoCarryIndexBound D
            (PreprocessingBilu.preprocessingScaleDen
              propernessDenominator) * noCarryScale ≤ fold →
        Nonempty (PreprocessedReserveCertificate data.core s D 0 1
          (4 * denseConstant)) := by
  obtain ⟨d, hdrel⟩ := hrelevant
  have hd : 0 < d := data.boxesProper.positive hdrel
  let rd : {e // e ∈ data.relevant} := ⟨d, hdrel⟩
  obtain ⟨corConstant, corWidth, denseConstant, denseEll, denseWidth,
      hcorConstant, hdenseConstant, hcertificate⟩ :=
    exists_centeredPopulatedDyadicCertificateConstants d hd D M
      propernessDenominator hpropernessDenominator
  refine ⟨rd, corConstant, corWidth, denseConstant, denseEll, denseWidth,
    hd, hcorConstant, hdenseConstant, ?_⟩
  intro q cap low terminal s hfamily hq hn hDn hlowTerminal hleveln hindex
    hinterval hcapacity hpopulation hcrossNumeric hfoldLevel hcomparison
    hcapStable hell hwidth hCell hsourcePos hcapSource hroom hsourceFold
  dsimp only
  intro hnoCarry
  let V : HDimension.HApproximation data.weakCore fold d 1
      (PreprocessingBilu.preprocessingScaleDen propernessDenominator) := by
    have hV := data.approximation rd
    rw [data.hAt_eq_fold rd] at hV
    exact Classical.choice hV
  have hdD : d ≤ D := data.rank_le rd
  have hfoldn : fold ≤ n := by
    have := data.horizon_le rd
    simpa only [data.hAt_eq_fold rd] using this
  have hfoldLarge : PreprocessingBilu.preprocessingNoCarryIndexBound D
      (PreprocessingBilu.preprocessingScaleDen propernessDenominator) ≤
        fold := by
    have := data.horizon_large rd
    simpa only [data.hAt_eq_fold rd,
      PreprocessingBilu.preprocessingNoCarryIndexBound] using this
  apply hcertificate data.boxesProper hdrel data.weakCore_subset_source
    data.core_subset_weakCore data.zero_mem_weakCore data.zero_mem_core
    (fun e he ↦ data.rank_le ⟨e, he⟩)
    data.stable data.weakCore_stable hfamily V hq hn hDn hdD
    hfoldn hlowTerminal hleveln hindex
    (fun z hz ↦ hinterval z (data.weakCore_subset_source hz))
    hcapacity hpopulation hcrossNumeric hfoldLevel hcomparison hcapStable
    hfoldLarge hell hwidth hCell hsourcePos hcapSource hroom hsourceFold
    hnoCarry

end RandomPartition

end

end Erdos186.CFP

#print axioms
  Erdos186.CFP.RandomPartition.exists_centeredDyadicDataCertificateConstants
