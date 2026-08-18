/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.CenteredScaledRankFlexiblePhysicalCertificate
import ErdosProblems.Erdos186.CFP.GreedyPopulatedRangeCrossing
import ErdosProblems.Erdos186.CFP.MultifoldSumsetLower
import ErdosProblems.Erdos186.CFP.RandomPartitionObstacleBound
import ErdosProblems.Erdos186.CFP.RandomPartitionGeneratedSubgroup
import ErdosProblems.Erdos186.CFP.RandomPartitionSharpPopulated
import ErdosProblems.Erdos186.CFP.ScaledCertificateNumerics

/-!
# Centered certificate from populated sharp colouring and a dyadic range

This is the structural outer join.  It constructs the random colouring,
retains strict population in every nonzero colour, proves all terminal
crossings from the source dyadic range, constructs the rank-flexible common
physical target, and invokes the scaled map-back certificate.  The remaining
hypotheses are explicit natural-number scale inequalities.
-/

namespace Erdos186.CFP

open GrowthLemmas

noncomputable section

namespace RandomPartition

/-- Structural source-facing join above centered preprocessing. -/
theorem exists_centeredPopulatedDyadicCertificateConstants
    (d : ℕ) (hd : 0 < d) (D M propernessDenominator : ℕ)
    (hpropernessDenominator : 0 < propernessDenominator) :
    ∃ corConstant corWidth denseConstant denseEll denseWidth : ℕ,
      0 < corConstant ∧ 0 < denseConstant ∧
      ∀ {source W B : Finset ℤ} {relevant : Finset ℕ}
        (hproper : Stability.RelevantBoxesProper W relevant),
        (hdrel : d ∈ relevant) → W ⊆ source → B ⊆ W →
        0 ∈ W → 0 ∈ B → (∀ e ∈ relevant, e ≤ D) →
        ∀ {stableBudget q cap n fold low terminal s C0 : ℕ},
          Stability.StronglyStableFor B (Stability.minimalBoxFamily W)
            stableBudget D (n ^ 2) relevant
              (Stability.centeredMinimalIdentificationFamily hproper) C0 →
          Stability.WeaklyStableMinimalFor W (2 * stableBudget) D n →
          PreprocessingBilu.DyadicRangeSourceHApproximationFamily
            source low terminal D 1
              (PreprocessingBilu.preprocessingScaleDen
                propernessDenominator) →
          HDimension.HApproximation W fold d 1
            (PreprocessingBilu.preprocessingScaleDen
              propernessDenominator) →
          0 < q → 2 ≤ n → D ≤ n → d ≤ D → fold ≤ n →
          low < terminal →
          (∀ h, low ≤ h → h ≤ terminal → 2 ^ h ≤ n) →
          (∀ h, low ≤ h → h ≤ terminal →
            PreprocessingBilu.preprocessingIndexBound D
                propernessDenominator ≤ 2 ^ h) →
          (∀ z ∈ W, 0 ≤ z ∧ z < (n : ℤ)) →
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
                    1)) ≤ B.card →
          2 ^ (low + 1) * (Nat.log 2 (2 ^ low * n + 1) + 1) +
              16 * Greedy.stableDyadicRatio D
                (PreprocessingBilu.preprocessingScaleDen
                  propernessDenominator) * 2 ^ terminal + 1 < cap →
          fold ≤ M * 2 ^ terminal →
          rankFlexiblePhysicalComparisonCoefficient D M
              (PreprocessingBilu.preprocessingScaleDen
                propernessDenominator) ≤ fold + 1 →
          cap ≤ 2 * stableBudget →
          PreprocessingBilu.preprocessingNoCarryIndexBound D
              (PreprocessingBilu.preprocessingScaleDen
                propernessDenominator) ≤ fold →
          denseEll ≤ q + 1 →
          max corWidth denseWidth ≤
            (Preprocessing.centeredCoordinateAxisBox
              (BoundingBox.dBoundingBox W d
                (hproper.positive hdrel)).progression
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
          Nonempty (PreprocessedReserveCertificate B s D 0 1
            (4 * denseConstant)) := by
  let scaleDen :=
    PreprocessingBilu.preprocessingScaleDen propernessDenominator
  have hscaleDen : 0 < scaleDen := by
    dsimp only [scaleDen, PreprocessingBilu.preprocessingScaleDen]
    positivity
  obtain ⟨corConstant, corWidth, denseConstant, denseEll, denseWidth,
      hcorConstant, hdenseConstant, hcertificate⟩ :=
    exists_centeredScaledRankFlexiblePhysicalCertificateConstants
      d hd D M scaleDen hscaleDen
  refine ⟨corConstant, corWidth, denseConstant, denseEll, denseWidth,
    hcorConstant, hdenseConstant, ?_⟩
  intro source W B relevant hproper hdrel hWsource hBW hzeroW hzeroB hrank
    stableBudget q cap n fold low terminal s C0 hstable hweakW hfamily V hq
    hn hDn hdD hfoldn hlowTerminal hleveln hindex hinterval hcapacity
    hpopulation hcrossNumeric hfoldLevel hcomparison hcapStable hfoldLarge
    hell hwidth hCell hsourcePos hcapSource hroom hsourceFold
  dsimp only
  intro hnoCarry
  have hobstacles := canonicalObstaclePolynomialBound_centered
    hn hDn hBW hzeroW hinterval hproper hrank
  obtain ⟨c, hpopulated, hstableColor, hspan⟩ :=
    exists_strictlyPopulated_eraseZero_coloring_stronglyStableFor_with_commonSpan_of_polynomial_bound_additive
      hstable
      (fun e he ↦ Stability.centeredMinimalIdentificationFamily_zero
        hproper e)
      hobstacles hq hcapacity hpopulation
  let A := B.erase 0
  have hzeroA : 0 ∉ A := Finset.notMem_erase 0 B
  have hAW : insert 0 A ⊆ W := by
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact hzeroW
    · exact hBW (Finset.erase_subset 0 B hz)
  have hASource : insert 0 A ⊆ source := hAW.trans hWsource
  let level : Fin (q + 1) → ℕ := fun _ ↦ terminal
  have hcross : ∀ i, Greedy.dyadicBinStart
      (integerColorClass A c i) cap cap (level i) < cap := by
    intro i
    simpa only [level] using
      dyadicBinStart_lt_cap_of_populated_dyadicRange
        c hfamily hzeroA hASource hAW hpopulated
        (fun j ↦ (hstableColor j).weaklyStable)
        (by omega) hlowTerminal hleveln hinterval hindex hcrossNumeric i
  have haccessible : ∀ i, ∀ T : Finset ℤ,
      T ⊆ integerColorClass A c i →
      (integerColorClass A c i).card ≤ T.card + cap →
      ∃ e : ℕ, 0 < e ∧ e ≤ D ∧
        ∃ VT : HDimension.HApproximation (insert 0 T) (2 ^ level i) e
            1 scaleDen,
          (2 * scaleDen) ^ e * (2 ^ level i + 1) ^ (e - 1) <
            (2 ^ level i) ^ e := by
    intro i T hT hTcard
    have hTnonempty : T.Nonempty := by
      by_contra hnot
      have hTempty : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hnot
      rw [hTempty] at hTcard
      simp only [Finset.card_empty, zero_add] at hTcard
      exact (Nat.not_lt_of_ge hTcard) (hpopulated i)
    have hTne : insert 0 T ≠ {0} := by
      intro heq
      obtain ⟨z, hz⟩ := hTnonempty
      have hz0 : z = 0 := by
        have : z ∈ ({0} : Finset ℤ) := by
          rw [← heq]
          exact Finset.mem_insert_of_mem hz
        simpa using this
      subst z
      exact hzeroA (integerColorClass_subset A c i (hT hz))
    have hTsource : insert 0 T ⊆ source := by
      exact (Finset.insert_subset_insert 0 hT).trans
        ((Finset.insert_subset_insert 0
          (integerColorClass_subset A c i)).trans hASource)
    simpa only [level, scaleDen, one_mul] using
      PreprocessingBilu.exists_HApproximation_numeric_of_dyadicRange
        hfamily (Nat.le_of_lt hlowTerminal) (Nat.le_refl terminal)
          hTsource (by simp) hTne
          (hindex terminal (Nat.le_of_lt hlowTerminal) le_rfl)
  have hWne : W ≠ {0} := by
    intro hW
    let i : Fin (q + 1) := ⟨0, by omega⟩
    have hcardPos : 0 < (integerColorClass A c i).card :=
      (Nat.zero_le cap).trans_lt (hpopulated i)
    obtain ⟨z, hz⟩ := Finset.card_pos.mp hcardPos
    have hzW : z ∈ W := hAW (Finset.mem_insert_of_mem
      (integerColorClass_subset A c i hz))
    have hz0 : z = 0 := by simpa [hW] using hzW
    subst z
    exact hzeroA (integerColorClass_subset A c i hz)
  have hglobalLarge : rankFlexiblePhysicalComparisonCoefficient D M
      scaleDen ≤ (multifoldSumset fold W).card :=
    coefficient_le_card_multifoldSumset hzeroW hWne hcomparison
  have hweakGlobal : Stability.WeaklyStableMinimalFor W cap D n :=
    hweakW.mono_deletionBudget hcapStable
  have hspanInteger : ∀ i, Stability.generatedSubgroup
      (Stability.centeredMinimalIdentificationFamily hproper d)
        (integerColorClass A c i) =
      Stability.generatedSubgroup
        (Stability.centeredMinimalIdentificationFamily hproper d) B := by
    intro i
    rw [generatedSubgroup_integerColorClass_eq_anchoredColorClass c i
      (Stability.centeredMinimalIdentificationFamily hproper d)
      (Stability.centeredMinimalIdentificationFamily_zero hproper d)]
    exact hspan i d hdrel
  obtain ⟨hreserveLower, hsUpper, hscaleUpper⟩ :=
    colorSourceScale_certificate_bounds hroom hdenseConstant
  apply hcertificate hproper hdrel hBW (Finset.erase_subset 0 B) hzeroB
    c level hzeroA hAW (fun i ↦ (hpopulated i).le) hcross
    (fun i ↦ (hstableColor i).weaklyStable)
    (fun i ↦ by simpa only [level] using
      (hleveln terminal (Nat.le_of_lt hlowTerminal) le_rfl))
    hinterval haccessible
    (fun i ↦ by simpa only [level] using hfoldLevel)
    hglobalLarge hweakGlobal V hdD hfoldn hsourceFold hfoldLarge hell hwidth
    hCell hsourcePos hspanInteger hcapSource hreserveLower hsUpper hscaleUpper
    hnoCarry

end RandomPartition

end

end Erdos186.CFP

#print axioms
  Erdos186.CFP.RandomPartition.exists_centeredPopulatedDyadicCertificateConstants
