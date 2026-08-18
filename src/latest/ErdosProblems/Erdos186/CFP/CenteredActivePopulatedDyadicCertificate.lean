/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.ActiveCenteredVolume
import ErdosProblems.Erdos186.CFP.BlockedCertificateNumerics
import ErdosProblems.Erdos186.CFP.CenteredScaledRankFlexiblePhysicalCertificate
import ErdosProblems.Erdos186.CFP.CenteredScaledActivePhysicalDensityTargetCertificate
import ErdosProblems.Erdos186.CFP.GreedyPopulatedRangeCrossing
import ErdosProblems.Erdos186.CFP.MultifoldSumsetLower
import ErdosProblems.Erdos186.CFP.PhysicalNoCarryNumerics
import ErdosProblems.Erdos186.CFP.PreprocessedCertificateScale
import ErdosProblems.Erdos186.CFP.RandomPartitionObstacleBound
import ErdosProblems.Erdos186.CFP.RandomPartitionGeneratedSubgroup
import ErdosProblems.Erdos186.CFP.RandomPartitionSharpPopulated
import ErdosProblems.Erdos186.CFP.ScaledCertificateNumerics

/-!
# Populated dyadic certificate in active centered coordinates

The canonical rank-`d` bounding presentation may contain width-one padding.
This join deletes those directions before applying Corollary 2.17, while
retaining the full-coordinate sharp-colouring span and projecting it to the
active coordinates.  All five Corollary/DenseBox constants are selected
uniformly over the finitely many active ranks at most `D`.
-/

namespace Erdos186.CFP

open GrowthLemmas
open scoped BigOperators

noncomputable section

namespace RandomPartition

/-- Structural source-facing join using the nondegenerate active part of the
canonical centered presentation.  No minimum-width assumption on the padded
rank-`d` box remains, and the output denominator is uniform in the retained
rank. -/
theorem exists_centeredActivePopulatedDyadicCertificateConstants
    (D M propernessDenominator : ℕ)
    (hpropernessDenominator : 0 < propernessDenominator) :
    ∃ corMax corWidthMax denseMax denseEllMax denseWidthMax : ℕ,
      0 < corMax ∧ 0 < denseMax ∧
      ∀ {source W B : Finset ℤ} {relevant : Finset ℕ} {d : ℕ}
        (hproper : Stability.RelevantBoxesProper W relevant),
        d ∈ relevant → W ⊆ source → B ⊆ W → 0 ∈ W → 0 ∈ B →
        (∀ e ∈ relevant, e ≤ D) →
        ∀ {stableBudget q cap n fold low terminal s C0 block : ℕ},
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
          0 < q → 2 ≤ n → D ≤ n → fold ≤ n →
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
          0 < block →
          denseEllMax ≤ q + 1 →
          max corWidthMax denseWidthMax ≤
            blockedColorSourceScale s q block →
          denseMax ≤ q + 1 →
          0 < blockedColorSourceScale s q block →
          cap + rankFlexiblePhysicalDensityDenominator D M
              (PreprocessingBilu.preprocessingScaleDen
                propernessDenominator) ≤
            blockedColorSourceScale s q block →
          2 * block * (q + 1) ≤ s →
          s ≤ fold →
          2 * PreprocessingBilu.preprocessingNoCarryIndexBound D
              (PreprocessingBilu.preprocessingScaleDen
                propernessDenominator) * corMax ≤ block →
          Nonempty (PreprocessedReserveCertificate B s D 0 1
            (4 * denseMax * block)) := by
  let scaleDen :=
    PreprocessingBilu.preprocessingScaleDen propernessDenominator
  let cDen := rankFlexiblePhysicalDensityDenominator D M scaleDen
  have hscaleDen : 0 < scaleDen := by
    dsimp only [scaleDen, PreprocessingBilu.preprocessingScaleDen]
    positivity
  have hcDen : 0 < cDen := by
    dsimp only [cDen, rankFlexiblePhysicalDensityDenominator,
      rankFlexiblePhysicalComparisonCoefficient, scaleDen]
    positivity
  have hconstants : ∀ i : Fin (D + 1),
      ∃ corConstant corWidth denseConstant denseEll denseWidth : ℕ,
        0 < corConstant ∧ 0 < denseConstant ∧
        (0 < i.1 →
          ∀ {W B A : Finset ℤ}
            (P : BoundingBox.BoundingGAP W i.1)
            (hPproper : P.progression.Proper)
            (hPnondegenerate : P.progression.Nondegenerate)
            (hBW : B ⊆ W) (hAB : A ⊆ B)
            (hzeroW : 0 ∈ W) (hzeroB : 0 ∈ B),
            ∀ {q cap target sourceScale s block : ℕ}
              (c : {a // a ∈ A} → Fin (q + 1))
              (run : ∀ j, Greedy.PhysicalTargetRun
                (integerColorClass A c j) cap target),
              denseEll ≤ q + 1 →
              max corWidth denseWidth ≤ sourceScale →
              denseConstant ≤ q + 1 →
              0 < sourceScale → 0 < block → i.1 ≤ D →
              (∀ j, Stability.generatedSubgroup
                  (Preprocessing.centeredIdentification P hPproper hzeroW)
                  (integerColorClass A c j) =
                Stability.generatedSubgroup
                  (Preprocessing.centeredIdentification P hPproper hzeroW) B) →
              (∀ j, (run j).steps + cDen ≤ sourceScale) →
              1 * (Preprocessing.centeredCoordinateAxisBox
                    P.progression sourceScale).volume ≤ cDen * target →
              (q + 1) * sourceScale ≤ s →
              s ≤ 2 * block * (q + 1) * sourceScale →
              sourceScale * ((q + 1) / denseConstant) ≤ s →
              (P.progression.dilate
                (((q + 1) / denseConstant) * corConstant *
                  (2 * sourceScale))).Proper →
              Nonempty (PreprocessedReserveCertificate B s D 0 1
                (4 * denseConstant * block))) := by
    intro i
    by_cases hi : 0 < i.1
    · obtain ⟨corConstant, corWidth, denseConstant, denseEll, denseWidth,
          hcor, hdense, hcert⟩ :=
        exists_centeredScaledActivePhysicalDensityTargetCertificateConstants
          i.1 hi 1 cDen (by omega) (by omega)
      refine ⟨corConstant, corWidth, denseConstant, denseEll, denseWidth,
        hcor, hdense, ?_⟩
      intro _hpos W B A P hPproper hPnondegenerate hBW hAB hzeroW hzeroB
        q cap target sourceScale s block c run hell hwidth hCell hsourcePos
        hblock hdD
        hambient hsourceBound htarget hreserveLower hsUpper hscaleUpper hnoCarry
      exact hcert P hPproper hPnondegenerate hBW hAB hzeroW hzeroB
        (D := D) (block := block) c run
        hell hwidth hCell hsourcePos hblock hdD hambient hsourceBound htarget
        hreserveLower hsUpper hscaleUpper hnoCarry
    · refine ⟨1, 1, 1, 1, 1, by omega, by omega, ?_⟩
      intro hpos
      omega
  choose corConstant corWidth denseConstant denseEll denseWidth hspec
    using hconstants
  let corMax := 1 + ∑ i, corConstant i
  let corWidthMax := 1 + ∑ i, corWidth i
  let denseMax := 1 + ∑ i, denseConstant i
  let denseEllMax := 1 + ∑ i, denseEll i
  let denseWidthMax := 1 + ∑ i, denseWidth i
  have hcorLe (i : Fin (D + 1)) : corConstant i ≤ corMax := by
    exact (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _)
      (Finset.mem_univ i)).trans (Nat.le_add_left _ 1)
  have hcorWidthLe (i : Fin (D + 1)) : corWidth i ≤ corWidthMax := by
    exact (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _)
      (Finset.mem_univ i)).trans (Nat.le_add_left _ 1)
  have hdenseLe (i : Fin (D + 1)) : denseConstant i ≤ denseMax := by
    exact (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _)
      (Finset.mem_univ i)).trans (Nat.le_add_left _ 1)
  have hellLe (i : Fin (D + 1)) : denseEll i ≤ denseEllMax := by
    exact (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _)
      (Finset.mem_univ i)).trans (Nat.le_add_left _ 1)
  have hdenseWidthLe (i : Fin (D + 1)) : denseWidth i ≤ denseWidthMax := by
    exact (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _)
      (Finset.mem_univ i)).trans (Nat.le_add_left _ 1)
  refine ⟨corMax, corWidthMax, denseMax, denseEllMax, denseWidthMax,
    by simp [corMax], by simp [denseMax], ?_⟩
  intro source W B relevant d hproper hdrel hWsource hBW hzeroW hzeroB
    hrank stableBudget q cap n fold low terminal s C0 block hstable hweakW hfamily
    V hq hn hDn hfoldn hlowTerminal hleveln hindex hinterval hcapacity
    hpopulation hcrossNumeric hfoldLevel hcomparison hcapStable hfoldLarge
    hblock hell hwidth hCell hsourcePos hcapSource hroom hsFold hblockLarge
  let sourceScale := blockedColorSourceScale s q block
  have hd : 0 < d := hproper.positive hdrel
  have hdD : d ≤ D := hrank d hdrel
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
  obtain ⟨target, run, hglobalTarget, _htargetEq⟩ :=
    exists_common_physicalTargetRun_of_rankFlexible_threshold
      (scaleNum := 1) (scaleDen := scaleDen) (c := c) (level := level)
      (hzeroA := hzeroA) (hAW := hAW)
      (hcap := fun i ↦ (hpopulated i).le) (hcross := hcross)
      (hstable := fun i ↦ (hstableColor i).weaklyStable)
      (hfoldn := fun _i ↦ by
        simpa only [level] using
          (hleveln terminal (Nat.le_of_lt hlowTerminal) le_rfl))
      (hinterval := hinterval) (haccessible := by
        intro i T hT hcard
        simpa only [one_mul] using haccessible i T hT hcard)
      (hscaleDen := hscaleDen)
      (hHM := fun i ↦ by simpa only [level] using hfoldLevel)
      (hlarge := by
        simpa only [rankFlexiblePhysicalComparisonCoefficient] using
          hglobalLarge)
  have htargetRaw :
      (Preprocessing.centeredCoordinateAxisBox
        (BoundingBox.dBoundingBox W d hd).progression
          sourceScale).volume ≤ cDen * target := by
    have hsourceFold : sourceScale ≤ fold := by
      have hsourceS : sourceScale ≤ s := by
        have hqScale : sourceScale ≤ (q + 1) * sourceScale := by
          simpa only [Nat.one_mul] using
            Nat.mul_le_mul_right sourceScale (show 1 ≤ q + 1 by omega)
        exact hqScale.trans (blockedColorSourceScale_bounds hblock hroom).2.2.2
      exact hsourceS.trans hsFold
    have hvolume :=
      Preprocessing.HApproximation.centeredCoordinateAxisBox_volume_le_physicalTarget_of_le
        hweakGlobal V hd hdD hfoldn hsourceFold hinterval
        (by
          simpa only [one_mul,
            PreprocessingBilu.preprocessingNoCarryIndexBound] using
            PreprocessingBilu.approximation_numeric_of_preprocessing_large
              hscaleDen hd hdD hfoldLarge)
        hglobalTarget
    dsimp only [cDen, rankFlexiblePhysicalDensityDenominator,
      rankFlexiblePhysicalComparisonCoefficient]
    convert hvolume using 1 <;> ring
  let Pfull := BoundingBox.dBoundingBox W d hd
  let Pactive := Pfull.activeDimensions
  have hactivePos : 0 < Pfull.progression.activeRank :=
    Pfull.activeRank_pos (hproper.proper hdrel) hzeroW hWne
  have hactiveD : Pfull.progression.activeRank ≤ D :=
    Pfull.progression.activeRank_le.trans hdD
  let activeIndex : Fin (D + 1) :=
    ⟨Pfull.progression.activeRank, by omega⟩
  have hactiveIndex : 0 < activeIndex.1 := by
    simpa only [activeIndex] using hactivePos
  have hactual := hspec activeIndex
  have hcertificate := hactual.2.2 hactiveIndex
    (W := W) (B := B) (A := A)
  have htargetActive :
      1 * (Preprocessing.centeredCoordinateAxisBox Pactive.progression
        sourceScale).volume ≤ cDen * target := by
    simp only [one_mul, Pactive, BoundingBox.BoundingGAP.activeDimensions_progression,
      Preprocessing.centeredCoordinateAxisBox_activeDimensions_volume]
    simpa only [Pfull] using htargetRaw
  have hspanActive : ∀ i, Stability.generatedSubgroup
      (Preprocessing.centeredIdentification Pactive
        (Pfull.activeDimensions_proper (hproper.proper hdrel)) hzeroW)
        (integerColorClass A c i) =
      Stability.generatedSubgroup
        (Preprocessing.centeredIdentification Pactive
          (Pfull.activeDimensions_proper (hproper.proper hdrel)) hzeroW) B := by
    intro i
    have hspanInteger : Stability.generatedSubgroup
        (Stability.centeredMinimalIdentificationFamily hproper d)
          (integerColorClass A c i) =
        Stability.generatedSubgroup
          (Stability.centeredMinimalIdentificationFamily hproper d) B := by
      rw [generatedSubgroup_integerColorClass_eq_anchoredColorClass c i
        (Stability.centeredMinimalIdentificationFamily hproper d)
        (Stability.centeredMinimalIdentificationFamily_zero hproper d)]
      exact hspan i d hdrel
    simpa only [Pactive, Pfull] using
      Preprocessing.generatedSubgroup_centeredActive_eq_of_centeredMinimal_eq
        hproper hdrel hzeroW hspanInteger
  have hrunSource : ∀ i, (run i).steps + cDen ≤ sourceScale := by
    intro i
    exact (Nat.add_le_add_right (run i).steps_le_cap cDen).trans hcapSource
  obtain ⟨_sourcePos, _hblockedLower, hsUpper, hreserveLower⟩ :=
    blockedColorSourceScale_bounds hblock hroom
  have hscaleUpper : sourceScale *
      ((q + 1) / denseConstant activeIndex) ≤ s := by
    have hdiv : (q + 1) / denseConstant activeIndex ≤ q + 1 :=
      Nat.div_le_self _ _
    calc
      sourceScale * ((q + 1) / denseConstant activeIndex) ≤
          sourceScale * (q + 1) := Nat.mul_le_mul_left sourceScale hdiv
      _ = (q + 1) * sourceScale := by ring
      _ ≤ s := hreserveLower
  have hellActual : denseEll activeIndex ≤ q + 1 :=
    (hellLe activeIndex).trans hell
  have hwidthActual : max (corWidth activeIndex) (denseWidth activeIndex) ≤
      sourceScale := by
    exact (max_le_max (hcorWidthLe activeIndex)
      (hdenseWidthLe activeIndex)).trans hwidth
  have hCellActual : denseConstant activeIndex ≤ q + 1 :=
    (hdenseLe activeIndex).trans hCell
  have hactualNoCarryScale :
          ((q + 1) / denseConstant activeIndex) * corConstant activeIndex *
          (2 * sourceScale) ≤
        (q + 1) * corMax * (2 * sourceScale) := by
    have hdiv : (q + 1) / denseConstant activeIndex ≤ q + 1 :=
      Nat.div_le_self _ _
    gcongr
    exact hcorLe activeIndex
  have hfullNoCarry :
      (Pfull.progression.dilate
        (((q + 1) / denseConstant activeIndex) * corConstant activeIndex *
          (2 * sourceScale))).Proper := by
    have huniformProper : (Pfull.progression.dilate
        ((q + 1) * corMax * (2 * sourceScale))).Proper := by
      have hnoCarryUniform : PreprocessingBilu.preprocessingNoCarryIndexBound D
          scaleDen * ((q + 1) * corMax * (2 * sourceScale)) ≤ fold := by
        have hleS : PreprocessingBilu.preprocessingNoCarryIndexBound D scaleDen *
            ((q + 1) * corMax * (2 * sourceScale)) ≤ s := by
          calc
            PreprocessingBilu.preprocessingNoCarryIndexBound D scaleDen *
                ((q + 1) * corMax * (2 * sourceScale)) =
                (2 * PreprocessingBilu.preprocessingNoCarryIndexBound D
                  scaleDen * corMax) * ((q + 1) * sourceScale) := by ring
            _ ≤ block * ((q + 1) * sourceScale) :=
              Nat.mul_le_mul_right ((q + 1) * sourceScale) hblockLarge
            _ = block * (q + 1) * sourceScale := by ring
            _ ≤ s := _hblockedLower
        exact hleS.trans hsFold
      exact PreprocessingBilu.HApproximation.boundingBox_dilate_proper_of_preprocessingNoCarry
        V hd hdD hnoCarryUniform
    exact GAP.dilate_proper_mono Pfull.progression hactualNoCarryScale
      huniformProper
  have hactiveNoCarry :
      (Pactive.progression.dilate
        (((q + 1) / denseConstant activeIndex) * corConstant activeIndex *
          (2 * sourceScale))).Proper := by
    exact GAP.dilate_activeDimensions_proper Pfull.progression _ hfullNoCarry
  obtain ⟨C⟩ := hcertificate Pactive
    (Pfull.activeDimensions_proper (hproper.proper hdrel))
    Pfull.activeDimensions_nondegenerate hBW (Finset.erase_subset 0 B)
    hzeroW hzeroB (block := block) c run hellActual hwidthActual hCellActual
    hsourcePos hblock hactiveD hspanActive hrunSource htargetActive
    hreserveLower hsUpper hscaleUpper hactiveNoCarry
  exact ⟨C.increaseScaleDen
    (by gcongr; exact hdenseLe activeIndex) (by positivity)⟩

end RandomPartition

end

end Erdos186.CFP

#print axioms
  Erdos186.CFP.RandomPartition.exists_centeredActivePopulatedDyadicCertificateConstants
