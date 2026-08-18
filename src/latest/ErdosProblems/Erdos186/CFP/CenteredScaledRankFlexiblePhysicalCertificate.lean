/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.CenteredScaledPhysicalDensityTargetCertificate
import ErdosProblems.Erdos186.CFP.GreedyPhysicalDensity
import ErdosProblems.Erdos186.CFP.PhysicalNoCarryNumerics

/-!
# Rank-flexible physical greedy runs in one final centered box

The colour approximations may have unrelated ranks and dyadic levels.  The
rank-flexible physical comparison first gives all colours one common target.
A single retained approximation of the global core then controls a smaller
centered coordinate box and certifies the no-carry dilation.  Thus the final
certificate only retains numerical scale inequalities.
-/

namespace Erdos186.CFP

open GrowthLemmas

noncomputable section

/-- Uniform comparison coefficient in the rank-flexible physical target. -/
def rankFlexiblePhysicalComparisonCoefficient
    (D M scaleDen : ℕ) : ℕ :=
  8 * (M + 1) ^ D * (2 * scaleDen) ^ D

/-- Density denominator after the final global coordinate-box comparison. -/
def rankFlexiblePhysicalDensityDenominator
    (D M scaleDen : ℕ) : ℕ :=
  8 * (6 * scaleDen) ^ D *
    rankFlexiblePhysicalComparisonCoefficient D M scaleDen

/-- Dilation volume is monotone in the dilation parameter. -/
theorem gap_volume_dilate_mono_of_le {d r a b : ℕ} (P : GAP d r)
    (hab : a ≤ b) :
    (P.dilate a).volume ≤ (P.dilate b).volume := by
  rw [Erdos186.GAP.volume_dilate, Erdos186.GAP.volume_dilate]
  apply Finset.prod_le_prod
  · intro i _hi
    exact Nat.zero_le _
  · intro i _hi
    exact Nat.add_le_add_right
      (Nat.mul_le_mul_right (P.widths i - 1) hab) 1

namespace Preprocessing

/-- The final coordinate scale can be any smaller scale than the retained
global approximation fold. -/
theorem HApproximation.centeredCoordinateAxisBox_volume_le_physicalTarget_of_le
    {W : Finset ℤ}
    {x D n fold sourceScale d scaleNum scaleDen coefficient target : ℕ}
    (hstable : Stability.WeaklyStableMinimalFor W x D n)
    (V : HDimension.HApproximation W fold d scaleNum scaleDen)
    (hd : 0 < d) (hdD : d ≤ D) (hfoldn : fold ≤ n)
    (hsourceScale : sourceScale ≤ fold)
    (hinterval : ∀ z ∈ W, 0 ≤ z ∧ z < (n : ℤ))
    (hnumeric :
      (2 * scaleDen) ^ d * (fold + 1) ^ (d - 1) <
        (scaleNum * fold) ^ d)
    (hphysical : (multifoldSumset fold W).card ≤ coefficient * target) :
    (centeredCoordinateAxisBox
        (BoundingBox.dBoundingBox W d hd).progression sourceScale).volume ≤
      (4 * (6 * scaleDen) ^ D * coefficient) * target := by
  have hfull :=
    Preprocessing.HApproximation.centeredCoordinateAxisBox_volume_le_physicalTarget
      hstable V hd hdD hfoldn hinterval hnumeric hphysical
  rw [centeredCoordinateAxisBox_volume]
  exact (gap_volume_dilate_mono_of_le _
    (Nat.mul_le_mul_left 2 hsourceScale)).trans hfull

end Preprocessing

namespace RandomPartition

/-- Complete finite structural join for heterogeneous colour ranks and
levels.  The remaining hypotheses are the sharp-colouring outputs and
explicit natural-number scale inequalities. -/
theorem exists_centeredScaledRankFlexiblePhysicalCertificateConstants
    (d : ℕ) (hd : 0 < d) (D M scaleDen : ℕ)
    (hscaleDen : 0 < scaleDen) :
    ∃ corConstant corWidth denseConstant denseEll denseWidth : ℕ,
      0 < corConstant ∧ 0 < denseConstant ∧
      ∀ {W B A : Finset ℤ} {relevant : Finset ℕ}
        (hproper : Stability.RelevantBoxesProper W relevant),
        (hdrel : d ∈ relevant) → B ⊆ W → A ⊆ B → 0 ∈ B →
        ∀ {q x n fold sourceScale cap s : ℕ}
          (c : {a // a ∈ A} → Fin (q + 1)),
          (level : Fin (q + 1) → ℕ) →
          0 ∉ A → insert 0 A ⊆ W →
          (∀ i, cap ≤ (integerColorClass A c i).card) →
          (∀ i, Greedy.dyadicBinStart
            (integerColorClass A c i) x cap (level i) < cap) →
          (∀ i, Stability.WeaklyStableFor
            (anchoredColorClass A c i) (Stability.minimalBoxFamily W)
              x D (n ^ 2)) →
          (∀ i, 2 ^ level i ≤ n) →
          (∀ z ∈ W, 0 ≤ z ∧ z < (n : ℤ)) →
          (∀ i, ∀ T : Finset ℤ,
            T ⊆ integerColorClass A c i →
            (integerColorClass A c i).card ≤ T.card + x →
            ∃ e : ℕ, 0 < e ∧ e ≤ D ∧
              ∃ V : HDimension.HApproximation
                  (insert 0 T) (2 ^ level i) e 1 scaleDen,
                (2 * scaleDen) ^ e * (2 ^ level i + 1) ^ (e - 1) <
                  (2 ^ level i) ^ e) →
          (∀ i, fold ≤ M * 2 ^ level i) →
          rankFlexiblePhysicalComparisonCoefficient D M scaleDen ≤
            (multifoldSumset fold W).card →
          Stability.WeaklyStableMinimalFor W x D n →
          (V : HDimension.HApproximation W fold d 1 scaleDen) →
          d ≤ D → fold ≤ n → sourceScale ≤ fold →
          PreprocessingBilu.preprocessingNoCarryIndexBound D scaleDen ≤
            fold →
          denseEll ≤ q + 1 →
          max corWidth denseWidth ≤
            (Preprocessing.centeredCoordinateAxisBox
              (BoundingBox.dBoundingBox W d
                (hproper.positive hdrel)).progression
              sourceScale).minWidth →
          denseConstant ≤ q + 1 →
          0 < sourceScale →
          (∀ i, Stability.generatedSubgroup
              (Stability.centeredMinimalIdentificationFamily hproper d)
              (integerColorClass A c i) =
            Stability.generatedSubgroup
              (Stability.centeredMinimalIdentificationFamily hproper d) B) →
          cap + rankFlexiblePhysicalDensityDenominator D M scaleDen ≤
            sourceScale →
          (q + 1) * sourceScale ≤ s →
          s ≤ 2 * (q + 1) * sourceScale →
          sourceScale * ((q + 1) / denseConstant) ≤ s →
          let noCarryScale :=
            ((q + 1) / denseConstant) * corConstant * (2 * sourceScale)
          PreprocessingBilu.preprocessingNoCarryIndexBound D scaleDen *
            noCarryScale ≤ fold →
          Nonempty (PreprocessedReserveCertificate B s D 0 1
            (4 * denseConstant)) := by
  let cDen := rankFlexiblePhysicalDensityDenominator D M scaleDen
  have hcDen : 0 < cDen := by
    dsimp only [cDen, rankFlexiblePhysicalDensityDenominator,
      rankFlexiblePhysicalComparisonCoefficient]
    positivity
  obtain ⟨corConstant, corWidth, denseConstant, denseEll, denseWidth,
      hcorConstant, hdenseConstant, hcertificate⟩ :=
    exists_centeredScaledPhysicalDensityTargetCertificateConstants
      d hd 1 cDen (by omega) (by omega)
  refine ⟨corConstant, corWidth, denseConstant, denseEll, denseWidth,
    hcorConstant, hdenseConstant, ?_⟩
  intro W B A relevant hproper hdrel hBW hAB hzeroB q x n fold
    sourceScale cap s c level hzeroA hAW hcap hcross hstableColors hleveln
    hinterval haccessible hfoldLevel hlarge hstableGlobal V hdD hfoldn
    hsourceFold hfoldLarge hell hwidth hCell hsourceScale hambient
    hcapSource hreserveLower hsUpper hscaleUpper
  dsimp only
  intro hnoCarryLarge
  obtain ⟨target, run, hglobalTarget, _htargetEq⟩ :=
    exists_common_physicalTargetRun_of_rankFlexible_threshold
      (scaleNum := 1) (scaleDen := scaleDen) (c := c) (level := level)
      (hzeroA := hzeroA) (hAW := hAW) (hcap := hcap)
      (hcross := hcross) (hstable := hstableColors) (hfoldn := hleveln)
      (hinterval := hinterval) (haccessible := by
        intro i T hT hcard
        simpa only [one_mul] using haccessible i T hT hcard)
      (hscaleDen := hscaleDen) (hHM := hfoldLevel) (hlarge := by
        simpa only [rankFlexiblePhysicalComparisonCoefficient] using hlarge)
  have htargetDensity :
      (Preprocessing.centeredCoordinateAxisBox
        (BoundingBox.dBoundingBox W d
          (hproper.positive hdrel)).progression sourceScale).volume ≤
        cDen * target := by
    have hvolume :=
      Preprocessing.HApproximation.centeredCoordinateAxisBox_volume_le_physicalTarget_of_le
        hstableGlobal V hd hdD hfoldn hsourceFold hinterval
        (by
          simpa only [one_mul,
            PreprocessingBilu.preprocessingNoCarryIndexBound] using
            PreprocessingBilu.approximation_numeric_of_preprocessing_large
              hscaleDen hd hdD hfoldLarge)
        hglobalTarget
    dsimp only [cDen, rankFlexiblePhysicalDensityDenominator,
      rankFlexiblePhysicalComparisonCoefficient]
    convert hvolume using 1 <;> ring
  have hrunSource : ∀ i, (run i).steps + cDen ≤ sourceScale := by
    intro i
    exact (Nat.add_le_add_right (run i).steps_le_cap cDen).trans hcapSource
  have hnoCarry :
      (((BoundingBox.dBoundingBox W d
        (hproper.positive hdrel)).progression).dilate
          (((q + 1) / denseConstant) * corConstant *
            (2 * sourceScale))).Proper := by
    exact
      PreprocessingBilu.HApproximation.boundingBox_dilate_proper_of_preprocessingNoCarry
        V hd hdD hnoCarryLarge
  apply hcertificate hproper hdrel hBW hAB hzeroB c run hell hwidth hCell
    hsourceScale hdD hambient hrunSource
  · simpa only [one_mul] using htargetDensity
  · exact hreserveLower
  · exact hsUpper
  · exact hscaleUpper
  · exact hnoCarry

end RandomPartition

end

end Erdos186.CFP

#print axioms
  Erdos186.CFP.RandomPartition.exists_centeredScaledRankFlexiblePhysicalCertificateConstants
