/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Bilu.Section4GenericSharpLoss
import ErdosProblems.Erdos186.CFP.Bilu.Section9UniformPresentationReplacement

/-!
# Terminal assembly of a uniform sharp replacement

This file packages the exact remaining geometric input.  Once the normalized
section gauge and the post-product affine restriction are supplied, all
source selection, rank ceilings, and volume constants are discharged here.
-/

namespace Erdos186.CFP.Bilu.Section4GenericSharpAssembly

open MeasureTheory
open CFP.BiluFreiman
open Proposition75Data Proposition75Construction
open Section4GenericSharpLoss Section4SharpDecayAssembly
open Section7BiasedNumerics Section8Synthesis
open Section8PresentationNormalization
open Section9NormalizedReplacement Section9UniformPresentationReplacement
open Section91GenericSharpProduct Section92PresentationDescent
open Section94RankThresholdBoundary

noncomputable section

set_option autoImplicit false

/-- The two genuinely geometric outputs left after Sections 5--8 and the
uniform source selection have been assembled. -/
structure UniformGenericSharpGeometry
    (s : ℕ) (sigma : ℝ) (proportionConstant rankBound : ℕ)
    (affineLoss : ℝ) where
  sharpSection : ∀ {A : Finset ℤ} (X : RankedBodyPresentation A)
    (epsilon : ℝ)
    {a : Fin (distortionRank sigma) → EuclideanSpace ℝ (Fin X.1)}
    {D : GeometricData (normalizedEuclideanBody X) a}
    (N : CoveredNormalizedReplacement
      (D := D) (K := normalizedLiftSet X)
      (coverConstant := 2 ^ distortionRank sigma * proportionConstant)
      (proposition75SourceConstant X.1 (distortionRank sigma))
      (ENNReal.ofReal
        (epsilon ^ proposition83Exponent X.1
          (distortionRank sigma)))⁻¹
      (Nat.ceil sigma)),
      Nonempty (GenericSharpSectionData X N)
  affine : ∀ {A : Finset ℤ} (X : RankedBodyPresentation A)
    (epsilon : ℝ)
    {a : Fin (distortionRank sigma) → EuclideanSpace ℝ (Fin X.1)}
    {D : GeometricData (normalizedEuclideanBody X) a}
    (N : CoveredNormalizedReplacement
      (D := D) (K := normalizedLiftSet X)
      (coverConstant := 2 ^ distortionRank sigma * proportionConstant)
      (proposition75SourceConstant X.1 (distortionRank sigma))
      (ENNReal.ofReal
        (epsilon ^ proposition83Exponent X.1
          (distortionRank sigma)))⁻¹
      (Nat.ceil sigma))
    (S : GenericSharpSectionData X N)
    (hA : A.Nonempty) (hcard : 1 < A.card)
    (hXrank : X.1 ≤ rankBound) (hX : EnlargedInjective s X)
    (hsum : ((twoA A).card : ℝ) ≤ sigma * A.card),
      ∃ Z : RankedBodyPresentation A,
        Z.1 ≤ rankBound ∧
        bodyVolume Z ≤ affineLoss *
          bodyVolume (rankedGenericSharpBodyPresentation X N S hcard)

/-- The uniform geometric package gives the internal sharp replacement
record consumed by the already-green Section 4 iteration. -/
def uniformSharpReplacementOfGenericGeometry
    (s : ℕ) (hs : 0 < s) (sigma : ℝ) (hsigma : 1 ≤ sigma)
    (proportionConstant rankBound : ℕ) (hrankBound : 1 ≤ rankBound)
    (affineLoss : ℝ) (haffineLoss : 0 < affineLoss)
    (hslice : RpowAffineSliceStatement
      (distortionRank sigma - 1) proportionConstant 1)
    (G : UniformGenericSharpGeometry s sigma proportionConstant
      rankBound affineLoss) :
    UniformSharpReplacement s sigma where
  rankBound := rankBound
  rankBound_pos := hrankBound
  sigma_one := hsigma
  loss := genericSharpUniformLoss affineLoss
    (uniformSharpProductRankBound rankBound proportionConstant sigma)
    rankBound (distortionRank sigma)
  loss_pos := genericSharpUniformLoss_pos haffineLoss hrankBound
  replace := by
    intro A X hA hcard hXrank hX epsilon hepsilon hsum hpolar hthreshold
    obtain ⟨a, D, ⟨N⟩⟩ :=
      exists_coveredNormalizedReplacement_of_presentation_fixed
        sigma epsilon hslice s hs X hX hA hsigma hepsilon hsum hpolar
          hthreshold
    obtain ⟨S⟩ := G.sharpSection X epsilon N
    obtain ⟨Z, hZrank, hZvolume⟩ :=
      G.affine X epsilon N S hA hcard hXrank hX hsum
    refine ⟨Z, hZrank, ?_⟩
    exact bodyVolume_le_genericSharpUniformLoss
      (r := distortionRank sigma)
      (epsilon := epsilon)
      (exponent := proposition83Exponent X.1 (distortionRank sigma))
      (affineLoss := affineLoss)
      (sharpRankBound :=
        uniformSharpProductRankBound rankBound proportionConstant sigma)
      (rankBound := rankBound) X N S hcard
      (initialRank_le_uniformSharpProductRankBound
        (s := s) X N hXrank)
      hXrank hrankBound hepsilon haffineLoss.le hZvolume

/-- Uniform construction of the geometric packages is now literally the
only premise before the public Bilu--Freiman theorem. -/
theorem biluFreimanStatement_of_uniformGenericSharpGeometry
    (hgeometry : ∀ s d : ℕ, 0 < s → 0 < d →
      ∀ delta : ℝ, 0 < delta →
        ∃ proportionConstant rankBound : ℕ,
          ∃ affineLoss : ℝ,
            1 ≤ rankBound ∧ 0 < affineLoss ∧
            RpowAffineSliceStatement
              (distortionRank (sourceDoublingSigma d delta) - 1)
                proportionConstant 1 ∧
            Nonempty (UniformGenericSharpGeometry s
              (sourceDoublingSigma d delta) proportionConstant
                rankBound affineLoss)) :
    BiluFreimanStatement := by
  apply biluFreimanStatement_of_uniformSharpReplacement
  intro s d hs hd delta hdelta
  obtain ⟨proportionConstant, rankBound, affineLoss,
      hrankBound, haffineLoss, hslice, G⟩ :=
    hgeometry s d hs hd delta hdelta
  obtain ⟨G⟩ := G
  exact ⟨uniformSharpReplacementOfGenericGeometry s hs
    (sourceDoublingSigma d delta)
    (one_le_sourceDoublingSigma d delta) proportionConstant rankBound
    hrankBound affineLoss haffineLoss hslice G⟩

end

end Erdos186.CFP.Bilu.Section4GenericSharpAssembly

#print axioms
  Erdos186.CFP.Bilu.Section4GenericSharpAssembly.uniformSharpReplacementOfGenericGeometry
#print axioms
  Erdos186.CFP.Bilu.Section4GenericSharpAssembly.biluFreimanStatement_of_uniformGenericSharpGeometry
