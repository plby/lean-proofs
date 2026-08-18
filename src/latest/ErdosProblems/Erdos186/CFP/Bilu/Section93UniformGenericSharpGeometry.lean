/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Bilu.Section4GenericSharpAssembly
import ErdosProblems.Erdos186.CFP.Bilu.Section91GenericSharpSection
import ErdosProblems.Erdos186.CFP.Bilu.Section92UniformRankRepair
import ErdosProblems.Erdos186.CFP.Bilu.Section93UniformAffineLoss

/-!
# The uniform sharp geometry package

The sharp product presentation from Section 9.1 is first repaired by the
terminating primitive-quotient construction of Section 9.2.  Its normalized
homogeneous affine span is then used as the final presentation.  Freiman's
dimension lemma bounds that span by `2 * ceil sigma`, while the central
section estimate and the rank-weighted repair give a single fixed volume
loss.  This discharges the last geometric record in the Section 4 assembly.
-/

namespace Erdos186.CFP.Bilu.Section93UniformGenericSharpGeometry

open CFP.BiluFreiman
open Section4DecayAlgebra Section4GenericSharpAssembly
open Section4SharpDecayAssembly
open Section5RpowAffineSlice
open Section7BiasedNumerics
open Section8Synthesis Section8PresentationNormalization
open Section9NormalizedReplacement Section9UniformPresentationReplacement
open Section91GenericSharpProduct Section91GenericSharpSection
open Section92PresentationDescent Section92UniformRankRepair
open Section92WeightedRankRepair
open Section93NormalizedAffineBodyPresentation
open Section93UniformAffineLoss

noncomputable section

set_option autoImplicit false

/-- The final affine rank depends only on the source doubling constant. -/
def uniformGenericAffineRankBound (sigma : ℝ) : ℕ :=
  2 * Nat.ceil sigma

theorem one_le_uniformGenericAffineRankBound
    {sigma : ℝ} (hsigma : 1 ≤ sigma) :
    1 ≤ uniformGenericAffineRankBound sigma := by
  have hceil : 0 < Nat.ceil sigma :=
    Nat.ceil_pos.mpr (zero_lt_one.trans_le hsigma)
  unfold uniformGenericAffineRankBound
  omega

/-- The intermediate sharp-product rank ceiling. -/
def uniformGenericSharpRankBound
    (sigma : ℝ) (proportionConstant : ℕ) : ℕ :=
  uniformSharpProductRankBound
    (uniformGenericAffineRankBound sigma) proportionConstant sigma

/-- The combined cost of primitive-quotient repair and affine restriction. -/
def uniformGenericAffineLoss
    (s : ℕ) (sigma : ℝ) (proportionConstant : ℕ) : ℝ :=
  normalizedAffineUniformLoss
      (uniformGenericSharpRankBound sigma proportionConstant) *
    uniformRepairLoss s
      (uniformGenericSharpRankBound sigma proportionConstant)

theorem uniformGenericAffineLoss_pos
    (s : ℕ) (sigma : ℝ) (proportionConstant : ℕ) :
    0 < uniformGenericAffineLoss s sigma proportionConstant := by
  unfold uniformGenericAffineLoss
  exact mul_pos (normalizedAffineUniformLoss_pos _)
    (uniformRepairLoss_pos _ _)

/-- Source-faithful realization of both remaining fields of
`UniformGenericSharpGeometry`. -/
def uniformGenericSharpGeometry
    (s : ℕ) (hs : 0 < s) (sigma : ℝ) (hsigma : 1 ≤ sigma)
    (proportionConstant : ℕ) :
    UniformGenericSharpGeometry s sigma proportionConstant
      (uniformGenericAffineRankBound sigma)
      (uniformGenericAffineLoss s sigma proportionConstant) where
  sharpSection := by
    intro A X epsilon a D N
    exact exists_genericSharpSectionData X N
  affine := by
    intro A X epsilon a D N S hA hcard hXrank hX hsum
    let rankBound := uniformGenericAffineRankBound sigma
    let sharpRankBound :=
      uniformGenericSharpRankBound sigma proportionConstant
    let Y : RankedBodyPresentation A :=
      rankedGenericSharpBodyPresentation X N S hcard
    have hYrank : Y.1 ≤ sharpRankBound := by
      dsimp only [Y, sharpRankBound, uniformGenericSharpRankBound]
      exact initialRank_le_uniformSharpProductRankBound
        (s := s) X N hXrank
    obtain ⟨W, hWinjective, hWrank, hweighted⟩ :=
      exists_enlargedInjective_of_canonicalQuotient
        s sharpRankBound hcard Y hYrank
    have hrepair : bodyVolume W ≤
        uniformRepairLoss s sharpRankBound * bodyVolume Y := by
      simpa only [uniformRepairLoss] using
        (bodyVolume_le_factor_pow_rankBound_of_weighted_le
          (one_le_canonicalRankRepairFactor s sharpRankBound)
          Y W hYrank hweighted)
    by_cases hproper : normalizedHomogeneousSubspace W ≠ ⊤
    · let Z : RankedBodyPresentation A :=
        rankedNormalizedProperAffineBodyPresentation W hA hproper
      refine ⟨Z, ?_, ?_⟩
      · dsimp only [Z, rankBound]
        exact rank_rankedNormalizedProperAffineBodyPresentation_le
          s hs W hWinjective hA sigma (zero_le_one.trans hsigma) hsum hproper
      · have hsection : bodyVolume Z ≤
            normalizedAffineUniformLoss sharpRankBound * bodyVolume W := by
          dsimp only [Z]
          exact
            bodyVolume_rankedNormalizedProperAffineBodyPresentation_le_uniform
              W hA hWrank hproper
        calc
          bodyVolume Z ≤
              normalizedAffineUniformLoss sharpRankBound * bodyVolume W :=
            hsection
          _ ≤ normalizedAffineUniformLoss sharpRankBound *
                (uniformRepairLoss s sharpRankBound * bodyVolume Y) :=
            mul_le_mul_of_nonneg_left hrepair
              (normalizedAffineUniformLoss_pos sharpRankBound).le
          _ = uniformGenericAffineLoss s sigma proportionConstant *
                bodyVolume
                  (rankedGenericSharpBodyPresentation X N S hcard) := by
            dsimp only [Y, sharpRankBound, uniformGenericSharpRankBound,
              uniformGenericAffineLoss]
            ring
    · have htop : normalizedHomogeneousSubspace W = ⊤ :=
        not_ne_iff.mp hproper
      let Z : RankedBodyPresentation A :=
        rankedNormalizedTopAffineBodyPresentation W
      refine ⟨Z, ?_, ?_⟩
      · dsimp only [Z, rankBound]
        exact rank_rankedNormalizedTopAffineBodyPresentation_le
          s hs W hWinjective hA sigma (zero_le_one.trans hsigma) hsum htop
      · have hsection : bodyVolume Z ≤
            normalizedAffineUniformLoss sharpRankBound * bodyVolume W := by
          dsimp only [Z]
          exact bodyVolume_rankedNormalizedTopAffineBodyPresentation_le_uniform
            W hWrank
        calc
          bodyVolume Z ≤
              normalizedAffineUniformLoss sharpRankBound * bodyVolume W :=
            hsection
          _ ≤ normalizedAffineUniformLoss sharpRankBound *
                (uniformRepairLoss s sharpRankBound * bodyVolume Y) :=
            mul_le_mul_of_nonneg_left hrepair
              (normalizedAffineUniformLoss_pos sharpRankBound).le
          _ = uniformGenericAffineLoss s sigma proportionConstant *
                bodyVolume
                  (rankedGenericSharpBodyPresentation X N S hcard) := by
            dsimp only [Y, sharpRankBound, uniformGenericSharpRankBound,
              uniformGenericAffineLoss]
            ring

/-- The complete source-facing Bilu--Freiman statement. -/
theorem biluFreimanStatement : BiluFreimanStatement := by
  apply biluFreimanStatement_of_uniformGenericSharpGeometry
  intro s d hs hd delta hdelta
  let sigma := sourceDoublingSigma d delta
  obtain ⟨proportionConstant, hslice⟩ :=
    exists_rpowAffineSliceStatement
      (distortionRank sigma - 1) 1 zero_lt_one
  refine ⟨proportionConstant, uniformGenericAffineRankBound sigma,
    uniformGenericAffineLoss s sigma proportionConstant,
    one_le_uniformGenericAffineRankBound
      (by simpa only [sigma] using one_le_sourceDoublingSigma d delta),
    uniformGenericAffineLoss_pos s sigma proportionConstant,
    hslice, ?_⟩
  exact ⟨uniformGenericSharpGeometry s hs sigma
    (by simpa only [sigma] using one_le_sourceDoublingSigma d delta)
    proportionConstant⟩

end

end Erdos186.CFP.Bilu.Section93UniformGenericSharpGeometry

#print axioms
  Erdos186.CFP.Bilu.Section93UniformGenericSharpGeometry.uniformGenericSharpGeometry
#print axioms
  Erdos186.CFP.Bilu.Section93UniformGenericSharpGeometry.biluFreimanStatement
