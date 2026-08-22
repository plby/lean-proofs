/-
Copyright (c) 2026 The Erdos Problems Formalization Project.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Erdos Problems Formalization Project
-/
import ErdosProblems.Erdos1165.Proposition13LiteralAssembly
import ErdosProblems.Erdos1165.AnnularProfileSequentialUpper

/-!
# Literal far-pair conditional tail from a prefix mixture

This downstream adapter specializes `AppendixPairCrossingTail` to the exact
explicit envelope stored by `ActualMarkedFarPairData`.  It isolates the
remaining spatial obligation: the reference marked event must be bounded by
the finite mixture of its actual retained prefix weights and the ideal
negative-binomial continuation weights.
-/

open MeasureTheory
open scoped BigOperators ENNReal

namespace Erdos1165.AppendixPairCrossingTailLiteral

open AppendixFirstMoment AppendixPair AppendixPairCrossingTail AppendixPairMoment
open AppendixPairReferenceMass
open AnnularProfileSequentialUpper
open MarkedTerminalDisintegration ProfileConditionalTailUpper
open ProfileWeightUpper Proposition13LiteralAssembly Proposition13Scales
open Proposition13Assembly

noncomputable section

/-- Exact constructor for the retained-outside `successful_le` field.  The
literal retained event need only be contained in one complete successful
profile event; the latter is bounded by the disjoint sequential upper
family. -/
theorem successful_le_pairPointEnvelope_of_sequentialUpperFamily
    {delta : ℝ} {blockIndex blockStart : ℕ} {x : Point}
    {historyGain : ℝ} (successful : Set StepPath)
    (family : SequentialProfileUpperFamily blockStart
      (scaleIndex delta blockIndex) chosenProfileDelta historyGain x)
    (hsubset : successful ⊆ stoppedSuccessfulPointEvent blockStart
      (scaleIndex delta blockIndex) chosenProfileDelta x)
    (hq : profileUpperTailStart ≤ scaleIndex delta blockIndex)
    (hgain : historyGain ≤ Real.exp prefixProfileCostDeficit) :
    fairSteps.real successful ≤ pairPointEnvelope delta blockIndex := by
  have hsuccess := (measureReal_mono hsubset).trans
    family.measureReal_le_gain_mul_constrainedProfileWeight
  have hprofile := constrainedProfileWeight_le_exp hq
  have hprofile0 : 0 ≤
      constrainedProfileWeight (scaleIndex delta blockIndex)
        chosenProfileDelta := constrainedProfileWeight_nonneg _ _
  have hprofileChosen :
      constrainedProfileWeight (scaleIndex delta blockIndex)
          chosenProfileDelta ≤
        Real.exp (-2 * (scaleIndex delta blockIndex : ℝ) +
          profileUpperConstant *
            (scaleIndex delta blockIndex : ℝ) ^ (3 / 5 : ℝ)) := by
    simpa only [chosenProfileDelta, profileUpperDelta, neg_mul] using hprofile
  calc
    fairSteps.real successful ≤ historyGain *
        constrainedProfileWeight (scaleIndex delta blockIndex)
          chosenProfileDelta := hsuccess
    _ ≤ Real.exp prefixProfileCostDeficit *
        Real.exp (-2 * (scaleIndex delta blockIndex : ℝ) +
          profileUpperConstant *
            (scaleIndex delta blockIndex : ℝ) ^ (3 / 5 : ℝ)) :=
      mul_le_mul hgain hprofileChosen hprofile0
        (Real.exp_nonneg prefixProfileCostDeficit)
    _ = pairPointEnvelope delta blockIndex := by
      unfold pairPointEnvelope
      rw [← Real.exp_add]
      congr 1
      ring

/-- Exact constructor for the scalar `referenceTail_le` field of
`ActualMarkedFarPairData`.  There is no atomwise prefix lower bound: the
actual nonnegative prefix weights are summed first and need only have total
mass at most one. -/
theorem referenceTail_le_pairPointEnvelope_of_profilePrefixMixture
    {delta : ℝ} {blockIndex coordinates start n : ℕ}
    (referenceMass : Fin coordinates → ℕ → ℝ≥0∞)
    (visitEvent : Set (Fin coordinates → ℕ))
    (prefixMass : Profile start → ℝ)
    (hn : n = scaleIndex delta blockIndex)
    (htailStart : profileUpperTailStart ≤ start)
    (hstartn : start ≤ n)
    (hcutoff : GaussianGeometricCutoff.geometricCutoff ≤ start)
    (hfactor :
      (referenceEventMass referenceMass visitEvent).toReal =
        crossingMixture (constrainedProfiles start profileUpperDelta)
          prefixMass
          (fun pref ↦ constrainedProfileTailWeight n start
            ((show 2 ≤ profileUpperTailStart by
              norm_num [profileUpperTailStart]).trans htailStart)
            hstartn pref profileUpperDelta))
    (hprefix : ∀ pref ∈ constrainedProfiles start profileUpperDelta,
      0 ≤ prefixMass pref)
    (hsum : ∑ pref ∈ constrainedProfiles start profileUpperDelta,
      prefixMass pref ≤ 1) :
    (referenceEventMass referenceMass visitEvent).toReal ≤
      pairPointEnvelope delta blockIndex / prefixProfileLower start := by
  subst n
  simpa only [pairPointEnvelope] using
    (referenceEventMass_le_exp_add_prefixDeficit_div_of_profilePrefixMixture
      referenceMass visitEvent prefixMass htailStart hstartn hcutoff
      hfactor hprefix hsum)

/-- Coefficient-bearing constructor for the scalar reference-tail field.
This is the source-facing form for A.6: the literal stopped-word mass is at
most a small comparison coefficient times the ideal prefix/tail mixture.
The coefficient is charged to the checked prefix cost before dividing by
the aggregate prefix lower. -/
theorem referenceTail_le_pairPointEnvelope_of_profilePrefixMixtureUpper
    {delta : ℝ} {blockIndex coordinates start n : ℕ}
    (referenceMass : Fin coordinates → ℕ → ℝ≥0∞)
    (visitEvent : Set (Fin coordinates → ℕ))
    (prefixMass : Profile start → ℝ) (coefficient : ℝ)
    (hn : n = scaleIndex delta blockIndex)
    (htailStart : profileUpperTailStart ≤ start)
    (hstartn : start ≤ n)
    (hcutoff : GaussianGeometricCutoff.geometricCutoff ≤ start)
    (hfactor :
      (referenceEventMass referenceMass visitEvent).toReal ≤
        coefficient *
          crossingMixture (constrainedProfiles start profileUpperDelta)
            prefixMass
            (fun pref ↦ constrainedProfileTailWeight n start
              ((show 2 ≤ profileUpperTailStart by
                norm_num [profileUpperTailStart]).trans htailStart)
              hstartn pref profileUpperDelta))
    (hcoefficient0 : 0 ≤ coefficient)
    (hcoefficient : coefficient ≤
      Real.exp (prefixProfileCost start + prefixProfileCostDeficit))
    (hprefix : ∀ pref ∈ constrainedProfiles start profileUpperDelta,
      0 ≤ prefixMass pref)
    (hsum : ∑ pref ∈ constrainedProfiles start profileUpperDelta,
      prefixMass pref ≤ 1) :
    (referenceEventMass referenceMass visitEvent).toReal ≤
      pairPointEnvelope delta blockIndex / prefixProfileLower start := by
  subst n
  simpa only [pairPointEnvelope] using
    (referenceEventMass_le_exp_add_prefixDeficit_div_of_profilePrefixMixtureUpper
      referenceMass visitEvent prefixMass coefficient htailStart hstartn
      hcutoff hfactor hcoefficient0 hcoefficient hprefix hsum)

/-- Specialization at the literal padded separation-prefix scale. -/
theorem referenceTail_le_actualPairField_of_profilePrefixMixture
    {delta : ℝ} {blockIndex coordinates : ℕ} {x y : Point}
    (referenceMass : Fin coordinates → ℕ → ℝ≥0∞)
    (visitEvent : Set (Fin coordinates → ℕ))
    (prefixMass :
      Profile (pairPrefixScale (scaleIndex delta blockIndex)
        (separationLevel (scaleIndex delta blockIndex) x y)) → ℝ)
    (htailStart : profileUpperTailStart ≤
      pairPrefixScale (scaleIndex delta blockIndex)
        (separationLevel (scaleIndex delta blockIndex) x y))
    (hstartn : pairPrefixScale (scaleIndex delta blockIndex)
      (separationLevel (scaleIndex delta blockIndex) x y) ≤
        scaleIndex delta blockIndex)
    (hcutoff : GaussianGeometricCutoff.geometricCutoff ≤
      pairPrefixScale (scaleIndex delta blockIndex)
        (separationLevel (scaleIndex delta blockIndex) x y))
    (hfactor :
      (referenceEventMass referenceMass visitEvent).toReal =
        crossingMixture
          (constrainedProfiles
            (pairPrefixScale (scaleIndex delta blockIndex)
              (separationLevel (scaleIndex delta blockIndex) x y))
            profileUpperDelta)
          prefixMass
          (fun pref ↦ constrainedProfileTailWeight
            (scaleIndex delta blockIndex)
            (pairPrefixScale (scaleIndex delta blockIndex)
              (separationLevel (scaleIndex delta blockIndex) x y))
            ((show 2 ≤ profileUpperTailStart by
              norm_num [profileUpperTailStart]).trans htailStart)
            hstartn pref profileUpperDelta))
    (hprefix : ∀ pref ∈ constrainedProfiles
        (pairPrefixScale (scaleIndex delta blockIndex)
          (separationLevel (scaleIndex delta blockIndex) x y))
        profileUpperDelta,
      0 ≤ prefixMass pref)
    (hsum : ∑ pref ∈ constrainedProfiles
        (pairPrefixScale (scaleIndex delta blockIndex)
          (separationLevel (scaleIndex delta blockIndex) x y))
        profileUpperDelta,
      prefixMass pref ≤ 1) :
    (referenceEventMass referenceMass visitEvent).toReal ≤
      pairPointEnvelope delta blockIndex /
        prefixProfileLower
          (pairPrefixScale (scaleIndex delta blockIndex)
            (separationLevel (scaleIndex delta blockIndex) x y)) := by
  exact referenceTail_le_pairPointEnvelope_of_profilePrefixMixture
    referenceMass visitEvent prefixMass rfl htailStart hstartn hcutoff
    hfactor hprefix hsum

/-- Coefficient-bearing specialization at the literal padded
separation-prefix scale. -/
theorem referenceTail_le_actualPairField_of_profilePrefixMixtureUpper
    {delta : ℝ} {blockIndex coordinates : ℕ} {x y : Point}
    (referenceMass : Fin coordinates → ℕ → ℝ≥0∞)
    (visitEvent : Set (Fin coordinates → ℕ))
    (prefixMass :
      Profile (pairPrefixScale (scaleIndex delta blockIndex)
        (separationLevel (scaleIndex delta blockIndex) x y)) → ℝ)
    (coefficient : ℝ)
    (htailStart : profileUpperTailStart ≤
      pairPrefixScale (scaleIndex delta blockIndex)
        (separationLevel (scaleIndex delta blockIndex) x y))
    (hstartn : pairPrefixScale (scaleIndex delta blockIndex)
      (separationLevel (scaleIndex delta blockIndex) x y) ≤
        scaleIndex delta blockIndex)
    (hcutoff : GaussianGeometricCutoff.geometricCutoff ≤
      pairPrefixScale (scaleIndex delta blockIndex)
        (separationLevel (scaleIndex delta blockIndex) x y))
    (hfactor :
      (referenceEventMass referenceMass visitEvent).toReal ≤
        coefficient *
          crossingMixture
            (constrainedProfiles
              (pairPrefixScale (scaleIndex delta blockIndex)
                (separationLevel (scaleIndex delta blockIndex) x y))
              profileUpperDelta)
            prefixMass
            (fun pref ↦ constrainedProfileTailWeight
              (scaleIndex delta blockIndex)
              (pairPrefixScale (scaleIndex delta blockIndex)
                (separationLevel (scaleIndex delta blockIndex) x y))
              ((show 2 ≤ profileUpperTailStart by
                norm_num [profileUpperTailStart]).trans htailStart)
              hstartn pref profileUpperDelta))
    (hcoefficient0 : 0 ≤ coefficient)
    (hcoefficient : coefficient ≤
      Real.exp
        (prefixProfileCost
            (pairPrefixScale (scaleIndex delta blockIndex)
              (separationLevel (scaleIndex delta blockIndex) x y)) +
          prefixProfileCostDeficit))
    (hprefix : ∀ pref ∈ constrainedProfiles
        (pairPrefixScale (scaleIndex delta blockIndex)
          (separationLevel (scaleIndex delta blockIndex) x y))
        profileUpperDelta,
      0 ≤ prefixMass pref)
    (hsum : ∑ pref ∈ constrainedProfiles
        (pairPrefixScale (scaleIndex delta blockIndex)
          (separationLevel (scaleIndex delta blockIndex) x y))
        profileUpperDelta,
      prefixMass pref ≤ 1) :
    (referenceEventMass referenceMass visitEvent).toReal ≤
      pairPointEnvelope delta blockIndex /
        prefixProfileLower
          (pairPrefixScale (scaleIndex delta blockIndex)
            (separationLevel (scaleIndex delta blockIndex) x y)) := by
  exact referenceTail_le_pairPointEnvelope_of_profilePrefixMixtureUpper
    referenceMass visitEvent prefixMass coefficient rfl htailStart hstartn
    hcutoff hfactor hcoefficient0 hcoefficient hprefix hsum

/-- The literal A.6 specialization: an accumulated chronological-row
coefficient bounded by `exp 1` is absorbed by the checked prefix budget.
This is the direct endpoint for `AnnularProfileUniformUpperLoss`; it avoids
re-exposing the artificial-looking larger coefficient inequality to the
walk-facing radial-word construction. -/
theorem referenceTail_le_actualPairField_of_profilePrefixMixtureExpOne
    {delta : ℝ} {blockIndex coordinates : ℕ} {x y : Point}
    (referenceMass : Fin coordinates → ℕ → ℝ≥0∞)
    (visitEvent : Set (Fin coordinates → ℕ))
    (prefixMass :
      Profile (pairPrefixScale (scaleIndex delta blockIndex)
        (separationLevel (scaleIndex delta blockIndex) x y)) → ℝ)
    (coefficient : ℝ)
    (htailStart : profileUpperTailStart ≤
      pairPrefixScale (scaleIndex delta blockIndex)
        (separationLevel (scaleIndex delta blockIndex) x y))
    (hstartn : pairPrefixScale (scaleIndex delta blockIndex)
      (separationLevel (scaleIndex delta blockIndex) x y) ≤
        scaleIndex delta blockIndex)
    (hcutoff : GaussianGeometricCutoff.geometricCutoff ≤
      pairPrefixScale (scaleIndex delta blockIndex)
        (separationLevel (scaleIndex delta blockIndex) x y))
    (hprefixPos : 1 ≤ pairPrefixScale (scaleIndex delta blockIndex)
      (separationLevel (scaleIndex delta blockIndex) x y))
    (hfactor :
      (referenceEventMass referenceMass visitEvent).toReal ≤
        coefficient *
          crossingMixture
            (constrainedProfiles
              (pairPrefixScale (scaleIndex delta blockIndex)
                (separationLevel (scaleIndex delta blockIndex) x y))
              profileUpperDelta)
            prefixMass
            (fun pref ↦ constrainedProfileTailWeight
              (scaleIndex delta blockIndex)
              (pairPrefixScale (scaleIndex delta blockIndex)
                (separationLevel (scaleIndex delta blockIndex) x y))
              ((show 2 ≤ profileUpperTailStart by
                norm_num [profileUpperTailStart]).trans htailStart)
              hstartn pref profileUpperDelta))
    (hcoefficient0 : 0 ≤ coefficient)
    (hcoefficient : coefficient ≤ Real.exp 1)
    (hprefix : ∀ pref ∈ constrainedProfiles
        (pairPrefixScale (scaleIndex delta blockIndex)
          (separationLevel (scaleIndex delta blockIndex) x y))
        profileUpperDelta,
      0 ≤ prefixMass pref)
    (hsum : ∑ pref ∈ constrainedProfiles
        (pairPrefixScale (scaleIndex delta blockIndex)
          (separationLevel (scaleIndex delta blockIndex) x y))
        profileUpperDelta,
      prefixMass pref ≤ 1) :
    (referenceEventMass referenceMass visitEvent).toReal ≤
      pairPointEnvelope delta blockIndex /
        prefixProfileLower
          (pairPrefixScale (scaleIndex delta blockIndex)
            (separationLevel (scaleIndex delta blockIndex) x y)) := by
  apply referenceTail_le_actualPairField_of_profilePrefixMixtureUpper
    referenceMass visitEvent prefixMass coefficient htailStart hstartn hcutoff
    hfactor hcoefficient0 _ hprefix hsum
  exact coefficient_le_exp_prefixProfileCost_add_deficit_of_le_exp_one
    hprefixPos hcoefficient

/-- Exact constructor for the revised, source-correct `jointTail_le` field.
The complementary stopped skeleton carries the radial-profile continuation,
while `referenceMass` remains only the normalized terminal point-visit law.
The finite prefix mixture is explicit and is bounded before it is multiplied
by the retained one-point event. -/
theorem jointTail_le_actualPairField_of_twoStageProfilePrefixMixtureExpOne
    {delta : ℝ} {blockIndex coordinates : ℕ} {x y : Point}
    (referenceMass : Fin coordinates → ℕ → ℝ≥0∞)
    (visitEvent : Set (Fin coordinates → ℕ))
    (successful retained : Set StepPath)
    (prefixMass :
      Profile (pairPrefixScale (scaleIndex delta blockIndex)
        (separationLevel (scaleIndex delta blockIndex) x y)) → ℝ)
    (coefficient : ℝ)
    (htailStart : profileUpperTailStart ≤
      pairPrefixScale (scaleIndex delta blockIndex)
        (separationLevel (scaleIndex delta blockIndex) x y))
    (hstartn : pairPrefixScale (scaleIndex delta blockIndex)
      (separationLevel (scaleIndex delta blockIndex) x y) ≤
        scaleIndex delta blockIndex)
    (hcutoff : GaussianGeometricCutoff.geometricCutoff ≤
      pairPrefixScale (scaleIndex delta blockIndex)
        (separationLevel (scaleIndex delta blockIndex) x y))
    (hprefixPos : 1 ≤ pairPrefixScale (scaleIndex delta blockIndex)
      (separationLevel (scaleIndex delta blockIndex) x y))
    (hterminal :
      (referenceEventMass referenceMass visitEvent).toReal ≤ 1)
    (hsuccessful : fairSteps.real successful ≤
      (coefficient *
        crossingMixture
          (constrainedProfiles
            (pairPrefixScale (scaleIndex delta blockIndex)
              (separationLevel (scaleIndex delta blockIndex) x y))
            profileUpperDelta)
          prefixMass
          (fun pref ↦ constrainedProfileTailWeight
            (scaleIndex delta blockIndex)
            (pairPrefixScale (scaleIndex delta blockIndex)
              (separationLevel (scaleIndex delta blockIndex) x y))
            ((show 2 ≤ profileUpperTailStart by
              norm_num [profileUpperTailStart]).trans htailStart)
            hstartn pref profileUpperDelta)) * fairSteps.real retained)
    (hretained : fairSteps.real retained ≤
      pairPointEnvelope delta blockIndex)
    (hcoefficient0 : 0 ≤ coefficient)
    (hcoefficient : coefficient ≤ Real.exp 1)
    (hprefix : ∀ pref ∈ constrainedProfiles
        (pairPrefixScale (scaleIndex delta blockIndex)
          (separationLevel (scaleIndex delta blockIndex) x y))
        profileUpperDelta,
      0 ≤ prefixMass pref)
    (hsum : ∑ pref ∈ constrainedProfiles
        (pairPrefixScale (scaleIndex delta blockIndex)
          (separationLevel (scaleIndex delta blockIndex) x y))
        profileUpperDelta,
      prefixMass pref ≤ 1) :
    (referenceEventMass referenceMass visitEvent).toReal *
        fairSteps.real successful ≤
      pairPointEnvelope delta blockIndex ^ 2 /
        prefixProfileLower
          (pairPrefixScale (scaleIndex delta blockIndex)
            (separationLevel (scaleIndex delta blockIndex) x y)) := by
  let start := pairPrefixScale (scaleIndex delta blockIndex)
    (separationLevel (scaleIndex delta blockIndex) x y)
  let radialTail : ℝ := coefficient *
    crossingMixture (constrainedProfiles start profileUpperDelta)
      prefixMass
      (fun pref ↦ constrainedProfileTailWeight
        (scaleIndex delta blockIndex) start
        ((show 2 ≤ profileUpperTailStart by
          norm_num [profileUpperTailStart]).trans htailStart)
        hstartn pref profileUpperDelta)
  have hcoefficientBudget : coefficient ≤
      Real.exp (prefixProfileCost start + prefixProfileCostDeficit) :=
    coefficient_le_exp_prefixProfileCost_add_deficit_of_le_exp_one
      hprefixPos hcoefficient
  have hradial : radialTail ≤
      pairPointEnvelope delta blockIndex / prefixProfileLower start := by
    dsimp only [radialTail]
    simpa only [pairPointEnvelope, start] using
      (coefficient_mul_profilePrefixMixture_le_exp_add_prefixDeficit_div
        prefixMass coefficient htailStart hstartn hcutoff hcoefficient0
        hcoefficientBudget hprefix hsum)
  apply referenceEventMass_mul_successful_le_pairPrefixEnvelope_of_twoStage
    referenceMass visitEvent successful retained radialTail
      (pairPointEnvelope delta blockIndex)
      (pairPointEnvelope_nonneg _ _) hterminal
  · simpa only [radialTail, start] using hsuccessful
  · exact hretained
  · simpa only [start] using hradial

/-- Direct finite-mixture constructor for the revised
`ActualMarkedFarPairData.radialTail_le` field.  The literal asymmetric atom
may provide a one-sided radial-tail comparison rather than an exact mixture
identity. -/
theorem radialTail_le_actualPairField_of_profilePrefixMixtureExpOne
    {delta : ℝ} {blockIndex : ℕ} {x y : Point}
    (radialTail : ℝ)
    (prefixMass :
      Profile (pairPrefixScale (scaleIndex delta blockIndex)
        (separationLevel (scaleIndex delta blockIndex) x y)) → ℝ)
    (coefficient : ℝ)
    (htailStart : profileUpperTailStart ≤
      pairPrefixScale (scaleIndex delta blockIndex)
        (separationLevel (scaleIndex delta blockIndex) x y))
    (hstartn : pairPrefixScale (scaleIndex delta blockIndex)
      (separationLevel (scaleIndex delta blockIndex) x y) ≤
        scaleIndex delta blockIndex)
    (hcutoff : GaussianGeometricCutoff.geometricCutoff ≤
      pairPrefixScale (scaleIndex delta blockIndex)
        (separationLevel (scaleIndex delta blockIndex) x y))
    (hprefixPos : 1 ≤ pairPrefixScale (scaleIndex delta blockIndex)
      (separationLevel (scaleIndex delta blockIndex) x y))
    (hradial : radialTail ≤ coefficient *
      crossingMixture
        (constrainedProfiles
          (pairPrefixScale (scaleIndex delta blockIndex)
            (separationLevel (scaleIndex delta blockIndex) x y))
          profileUpperDelta)
        prefixMass
        (fun pref ↦ constrainedProfileTailWeight
          (scaleIndex delta blockIndex)
          (pairPrefixScale (scaleIndex delta blockIndex)
            (separationLevel (scaleIndex delta blockIndex) x y))
          ((show 2 ≤ profileUpperTailStart by
            norm_num [profileUpperTailStart]).trans htailStart)
          hstartn pref profileUpperDelta))
    (hcoefficient0 : 0 ≤ coefficient)
    (hcoefficient : coefficient ≤ Real.exp 1)
    (hprefix : ∀ pref ∈ constrainedProfiles
        (pairPrefixScale (scaleIndex delta blockIndex)
          (separationLevel (scaleIndex delta blockIndex) x y))
        profileUpperDelta,
      0 ≤ prefixMass pref)
    (hsum : ∑ pref ∈ constrainedProfiles
        (pairPrefixScale (scaleIndex delta blockIndex)
          (separationLevel (scaleIndex delta blockIndex) x y))
        profileUpperDelta,
      prefixMass pref ≤ 1) :
    radialTail ≤ pairPointEnvelope delta blockIndex /
      prefixProfileLower
        (pairPrefixScale (scaleIndex delta blockIndex)
          (separationLevel (scaleIndex delta blockIndex) x y)) := by
  let start := pairPrefixScale (scaleIndex delta blockIndex)
    (separationLevel (scaleIndex delta blockIndex) x y)
  have hcoefficientBudget : coefficient ≤
      Real.exp (prefixProfileCost start + prefixProfileCostDeficit) :=
    coefficient_le_exp_prefixProfileCost_add_deficit_of_le_exp_one
      hprefixPos hcoefficient
  apply hradial.trans
  simpa only [pairPointEnvelope, start] using
    (coefficient_mul_profilePrefixMixture_le_exp_add_prefixDeficit_div
      prefixMass coefficient htailStart hstartn hcutoff hcoefficient0
      hcoefficientBudget hprefix hsum)

end

end Erdos1165.AppendixPairCrossingTailLiteral
