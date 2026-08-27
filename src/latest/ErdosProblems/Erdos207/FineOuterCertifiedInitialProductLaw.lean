/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.FineOuterCanonicalEnvelopeBounds
import ErdosProblems.Erdos207.OuterSharpRecursiveProductLaw

/-!
# Certified canonical outer product law

This is the assembly boundary for the long initial random-greedy phase.  The
two certificates proved in the preceding files replace every time-dependent
rate, variance, availability, and survival-envelope hypothesis of the sharp
product-law theorem.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem fineOuterCertified_absorberInitialProductLaw
    {V : Type*} [Fintype V] [DecidableEq V]
    {q Mloc fuel sPair sGlobal sInc Kpair Kglobal Kinc Delta delta I Dcut
      K rInc Rinc Umax dmin reserve : ℕ}
    {Habs G : SimpleGraph V} {X U : Finset V}
    {B A : TripleSystemOn V}
    (upper₀ lower₀ : ℕ) (buffer thetaPair : ℝ)
    (rate scale p C : ℝ≥0)
    {Aenv Bscale Q : ℝ≥0}
    (hA2 : HasAbsorberLocalization q Mloc Habs X B)
    (htri : ConsistsOfTriangles G A)
    (houtside₀ : OutsideLeavePairsAlive
      (internalOuterGraph G U)ᶜ U
      (absorberGreedyInitialState
        (absorberErdosForbiddenConfigurationsOn q B)
        (outerOnlyAvailable U A)))
    (hactive₀ : timedSharpScheduledAggregatePairBandActive
      (absorberErdosForbiddenConfigurationsOn q B)
      Kpair Kglobal Kinc Delta delta I Dcut
      (outerSharpLowerAvailability (internalOuterGraph G U)ᶜ U
        (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc)
      (outerSharpLowerSchedule (internalOuterGraph G U)ᶜ U
        (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc)
      (outerSharpUpperAvailability (internalOuterGraph G U)ᶜ U
        (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc)
      (outerSharpUpperSchedule (internalOuterGraph G U)ᶜ U
        (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc) 0
      (absorberGreedyInitialState
        (absorberErdosForbiddenConfigurationsOn q B)
        (outerOnlyAvailable U A)))
    (hcap₀ : HasAvailablePairCutoff upper₀
      (absorberGreedyInitialState
        (absorberErdosForbiddenConfigurationsOn q B)
        (outerOnlyAvailable U A)))
    (hfloor₀ : HasAvailablePairFloor lower₀
      (absorberGreedyInitialState
        (absorberErdosForbiddenConfigurationsOn q B)
        (outerOnlyAvailable U A)))
    (hbounds : ∀ i, i ≤ fuel →
      dmin ≤ outerSharpLowerSchedule (internalOuterGraph G U)ᶜ U
          (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i ∧
      outerSharpUpperSchedule (internalOuterGraph G U)ᶜ U
          (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i ≤ Umax ∧
      Dcut ≤ outerSharpLowerAvailability (internalOuterGraph G U)ᶜ U
          (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i ∧
      0 ≤ (outerSharpEnvelope (internalOuterGraph G U)ᶜ U
          (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i).2 - buffer)
    (hprocess : FineOuterProcessBounds (internalOuterGraph G U)ᶜ U
      (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc K fuel dmin Umax Dcut
      Kpair Kglobal reserve)
    (henvelope : FineOuterZeroEnvelopeBounds (internalOuterGraph G U)ᶜ U
      (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc K fuel dmin Aenv Bscale Q)
    (hgap : Umax < Dcut) (hDcutPos : 0 < Dcut)
    (hUmaxDelta : Umax ≤ Delta) (hdeltaMin : delta ≤ dmin)
    (hsmallBase : 3 + Kpair < delta)
    (hrInc : 0 < rInc)
    (hrIncR : rInc ≤ Rinc)
    (htheta : 0 < thetaPair)
    (hthetaUpper : thetaPair * (fineOuterUpperJump Umax : ℝ) ≤ 1)
    (hthetaLower : thetaPair * ((3 + Kpair : ℕ) : ℝ) ≤ 1)
    (hfailureScale : 1 ≤ scale)
    (hfailureRate : rate ≤ scale * (Fintype.card V + 1 : ℝ≥0)⁻¹)
    (hfailureRatio : (fuel : ℝ≥0) * (Dcut : ℝ≥0)⁻¹ ≤ rate)
    (hcard : 0 < Fintype.card V)
    (hfuel : fuel ≤ Fintype.card V ^ 2)
    (hpointCoefficient :
      ((2 : ℝ≥0) ^ (3 * K)) *
          (Q ^ 3 * (5 * Aenv ^ 3 * Bscale)) ≤ C)
    (hCp : 1 ≤ C * p) (hC : 1 ≤ C)
    (hlarge : ∀ (Qsys : TripleSystemOn V) (E : Finset (Sym2 V)),
      K < Qsys.card + E.card →
      1 ≤ C ^ (Qsys.card + E.card) *
        (p ^ E.card * (Fintype.card V : ℝ≥0)⁻¹ ^ Qsys.card +
          sharpScheduledAbsorberPhaseFailure q Mloc fuel sPair sGlobal sInc
            Kpair Kglobal Kinc I Habs X B scale thetaPair buffer
              (fineOuterVarianceBound Dcut Umax Kpair Kglobal Kinc
                (fineOuterUpperRateBound reserve Umax)
                (fineOuterLowerRateBound Dcut Umax Kinc)))) :
    let F := absorberErdosForbiddenConfigurationsOn q B
    let S₀ := absorberGreedyInitialState F (outerOnlyAvailable U A)
    let D := outerSharpLowerAvailability (internalOuterGraph G U)ᶜ U
      (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc
    let d := outerSharpLowerSchedule (internalOuterGraph G U)ᶜ U
      (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc
    let Mschedule := outerSharpUpperAvailability (internalOuterGraph G U)ᶜ U
      (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc
    let u := outerSharpUpperSchedule (internalOuterGraph G U)ᶜ U
      (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc
    let active := timedSharpScheduledAggregatePairBandActive F Kpair Kglobal
      Kinc Delta delta I Dcut D d Mschedule u
    let L := FiniteLaw.timedStoppedProcessLaw fuel
      (fun _ ↦ greedyKernel F) active S₀
    IsInitialProductBound L (fun z ↦ z.2.chosen) p C
        (sharpScheduledAbsorberPhaseFailure q Mloc fuel sPair sGlobal sInc
          Kpair Kglobal Kinc I Habs X B scale thetaPair buffer
            (fineOuterVarianceBound Dcut Umax Kpair Kglobal Kinc
              (fineOuterUpperRateBound reserve Umax)
              (fineOuterLowerRateBound Dcut Umax Kinc))) ∧
      L.SupportedOn (fun z ↦
        z.2.chosen ⊆ A ∧ IsPackingOn z.2.chosen ∧
          AvoidsForbidden z.2.chosen F ∧
          TrianglesDisjointFrom U z.2.chosen) ∧
      L.probability (fun z ↦ ¬ ∀ v : V,
        (scheduledEdgesAt
          (preliminaryResidualInternalEdges G U z.2.chosen) v).card <
            Rinc) ≤
        trackedResidualOuterFactorialTail V (internalOuterGraph G U) U
          (cumulativeSurvival
            (boundedSharpSurvivalSchedule fuel Mschedule d (3 * rInc))
            fuel)
          (sharpScheduledAbsorberPhaseFailure q Mloc fuel sPair sGlobal sInc
            Kpair Kglobal Kinc I Habs X B scale thetaPair buffer
              (fineOuterVarianceBound Dcut Umax Kpair Kglobal Kinc
                (fineOuterUpperRateBound reserve Umax)
                (fineOuterLowerRateBound Dcut Umax Kinc)))
          rInc Rinc := by
  apply outerSharpRecursive_absorberInitialProductLaw
    (q := q) (Mloc := Mloc) (fuel := fuel) (sPair := sPair)
    (sGlobal := sGlobal) (sInc := sInc) (Kpair := Kpair)
    (Kglobal := Kglobal) (Kinc := Kinc) (Delta := Delta)
    (delta := delta) (I := I) (Dcut := Dcut)
    (JUpper := fineOuterUpperJump Umax) (K := K) (rInc := rInc) (Rinc := Rinc)
    (Umax := Umax)
    (dmin := dmin) (Habs := Habs) (G := G) (X := X) (U := U)
    (B := B) (A := A) upper₀ lower₀ buffer thetaPair
    (fineOuterVarianceBound Dcut Umax Kpair Kglobal Kinc
      (fineOuterUpperRateBound reserve Umax)
      (fineOuterLowerRateBound Dcut Umax Kinc)) rate scale p C
    (R0 := (outerSharpEligiblePairs (internalOuterGraph G U)ᶜ U 0 : ℕ))
    (slope := 0) (Q := Q) (Aenv := Aenv) (Bscale := Bscale)
    hA2 htri houtside₀ hactive₀ hcap₀ hfloor₀ hbounds hgap hDcutPos
    hUmaxDelta hdeltaMin hsmallBase hprocess.upper_jump
    hprocess.lower_death hprocess.variance_upper hprocess.variance_lower
    htheta hthetaUpper hthetaLower (by unfold fineOuterVarianceBound; positivity)
    hfailureScale hfailureRate hfailureRatio hprocess.degree_le_availability
    hprocess.effective hrInc hrIncR hcard hfuel hprocess.upper_availability_pos
    hprocess.half henvelope.envelope_pos henvelope.all_envelope
    (henvelope.envelope_ratio.trans hCp) henvelope.envelope_loss
    hprocess.three henvelope.envelope_eligible henvelope.pair_scale
    henvelope.quadratic hpointCoefficient hCp hC hlarge

end

end Erdos207
