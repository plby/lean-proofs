/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.OuterSharpCubicSchedule
import ErdosProblems.Erdos207.SharpScheduledOuterOnlyAbsorberLaw

/-!
# The recursive outer-sharp initial product law

This file joins the self-consistent recursive pair schedules, their affine
survival envelope, and the sharp absorber failure theorem.  The resulting
interface contains only scalar inequalities: all target trajectories,
availability formulas, positivity clauses, and retrospective product
estimates are discharged internally.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- The exact recursive outer-only schedules give an initial product law as
soon as their uniform floor/ceiling certificate and affine-envelope scalars
are supplied. -/
theorem outerSharpRecursive_absorberInitialProductLaw
    {V : Type*} [Fintype V] [DecidableEq V]
    {q Mloc fuel sPair sGlobal sInc Kpair Kglobal Kinc Delta delta I Dcut
      JUpper K rInc Rinc Umax dmin : ℕ}
    {Habs G : SimpleGraph V} {X U : Finset V}
    {B A : TripleSystemOn V}
    (upper₀ lower₀ : ℕ) (buffer thetaPair vPair : ℝ)
    (rate scale p C : ℝ≥0)
    {R0 slope Q Aenv Bscale : ℝ≥0}
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
    (hgap : Umax < Dcut)
    (hDcutPos : 0 < Dcut)
    (hUmaxDelta : Umax ≤ Delta)
    (hdeltaMin : delta ≤ dmin)
    (hsmallBase : 3 + Kpair < delta)
    (hupperJump : ∀ i, i < fuel →
      sharpScheduledPairUpperRate
        (outerSharpUpperAvailability (internalOuterGraph G U)ᶜ U
          (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i)
        (outerSharpLowerSchedule (internalOuterGraph G U)ᶜ U
          (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i)
        (outerSharpUpperSchedule (internalOuterGraph G U)ᶜ U
          (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i) ≤ JUpper)
    (hlowerDeath : ∀ i, i < fuel →
      sharpScheduledPairLowerRate
        (outerSharpLowerAvailability (internalOuterGraph G U)ᶜ U
          (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i)
        (outerSharpUpperSchedule (internalOuterGraph G U)ᶜ U
          (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i) Kinc ≤
      outerSharpLowerSchedule (internalOuterGraph G U)ᶜ U
        (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i)
    (hvarianceUpper : ∀ i, i < fuel →
      sharpScheduledPairUpperVariance
        (outerSharpLowerAvailability (internalOuterGraph G U)ᶜ U
          (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i)
        (outerSharpUpperSchedule (internalOuterGraph G U)ᶜ U
          (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i)
        Kpair Kglobal
        (sharpScheduledPairUpperRate
          (outerSharpUpperAvailability (internalOuterGraph G U)ᶜ U
            (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i)
          (outerSharpLowerSchedule (internalOuterGraph G U)ᶜ U
            (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i)
          (outerSharpUpperSchedule (internalOuterGraph G U)ᶜ U
            (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i)) ≤ vPair)
    (hvarianceLower : ∀ i, i < fuel →
      sharpScheduledPairLowerVariance
        (outerSharpLowerAvailability (internalOuterGraph G U)ᶜ U
          (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i)
        (outerSharpUpperSchedule (internalOuterGraph G U)ᶜ U
          (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i)
        Kpair Kinc
        (sharpScheduledPairLowerRate
          (outerSharpLowerAvailability (internalOuterGraph G U)ᶜ U
            (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i)
          (outerSharpUpperSchedule (internalOuterGraph G U)ᶜ U
            (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i) Kinc) ≤ vPair)
    (htheta : 0 < thetaPair)
    (hthetaUpper : thetaPair * (JUpper : ℝ) ≤ 1)
    (hthetaLower : thetaPair * ((3 + Kpair : ℕ) : ℝ) ≤ 1)
    (hv : 0 ≤ vPair)
    (hfailureScale : 1 ≤ scale)
    (hfailureRate : rate ≤ scale * (Fintype.card V + 1 : ℝ≥0)⁻¹)
    (hfailureRatio : (fuel : ℝ≥0) * (Dcut : ℝ≥0)⁻¹ ≤
      rate)
    (hdM : ∀ i, i < fuel →
      outerSharpLowerSchedule (internalOuterGraph G U)ᶜ U
          (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i ≤
        outerSharpUpperAvailability (internalOuterGraph G U)ᶜ U
          (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i)
    (heffective : ∀ i, i < fuel →
      outerSharpLowerSchedule (internalOuterGraph G U)ᶜ U
          (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i - 3 * K <
        outerSharpUpperAvailability (internalOuterGraph G U)ᶜ U
          (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i)
    (hrInc : 0 < rInc)
    (hrIncR : rInc ≤ Rinc)
    (hcard : 0 < Fintype.card V)
    (hfuel : fuel ≤ Fintype.card V ^ 2)
    (hMpos : ∀ i, i < fuel →
      0 < outerSharpUpperAvailability (internalOuterGraph G U)ᶜ U
        (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i)
    (hhalf : ∀ i, i < fuel →
      2 * (outerSharpLowerSchedule (internalOuterGraph G U)ᶜ U
          (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i - 3 * K) ≤
        outerSharpUpperAvailability (internalOuterGraph G U)ᶜ U
          (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i)
    (henvelopePos : (fuel : ℝ≥0) * slope < R0)
    (hallEnvelope : ∀ i, i < fuel →
      (outerSharpEligiblePairs (internalOuterGraph G U)ᶜ U i : ℝ≥0) ≤
        affineSurvivalEnvelope R0 slope i)
    (henvelopeRatio : affineSurvivalEnvelope R0 slope fuel / R0 ≤ C * p)
    (henvelopeLoss : ∀ i, i < fuel →
      slope * (outerSharpUpperSchedule (internalOuterGraph G U)ᶜ U
          (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i : ℕ) ≤
        3 * (outerSharpLowerSchedule (internalOuterGraph G U)ᶜ U
          (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i - 3 * K : ℕ))
    (hthree : ∀ i, i < fuel →
      3 ≤ outerSharpEligiblePairs (internalOuterGraph G U)ᶜ U i *
        outerSharpLowerSchedule (internalOuterGraph G U)ᶜ U
          (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i)
    (henvelopeEligible : ∀ i, i < fuel →
      affineSurvivalEnvelope R0 slope i ≤
        Aenv * (outerSharpEligiblePairs
          (internalOuterGraph G U)ᶜ U i : ℕ))
    (hpairScale : ∀ i, i < fuel →
      ((outerSharpEligiblePairs
          (internalOuterGraph G U)ᶜ U i : ℕ) : ℝ≥0) ^ 2 ≤
        Bscale * (Fintype.card V : ℝ≥0) ^ 3 *
          (outerSharpLowerSchedule (internalOuterGraph G U)ᶜ U
            (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i : ℕ))
    (hquadratic : (Fintype.card V : ℝ≥0) ^ 2 ≤ Q * R0)
    (hpointCoefficient :
      ((2 : ℝ≥0) ^ (3 * K)) *
          (Q ^ 3 * (5 * Aenv ^ 3 * Bscale)) ≤ C)
    (hCp : 1 ≤ C * p) (hC : 1 ≤ C)
    (hlarge : ∀ (Qsys : TripleSystemOn V) (E : Finset (Sym2 V)),
      K < Qsys.card + E.card →
      1 ≤ C ^ (Qsys.card + E.card) *
        (p ^ E.card * (Fintype.card V : ℝ≥0)⁻¹ ^ Qsys.card +
          sharpScheduledAbsorberPhaseFailure q Mloc fuel sPair sGlobal sInc
            Kpair Kglobal Kinc I Habs X B scale thetaPair buffer vPair)) :
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
          Kpair Kglobal Kinc I Habs X B scale thetaPair buffer vPair) ∧
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
            Kpair Kglobal Kinc I Habs X B scale thetaPair buffer vPair)
          rInc Rinc := by
  dsimp only
  let Hout := (internalOuterGraph G U)ᶜ
  let D := outerSharpLowerAvailability Hout U
    (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc
  let d := outerSharpLowerSchedule Hout U
    (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc
  let Mschedule := outerSharpUpperAvailability Hout U
    (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc
  let u := outerSharpUpperSchedule Hout U
    (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc
  have htargets := outerSharpRecursive_target_bounds
    (F := absorberErdosForbiddenConfigurationsOn q B)
    (S₀ := absorberGreedyInitialState
      (absorberErdosForbiddenConfigurationsOn q B) (outerOnlyAvailable U A))
    Hout U upper₀ lower₀ buffer Kinc fuel Delta delta hcap₀ hfloor₀
    (fun i hi ↦ (hbounds i hi).2.2.2)
    (fun i hi ↦ (hbounds i hi).2.1.trans hUmaxDelta)
    (fun i hi ↦ hdeltaMin.trans (hbounds i hi).1)
  have hDpos : ∀ i, i ≤ fuel → 0 < D i := by
    intro i hi
    exact hDcutPos.trans_le (hbounds i hi).2.2.1
  have hDgap : ∀ i, i < fuel → u i < D i := by
    intro i hi
    exact (hbounds i (Nat.le_of_lt hi)).2.1.trans_lt
      (hgap.trans_le (hbounds i (Nat.le_of_lt hi)).2.2.1)
  have hsurvival : cumulativeSurvival
      (boundedSharpSurvivalSchedule fuel Mschedule d (3 * K)) fuel ≤ C * p := by
    apply (cumulativeSurvival_outerSharpRecursive_le Hout U
      (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc fuel (3 * K)
      hMpos henvelopePos hallEnvelope henvelopeLoss).trans
    exact henvelopeRatio
  have hpoint : transferPointWeight
      (boundedSharpSurvivalSchedule fuel Mschedule d (3 * K))
      (boundedSharpTransferSchedule fuel D Mschedule d (3 * K)) fuel ≤
        C * (Fintype.card V : ℝ≥0)⁻¹ := by
    apply (transferPointWeight_outerSharpRecursive_le_of_half Hout U
      (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc fuel K hcard hfuel hMpos
      hhalf henvelopePos hallEnvelope henvelopeLoss hthree
      henvelopeEligible hpairScale hquadratic).trans
    exact mul_le_mul_of_nonneg_right hpointCoefficient zero_le
  apply sharpScheduledOuterOnly_absorberInitialProductLaw
    (q := q) (M := Mloc) (fuel := fuel) (sPair := sPair)
    (sGlobal := sGlobal) (sInc := sInc) (Kpair := Kpair)
    (Kglobal := Kglobal) (Kinc := Kinc) (Delta := Delta)
    (delta := delta) (I := I) (Dcut := Dcut) (JUpper := JUpper)
    (K := K) (rInc := rInc) (Rinc := Rinc)
    (Habs := Habs) (G := G) (X := X) (U := U)
    (B := B) (A := A) D d Mschedule u thetaPair buffer vPair
    rate scale p C
    hA2 htri houtside₀ hsmallBase hactive₀ hDcutPos hDpos hDgap
    (fun i hi ↦ (hbounds i hi).2.2.1)
    htargets.1 htargets.2.1 htargets.2.2.1 htargets.2.2.2
    (fun i _hi ↦ le_rfl) (fun i _hi ↦ le_rfl)
    (fun i hi ↦ by
      change 1 ≤ outerSharpLowerSchedule Hout U
        (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i
      have hs := hsmallBase.trans_le
        (hdeltaMin.trans (hbounds i (Nat.le_of_lt hi)).1)
      exact Nat.succ_le_iff.mpr ((by omega : 0 < 3 + Kpair).trans hs))
    (fun i hi ↦ hsmallBase.trans_le
      (hdeltaMin.trans (hbounds i (Nat.le_of_lt hi)).1))
    hupperJump hlowerDeath hvarianceUpper hvarianceLower htheta hthetaUpper
    hthetaLower hv hfailureScale hfailureRate hfailureRatio hdM heffective
    (fun i hi ↦ by
      have hle := hdM i hi
      change d i ≤ Mschedule i at hle
      have hpos : 0 < d i := by
        have hdminPos : 0 < dmin := by
          have hs := hsmallBase.trans_le hdeltaMin
          omega
        have hraw := hdminPos.trans_le
          (hbounds i (Nat.le_of_lt hi)).1
        simpa only [d, Hout] using hraw
      omega)
    hrIncR hsurvival hpoint hCp hC hlarge

end

end Erdos207
