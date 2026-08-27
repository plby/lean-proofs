/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SharpScheduledAbsorberFailure
import ErdosProblems.Erdos207.OuterOnlySharpScheduledInitialProductLaw
import ErdosProblems.Erdos207.TrackedResidualFactorialTail

/-!
# Concrete sharp outer-only initial law

This wrapper discharges the inactive-probability hypothesis of the sharp
initial product law by the five-event absorber failure estimate.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem sharpScheduledOuterOnly_absorberInitialProductLaw
    {V : Type*} [Fintype V] [DecidableEq V]
    {q M fuel sPair sGlobal sInc Kpair Kglobal Kinc Delta delta I Dcut
      JUpper K rInc Rinc : ℕ}
    {Habs G : SimpleGraph V} {X U : Finset V}
    {B A : TripleSystemOn V}
    (D d Mschedule u : ℕ → ℕ) (thetaPair aPair vPair : ℝ)
    (rate scale p C : ℝ≥0)
    (hA2 : HasAbsorberLocalization q M Habs X B)
    (htri : ConsistsOfTriangles G A)
    (houtside₀ : OutsideLeavePairsAlive
      (internalOuterGraph G U)ᶜ U
      (absorberGreedyInitialState
        (absorberErdosForbiddenConfigurationsOn q B)
        (outerOnlyAvailable U A)))
    (hsmallBase : 3 + Kpair < delta)
    (hactive₀ : timedSharpScheduledAggregatePairBandActive
      (absorberErdosForbiddenConfigurationsOn q B)
      Kpair Kglobal Kinc Delta delta I Dcut D d Mschedule u 0
      (absorberGreedyInitialState
        (absorberErdosForbiddenConfigurationsOn q B)
        (outerOnlyAvailable U A)))
    (hDcutPos : 0 < Dcut)
    (hDpos : ∀ i, i ≤ fuel → 0 < D i)
    (hDgap : ∀ i, i < fuel → u i < D i)
    (hDcut : ∀ i, i ≤ fuel → Dcut ≤ D i)
    (hbaseCap : ∀ P : PairOn V, ∀ i, i ≤ fuel →
      sharpScheduledPairUpperTarget
          (absorberGreedyInitialState
            (absorberErdosForbiddenConfigurationsOn q B)
            (outerOnlyAvailable U A)) Mschedule d u P i + aPair ≤
        ((Delta + 1 : ℕ) : ℝ))
    (hbaseFloor : ∀ P : PairOn V, ∀ i, i ≤ fuel →
      PairAlive P.1
          (absorberGreedyInitialState
            (absorberErdosForbiddenConfigurationsOn q B)
            (outerOnlyAvailable U A)) →
        (delta : ℝ) ≤
          sharpScheduledPairLowerTarget
              (absorberGreedyInitialState
                (absorberErdosForbiddenConfigurationsOn q B)
                (outerOnlyAvailable U A)) D u Kinc P i - aPair)
    (hscheduledCap : ∀ P : PairOn V, ∀ i, i ≤ fuel →
      sharpScheduledPairUpperTarget
          (absorberGreedyInitialState
            (absorberErdosForbiddenConfigurationsOn q B)
            (outerOnlyAvailable U A)) Mschedule d u P i + aPair ≤
        ((u i + 1 : ℕ) : ℝ))
    (hscheduledFloor : ∀ P : PairOn V, ∀ i, i ≤ fuel →
      PairAlive P.1
          (absorberGreedyInitialState
            (absorberErdosForbiddenConfigurationsOn q B)
            (outerOnlyAvailable U A)) →
        (d i : ℝ) ≤
          sharpScheduledPairLowerTarget
              (absorberGreedyInitialState
                (absorberErdosForbiddenConfigurationsOn q B)
                (outerOnlyAvailable U A)) D u Kinc P i - aPair)
    (hDschedule : ∀ i, i ≤ fuel →
      D i ≤ (Nat.choose (Fintype.card V) 2 - 3 * i -
          (graphEdges (internalOuterGraph G U)ᶜ).card) *
            d i / 3)
    (hMschedule : ∀ i, i ≤ fuel →
      ((Nat.choose (Fintype.card V) 2 - 3 * i -
          (graphEdges (internalOuterGraph G U)ᶜ).card) * u i) / 3 ≤ Mschedule i)
    (hdone : ∀ i, i < fuel → 1 ≤ d i)
    (hsmall : ∀ i, i < fuel → 3 + Kpair < d i)
    (hupperJump : ∀ i, i < fuel →
      sharpScheduledPairUpperRate (Mschedule i) (d i) (u i) ≤ JUpper)
    (hlowerDeath : ∀ i, i < fuel →
      sharpScheduledPairLowerRate (D i) (u i) Kinc ≤ d i)
    (hvarianceUpper : ∀ i, i < fuel →
      sharpScheduledPairUpperVariance (D i) (u i) Kpair Kglobal
        (sharpScheduledPairUpperRate (Mschedule i) (d i) (u i)) ≤ vPair)
    (hvarianceLower : ∀ i, i < fuel →
      sharpScheduledPairLowerVariance (D i) (u i) Kpair Kinc
        (sharpScheduledPairLowerRate (D i) (u i) Kinc) ≤ vPair)
    (htheta : 0 < thetaPair)
    (hthetaUpper : thetaPair * (JUpper : ℝ) ≤ 1)
    (hthetaLower : thetaPair * ((3 + Kpair : ℕ) : ℝ) ≤ 1)
    (hv : 0 ≤ vPair)
    (hscale : 1 ≤ scale)
    (hscaleRate : rate ≤ scale * (Fintype.card V + 1 : ℝ≥0)⁻¹)
    (hratio : (fuel : ℝ≥0) * (Dcut : ℝ≥0)⁻¹ ≤ rate)
    (hdM : ∀ i, i < fuel → d i ≤ Mschedule i)
    (heffective : ∀ i, i < fuel → d i - 3 * K < Mschedule i)
    (heffectiveInc : ∀ i, i < fuel → d i - 3 * rInc < Mschedule i)
    (hrIncR : rInc ≤ Rinc)
    (hsurvival : cumulativeSurvival
      (boundedSharpSurvivalSchedule fuel Mschedule d (3 * K)) fuel ≤ C * p)
    (hpoint : transferPointWeight
      (boundedSharpSurvivalSchedule fuel Mschedule d (3 * K))
      (boundedSharpTransferSchedule fuel D Mschedule d (3 * K)) fuel ≤
        C * (Fintype.card V : ℝ≥0)⁻¹)
    (hCp : 1 ≤ C * p) (hC : 1 ≤ C)
    (hlarge : ∀ (Q : TripleSystemOn V) (E : Finset (Sym2 V)),
      K < Q.card + E.card →
      1 ≤ C ^ (Q.card + E.card) *
        (p ^ E.card *
          (Fintype.card V : ℝ≥0)⁻¹ ^ Q.card +
            sharpScheduledAbsorberPhaseFailure q M fuel sPair sGlobal sInc
              Kpair Kglobal Kinc I Habs X B scale thetaPair aPair vPair)) :
    let F := absorberErdosForbiddenConfigurationsOn q B
    let S₀ := absorberGreedyInitialState F (outerOnlyAvailable U A)
    let active := timedSharpScheduledAggregatePairBandActive F Kpair Kglobal
      Kinc Delta delta I Dcut D d Mschedule u
    let L := FiniteLaw.timedStoppedProcessLaw fuel
      (fun _ ↦ greedyKernel F) active S₀
    IsInitialProductBound L (fun z ↦ z.2.chosen) p C
        (sharpScheduledAbsorberPhaseFailure q M fuel sPair sGlobal sInc
          Kpair Kglobal Kinc I Habs X B scale thetaPair aPair vPair) ∧
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
          (sharpScheduledAbsorberPhaseFailure q M fuel sPair sGlobal sInc
            Kpair Kglobal Kinc I Habs X B scale thetaPair aPair vPair)
          rInc Rinc := by
  dsimp only
  let F := absorberErdosForbiddenConfigurationsOn q B
  let Aout := outerOnlyAvailable U A
  let S₀ := absorberGreedyInitialState F Aout
  let active := timedSharpScheduledAggregatePairBandActive F Kpair Kglobal
    Kinc Delta delta I Dcut D d Mschedule u
  let L := FiniteLaw.timedStoppedProcessLaw fuel
    (fun _ ↦ greedyKernel F) active S₀
  have hInv₀ : AbsorberGreedyInvariant F Aout S₀ := by
    exact absorberGreedyInitialState_invariant F Aout
      (fun _C hC ↦ absorberErdosForbidden_nonempty hC)
  have hchosen₀ : S₀.chosen = ∅ := by
    simp [S₀, absorberGreedyInitialState]
  have hinactive : L.probability (fun z ↦ ¬ active z.1.1 z.2) ≤
      sharpScheduledAbsorberPhaseFailure q M fuel sPair sGlobal sInc
        Kpair Kglobal Kinc I Habs X B scale thetaPair aPair vPair := by
    simpa only [L, active, F, Aout, S₀] using
      probability_timedSharpScheduledAbsorber_not_active_le
        (F := F) (H := Habs) (G := G)
        (X := X) (U := U) (B := B) (A := A) (S₀ := S₀)
        D d Mschedule u thetaPair aPair vPair rate scale rfl rfl hA2 hInv₀
        htri
        (by simpa only [S₀, Aout] using houtside₀) hchosen₀ hsmallBase
        hDcutPos hDpos hDgap hDcut
        (by simpa only [S₀, Aout] using hbaseCap)
        (by simpa only [S₀, Aout] using hbaseFloor)
        (by simpa only [S₀, Aout] using hscheduledCap)
        (by simpa only [S₀, Aout] using hscheduledFloor)
        hDschedule hMschedule hdone hsmall hupperJump hlowerDeath
        hvarianceUpper hvarianceLower htheta hthetaUpper hthetaLower hv
        hscale hscaleRate hratio
  have hproduct :=
    timedSharpScheduledOuterOnly_initialProductLaw fuel F G U A S₀
      Kpair Kglobal Kinc Delta delta I Dcut K D d Mschedule u p C
      (sharpScheduledAbsorberPhaseFailure q M fuel sPair sGlobal sInc
        Kpair Kglobal Kinc I Habs X B scale thetaPair aPair vPair)
      hInv₀ (by simpa only [S₀, Aout] using houtside₀) hchosen₀
      hsmallBase hactive₀ (fun i hi ↦ hDpos i (Nat.le_of_lt hi)) hdM
      heffective hinactive hsurvival hpoint hCp hC hlarge
  have hincidence :=
    timedSharpScheduledOuterOnly_probability_not_internalIncidenceGood_le_moment
      fuel F G U A S₀ Kpair Kglobal Kinc Delta delta I Dcut rInc Rinc
      D d Mschedule u
      (sharpScheduledAbsorberPhaseFailure q M fuel sPair sGlobal sInc
        Kpair Kglobal Kinc I Habs X B scale thetaPair aPair vPair)
      hrIncR hInv₀ (by simpa only [S₀, Aout] using houtside₀) hchosen₀
      hsmallBase hactive₀ (fun i hi ↦ hDpos i (Nat.le_of_lt hi)) hdM
      heffectiveInc hinactive
  exact ⟨by simpa only [L, active, F, Aout, S₀] using hproduct.1,
    by simpa only [L, active, F, Aout, S₀] using hproduct.2,
    by simpa only [L, active, F, Aout, S₀] using hincidence⟩

end

end Erdos207
