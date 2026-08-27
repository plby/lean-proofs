/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.FineOuterCertifiedInitialProductLaw
import ErdosProblems.Erdos207.OuterOnlyVertexStarTerminal

/-!
# Residual-degree tail from a certified fine outer corridor

The same deterministic certificate used by the initial product law also
discharges every hypothesis of the sharp inactive-probability theorem.  This
module combines that failure bound with the vertex-star martingale tail.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem fineOuterCertified_residualDegreeTail
    {V : Type*} [Fintype V] [DecidableEq V]
    {q Mloc fuel sPair sGlobal sInc Kpair Kglobal Kinc Delta delta I Dcut
      K R starCap Umax dmin reserve : ℕ}
    {Habs G : SimpleGraph V} {X U : Finset V}
    {B A : TripleSystemOn V}
    (upper₀ lower₀ : ℕ) (buffer thetaPair thetaStar aStar : ℝ)
    (rate scale : ℝ≥0)
    (hA2 : HasAbsorberLocalization q Mloc Habs X B)
    (htri : ConsistsOfTriangles G A)
    (houtside₀ : OutsideLeavePairsAlive
      (internalOuterGraph G U)ᶜ U
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
    (hgap : Umax < Dcut) (hDcutPos : 0 < Dcut)
    (hUmaxDelta : Umax ≤ Delta) (hdeltaMin : delta ≤ dmin)
    (hsmallBase : 3 + Kpair < delta)
    (hthetaPair : 0 < thetaPair)
    (hthetaUpper : thetaPair * (fineOuterUpperJump Umax : ℝ) ≤ 1)
    (hthetaLower : thetaPair * ((3 + Kpair : ℕ) : ℝ) ≤ 1)
    (hfailureScale : 1 ≤ scale)
    (hfailureRate : rate ≤ scale * (Fintype.card V + 1 : ℝ≥0)⁻¹)
    (hfailureRatio : (fuel : ℝ≥0) * (Dcut : ℝ≥0)⁻¹ ≤ rate)
    (hRpos : 0 < R)
    (hrateOne : ∀ i, i < fuel →
      R * outerSharpLowerSchedule (internalOuterGraph G U)ᶜ U
          (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i ≤
        2 * outerSharpUpperAvailability (internalOuterGraph G U)ᶜ U
          (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i)
    (hstarCap : (univ \ U).card - 1 ≤ R + 2 * starCap)
    (hcumulative : aStar + starCap ≤ cumulativeGreedyRate
      (outerOnlyVertexSelectionRate R
        (outerSharpLowerSchedule (internalOuterGraph G U)ᶜ U
          (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc)
        (outerSharpUpperAvailability (internalOuterGraph G U)ᶜ U
          (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc)) fuel)
    (hthetaStar : 0 < thetaStar) (hthetaStarOne : thetaStar ≤ 1) :
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
    ((L.probability (fun z ↦ ∃ v : V,
      R ≤ (scheduledEdgesAt
        (preliminaryResidualInternalEdges G U z.2.chosen) v).card) : ℝ)) ≤
      (sharpScheduledAbsorberPhaseFailure q Mloc fuel sPair sGlobal sInc
        Kpair Kglobal Kinc I Habs X B scale thetaPair buffer
          (fineOuterVarianceBound Dcut Umax Kpair Kglobal Kinc
            (fineOuterUpperRateBound reserve Umax)
            (fineOuterLowerRateBound Dcut Umax Kinc)) : ℝ) +
      (Fintype.card V : ℝ) *
        Real.exp (-thetaStar * aStar + thetaStar ^ 2 * (fuel : ℝ)) := by
  dsimp only
  let F := absorberErdosForbiddenConfigurationsOn q B
  let S₀ := absorberGreedyInitialState F (outerOnlyAvailable U A)
  let Hout := (internalOuterGraph G U)ᶜ
  let D := outerSharpLowerAvailability Hout U
    (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc
  let d := outerSharpLowerSchedule Hout U
    (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc
  let Mschedule := outerSharpUpperAvailability Hout U
    (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc
  let u := outerSharpUpperSchedule Hout U
    (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc
  let active := timedSharpScheduledAggregatePairBandActive F Kpair Kglobal
    Kinc Delta delta I Dcut D d Mschedule u
  let failure := sharpScheduledAbsorberPhaseFailure q Mloc fuel sPair
    sGlobal sInc Kpair Kglobal Kinc I Habs X B scale thetaPair buffer
      (fineOuterVarianceBound Dcut Umax Kpair Kglobal Kinc
        (fineOuterUpperRateBound reserve Umax)
        (fineOuterLowerRateBound Dcut Umax Kinc))
  have hAbs₀ : AbsorberGreedyInvariant F (outerOnlyAvailable U A) S₀ := by
    exact absorberGreedyInitialState_invariant F (outerOnlyAvailable U A)
      (fun _C hC ↦ absorberErdosForbidden_nonempty hC)
  have hchosen₀ : S₀.chosen = ∅ := by
    simp [S₀, absorberGreedyInitialState]
  have htargets := outerSharpRecursive_target_bounds
    (F := F) (S₀ := S₀) Hout U upper₀ lower₀ buffer Kinc fuel
      Delta delta hcap₀ hfloor₀
      (fun i hi ↦ (hbounds i hi).2.2.2)
      (fun i hi ↦ (hbounds i hi).2.1.trans hUmaxDelta)
      (fun i hi ↦ hdeltaMin.trans (hbounds i hi).1)
  have hDpos : ∀ i, i ≤ fuel → 0 < D i := by
    intro i hi
    exact hDcutPos.trans_le (by
      simpa only [D, Hout] using (hbounds i hi).2.2.1)
  have hDgap : ∀ i, i < fuel → u i < D i := by
    intro i hi
    have huBound : u i ≤ Umax := by
      simpa only [u, Hout] using (hbounds i hi.le).2.1
    have hDBound : Dcut ≤ D i := by
      simpa only [D, Hout] using (hbounds i hi.le).2.2.1
    exact huBound.trans_lt (hgap.trans_le hDBound)
  have hsmall : ∀ i, i < fuel → 3 + Kpair < d i := by
    intro i hi
    exact hsmallBase.trans_le (hdeltaMin.trans (by
      simpa only [d, Hout] using (hbounds i hi.le).1))
  have hdone : ∀ i, i < fuel → 1 ≤ d i := by
    intro i hi
    have hs := hsmall i hi
    omega
  have hinactiveNN :
      (FiniteLaw.timedStoppedProcessLaw fuel
        (fun _ ↦ greedyKernel F) active S₀).probability
          (fun z ↦ ¬ active z.1.1 z.2) ≤ failure := by
    simpa only [F, S₀, Hout, D, d, Mschedule, u, active, failure] using
      probability_timedSharpScheduledAbsorber_not_active_le
        (q := q) (M := Mloc) (n := fuel) (sPair := sPair)
        (sGlobal := sGlobal) (sInc := sInc) (Kpair := Kpair)
        (Kglobal := Kglobal) (Kinc := Kinc) (Delta := Delta)
        (delta := delta) (I := I) (Dcut := Dcut)
        (JUpper := fineOuterUpperJump Umax)
        (F := F) (H := Habs) (G := G) (X := X) (U := U)
        (B := B) (A := A) (S₀ := S₀)
        D d Mschedule u thetaPair buffer
        (fineOuterVarianceBound Dcut Umax Kpair Kglobal Kinc
          (fineOuterUpperRateBound reserve Umax)
          (fineOuterLowerRateBound Dcut Umax Kinc))
        rate scale rfl rfl hA2 hAbs₀ htri
        (by simpa only [S₀, F] using houtside₀) hchosen₀ hsmallBase
        hDcutPos hDpos hDgap
        (fun i hi ↦ by simpa only [D, Hout] using (hbounds i hi).2.2.1)
        htargets.1 htargets.2.1 htargets.2.2.1 htargets.2.2.2
        (fun _i _hi ↦ le_rfl) (fun _i _hi ↦ le_rfl)
        hdone hsmall hprocess.upper_jump hprocess.lower_death
        hprocess.variance_upper hprocess.variance_lower hthetaPair
        hthetaUpper hthetaLower
        (by unfold fineOuterVarianceBound; positivity)
        hfailureScale hfailureRate hfailureRatio
  have hinactive :
      (((FiniteLaw.timedStoppedProcessLaw fuel
        (fun _ ↦ greedyKernel F) active S₀).probability
          (fun z ↦ ¬ active z.1.1 z.2) : ℝ)) ≤ (failure : ℝ) := by
    exact_mod_cast hinactiveNN
  apply probability_timedStoppedGreedy_exists_residualDegree_ge_le
    fuel F G U A active S₀ Kpair R starCap d Mschedule thetaStar aStar
      (failure : ℝ) hAbs₀ (by simpa only [S₀, F] using houtside₀) htri
      hchosen₀ hRpos
  · intro _i _hi _S _hAbs _hout hactive
    exact hactive.1.1.1.1.1.1
  · intro _i _hi _S _hAbs _hout hactive
    exact hactive.1.1.1.1.1.2.2.1
  · intro _i _hi _S _hAbs _hout hactive
    exact hactive.1.1.2.2
  · intro i hi
    simpa only [Mschedule, Hout] using hprocess.upper_availability_pos i hi
  · intro _i _hi _S _hAbs _hout hactive
    exact hactive.1.2
  · exact hsmall
  · intro i hi
    simpa only [d, Mschedule, Hout] using hrateOne i hi
  · exact hstarCap
  · simpa only [d, Mschedule, Hout] using hcumulative
  · exact hthetaStar
  · exact hthetaStarOne
  · exact hinactive

end

end Erdos207
