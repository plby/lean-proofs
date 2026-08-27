/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.FineInitialCanonicalOuterCertificates
import ErdosProblems.Erdos207.FineOuterCertifiedInitialProductLaw
import ErdosProblems.Erdos207.FineInitialOuterSharpActive

/-!
# The canonical initial product law of a fine power vortex

The deterministic certificate and the packaged time-zero state discharge
all graph-valued assumptions of the long outer random-greedy theorem.  Only
coefficient cutoffs and explicit scalar inequalities remain.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem FineInitialPowerVortexPackage.canonicalOuterInitialProductLaw
    {q h n ell t T rootPower step E : ℕ}
    (P : FineInitialPowerVortexPackage q h n ell t rootPower step)
    (hell : 0 < ell) (hh : 2 ≤ h) (ht : 12 ≤ t) (hq : 4 ≤ q)
    (hexponent : max rootPower (step * (ell - 1)) + 1 ≤ E)
    (hpower : t ^ E ≤ n)
    {sPair sGlobal sInc Kpair Kglobal Kinc Delta delta I K rInc Rinc : ℕ}
    (hKpair : pairTwoAwayThreatExtensionCoefficient q P.B ≤ Kpair)
    (hKglobal : twoAwayThreatExtensionCoefficient q
      (12 * (q + 2) ^ 2) P.H P.X P.B ≤ Kglobal)
    (hKinc : initialAggregatePairTwoAwayCoefficient q P.B * n ≤ Kinc)
    (hOuterDelta :
      (univ \ P.W.U ((⟨0, hell⟩ : Fin ell).succ)).card ≤ Delta)
    (hdelta : delta ≤
      (univ \ P.W.U ((⟨0, hell⟩ : Fin ell).succ)).card -
          2 * (n / t ^ fineInitialExponent) - 4 + 1)
    (hI : Fintype.card (TripleOn (Fin n)) *
      twoAwayThreatExtensionCoefficient q (12 * (q + 2) ^ 2)
        P.H P.X P.B ≤ I)
    (hcert :
      let i : Fin ell := ⟨0, hell⟩
      let U := P.W.U i.succ
      let G := graphDifference (SimpleGraph.completeGraph (Fin n)) P.H
      let Hout := (internalOuterGraph G U)ᶜ
      let outside := (univ \ U).card
      let lower₀ := outside - 2 * (n / t ^ fineInitialExponent) - 4 + 1
      FineOuterCanonicalCertificates Hout U lower₀ outside T
        Kinc K Kpair Kglobal)
    (hgap :
      let i : Fin ell := ⟨0, hell⟩
      let outside := (univ \ P.W.U i.succ).card
      5 * outside < fineOuterCoarseAvailabilityFloor outside T)
    (hUmaxDelta :
      let i : Fin ell := ⟨0, hell⟩
      let outside := (univ \ P.W.U i.succ).card
      5 * outside ≤ Delta)
    (hdeltaMin :
      let i : Fin ell := ⟨0, hell⟩
      let outside := (univ \ P.W.U i.succ).card
      delta ≤ fineOuterCoarseDegreeFloor outside T)
    (hsmallBase : 3 + Kpair < delta)
    (hrInc : 0 < rInc)
    (hrIncR : rInc ≤ Rinc)
    (thetaPair : ℝ)
    (htheta : 0 < thetaPair)
    (hthetaUpper : thetaPair ≤ 1)
    (hthetaLower : thetaPair * ((3 + Kpair : ℕ) : ℝ) ≤ 1)
    (rate scale p C : ℝ≥0)
    (hfailureScale : 1 ≤ scale)
    (hfailureRate : rate ≤ scale * (n + 1 : ℝ≥0)⁻¹)
    (hfailureRatio :
      let i : Fin ell := ⟨0, hell⟩
      let U := P.W.U i.succ
      let G := graphDifference (SimpleGraph.completeGraph (Fin n)) P.H
      let Hout := (internalOuterGraph G U)ᶜ
      let outside := (univ \ U).card
      (outerSharpStopFuel Hout U (fineOuterReserve outside T) : ℝ≥0) *
          (fineOuterCoarseAvailabilityFloor outside T : ℝ≥0)⁻¹ ≤ rate)
    (hcard : 0 < n)
    (hfuel :
      let i : Fin ell := ⟨0, hell⟩
      let U := P.W.U i.succ
      let G := graphDifference (SimpleGraph.completeGraph (Fin n)) P.H
      let Hout := (internalOuterGraph G U)ᶜ
      let outside := (univ \ U).card
      outerSharpStopFuel Hout U (fineOuterReserve outside T) ≤ n ^ 2)
    (hpointCoefficient :
      ((2 : ℝ≥0) ^ (3 * K)) *
          ((20 : ℝ≥0) ^ 3 *
            (5 * (T : ℝ≥0) ^ 3 * (64 * T ^ 2 : ℕ))) ≤ C)
    (hCp : 1 ≤ C * p) (hC : 1 ≤ C)
    (hlarge :
      let i : Fin ell := ⟨0, hell⟩
      let U := P.W.U i.succ
      let G := graphDifference (SimpleGraph.completeGraph (Fin n)) P.H
      let Hout := (internalOuterGraph G U)ᶜ
      let outside := (univ \ U).card
      let fuel := outerSharpStopFuel Hout U (fineOuterReserve outside T)
      ∀ (Qsys : TripleSystemOn (Fin n)) (Epairs : Finset (Sym2 (Fin n))),
        K < Qsys.card + Epairs.card →
        1 ≤ C ^ (Qsys.card + Epairs.card) *
          (p ^ Epairs.card * (n : ℝ≥0)⁻¹ ^ Qsys.card +
            sharpScheduledAbsorberPhaseFailure q (12 * (q + 2) ^ 2)
              fuel sPair sGlobal sInc Kpair Kglobal Kinc I P.H P.X P.B
              scale thetaPair (fineOuterBuffer outside T)
              (fineOuterVarianceBound
                (fineOuterCoarseAvailabilityFloor outside T)
                (5 * outside) Kpair Kglobal Kinc
                (fineOuterUpperRateBound (fineOuterReserve outside T)
                  (5 * outside))
                (fineOuterLowerRateBound
                  (fineOuterCoarseAvailabilityFloor outside T)
                  (5 * outside) Kinc)))) :
    let F := absorberErdosForbiddenConfigurationsOn q P.B
    let i : Fin ell := ⟨0, hell⟩
    let U := P.W.U i.succ
    let G := graphDifference (SimpleGraph.completeGraph (Fin n)) P.H
    let A := (absorberGreedyInitialState F
      (outsideAvailableTriangles P.H P.B)).available
    let Hout := (internalOuterGraph G U)ᶜ
    let outside := (univ \ U).card
    let lower₀ := outside - 2 * (n / t ^ fineInitialExponent) - 4 + 1
    let fuel := outerSharpStopFuel Hout U (fineOuterReserve outside T)
    let S₀ := absorberGreedyInitialState F (outerOnlyAvailable U A)
    let active := timedSharpScheduledAggregatePairBandActive F Kpair Kglobal
      Kinc Delta delta I (fineOuterCoarseAvailabilityFloor outside T)
      (outerSharpLowerAvailability Hout U
        (outside : ℝ) (lower₀ : ℝ) (fineOuterBuffer outside T) Kinc)
      (outerSharpLowerSchedule Hout U
        (outside : ℝ) (lower₀ : ℝ) (fineOuterBuffer outside T) Kinc)
      (outerSharpUpperAvailability Hout U
        (outside : ℝ) (lower₀ : ℝ) (fineOuterBuffer outside T) Kinc)
      (outerSharpUpperSchedule Hout U
        (outside : ℝ) (lower₀ : ℝ) (fineOuterBuffer outside T) Kinc)
    let L := FiniteLaw.timedStoppedProcessLaw fuel
      (fun _ ↦ greedyKernel F) active S₀
    IsInitialProductBound L (fun z ↦ z.2.chosen) p C
        (sharpScheduledAbsorberPhaseFailure q (12 * (q + 2) ^ 2)
          fuel sPair sGlobal sInc Kpair Kglobal Kinc I P.H P.X P.B
          scale thetaPair (fineOuterBuffer outside T)
          (fineOuterVarianceBound
            (fineOuterCoarseAvailabilityFloor outside T)
            (5 * outside) Kpair Kglobal Kinc
            (fineOuterUpperRateBound (fineOuterReserve outside T)
              (5 * outside))
            (fineOuterLowerRateBound
              (fineOuterCoarseAvailabilityFloor outside T)
              (5 * outside) Kinc))) ∧
      L.SupportedOn (fun z ↦
        z.2.chosen ⊆ A ∧ IsPackingOn z.2.chosen ∧
          AvoidsForbidden z.2.chosen F ∧
          TrianglesDisjointFrom U z.2.chosen) ∧
      L.probability (fun z ↦ ¬ ∀ v : Fin n,
        (scheduledEdgesAt
          (preliminaryResidualInternalEdges G U z.2.chosen) v).card <
            Rinc) ≤
        trackedResidualOuterFactorialTail (Fin n) (internalOuterGraph G U) U
          (cumulativeSurvival
            (boundedSharpSurvivalSchedule fuel
              (outerSharpUpperAvailability Hout U
                (outside : ℝ) (lower₀ : ℝ) (fineOuterBuffer outside T) Kinc)
              (outerSharpLowerSchedule Hout U
                (outside : ℝ) (lower₀ : ℝ) (fineOuterBuffer outside T) Kinc)
              (3 * rInc)) fuel)
          (sharpScheduledAbsorberPhaseFailure q (12 * (q + 2) ^ 2)
            fuel sPair sGlobal sInc Kpair Kglobal Kinc I P.H P.X P.B
            scale thetaPair (fineOuterBuffer outside T)
            (fineOuterVarianceBound
              (fineOuterCoarseAvailabilityFloor outside T)
              (5 * outside) Kpair Kglobal Kinc
              (fineOuterUpperRateBound (fineOuterReserve outside T)
                (5 * outside))
              (fineOuterLowerRateBound
                (fineOuterCoarseAvailabilityFloor outside T)
                (5 * outside) Kinc)))
          rInc Rinc := by
  dsimp only
  let F := absorberErdosForbiddenConfigurationsOn q P.B
  let i : Fin ell := ⟨0, hell⟩
  let U := P.W.U i.succ
  let G := graphDifference (SimpleGraph.completeGraph (Fin n)) P.H
  let A := (absorberGreedyInitialState F
    (outsideAvailableTriangles P.H P.B)).available
  let Hout := (internalOuterGraph G U)ᶜ
  let outside := (univ \ U).card
  let lower₀ := outside - 2 * (n / t ^ fineInitialExponent) - 4 + 1
  let fuel := outerSharpStopFuel Hout U (fineOuterReserve outside T)
  have hlevelSmall : 2 * U.card + 8 ≤ n := by
    simpa only [U, i] using
      P.toInitialPowerVortexPackage.firstLevel_twice_add_eight_le
        hell ht hexponent hpower
  have hcoarseGap : ((U.card + 2 : ℕ) : ℝ≥0) <
      (1 - (t : ℝ≥0)⁻¹) *
        ((1 : ℝ≥0) ^ 2 * 1 * (P.W.U i.castSucc).card) := by
    have hfull := P.toInitialPowerVortexPackage.initialOuterOnlyNearFullGap
      hell (by omega) hlevelSmall
    have hleft : U.card + 2 ≤ U.card + 2 +
        (outside - 2 * (n / t) - 4) := Nat.le_add_right _ _
    have hleftNN : ((U.card + 2 : ℕ) : ℝ≥0) ≤
        ((U.card + 2 + (outside - 2 * (n / t) - 4) : ℕ) : ℝ≥0) := by
      exact_mod_cast hleft
    exact hleftNN.trans_lt (by
      simpa only [U, i, outside] using hfull)
  have hready := P.toInitialPowerVortexPackage.initialOuterOnlyReady
    hell hh (by simpa only [U, i] using hcoarseGap)
  have hcap := P.toInitialPowerVortexPackage.initialOuterOnlyPairCutoff
    hell hh (by simpa only [U, i] using hcoarseGap)
  have hfloor := P.initialOuterOnlyFineNearFullPairFloor hell hh
    (by omega) hlevelSmall
  have hc := hcert
  dsimp only [i, U, G, Hout, outside, lower₀] at hc
  have hbuffer : 0 ≤ fineOuterBuffer outside T := by
    unfold fineOuterBuffer fineOuterInitialOffset
    positivity
  have hDcutPos : 0 < fineOuterCoarseAvailabilityFloor outside T := by
    have hg := hgap
    dsimp only [i, U, outside] at hg
    exact (Nat.zero_le (5 * outside)).trans_lt hg
  have hactive := P.initialOuterSharpActive
    (E := E) hell hh ht hq hexponent hpower
    (Kpair := Kpair) (Kglobal := Kglobal) (Kinc := Kinc)
    (Delta := Delta) (delta := delta) (I := I)
    (Dcut := fineOuterCoarseAvailabilityFloor outside T)
    hKpair hKglobal hKinc hOuterDelta hdelta hI
    (fineOuterBuffer outside T) hbuffer hDcutPos
    (hc.bounds 0 (Nat.zero_le _)).2.2.1
  have hpoint : IsMasterStagePointwiseGood P.W 0 F G A
      ∅ ∅ 1 1 (fineInitialError t) h := by
    simpa only [F, G, A] using
      initialMasterStagePointwiseGood_of_typical P.typicalFine
  have htri : ConsistsOfTriangles G A := hpoint.2.2.2.2.2.1
  apply fineOuterCertified_absorberInitialProductLaw
    (q := q) (Mloc := 12 * (q + 2) ^ 2) (fuel := fuel)
    (sPair := sPair) (sGlobal := sGlobal) (sInc := sInc)
    (Kpair := Kpair) (Kglobal := Kglobal) (Kinc := Kinc)
    (Delta := Delta) (delta := delta) (I := I)
    (Dcut := fineOuterCoarseAvailabilityFloor outside T)
    (K := K) (rInc := rInc) (Rinc := Rinc) (Umax := 5 * outside)
    (dmin := fineOuterCoarseDegreeFloor outside T)
    (reserve := fineOuterReserve outside T)
    (Habs := P.H) (G := G) (X := P.X) (U := U) (B := P.B) (A := A)
    outside lower₀ (fineOuterBuffer outside T) thetaPair rate scale p C
    (Aenv := (T : ℝ≥0)) (Bscale := (64 * T ^ 2 : ℕ)) (Q := 20)
    P.localization htri
    (by simpa only [F, G, A, U, i] using hready.2.1)
    (by simpa only [F, G, A, Hout, U, outside, lower₀, i] using hactive)
    (by simpa only [F, A, U, outside, i] using hcap)
    (by simpa only [F, A, U, outside, lower₀, i] using hfloor)
    hc.bounds hc.process hc.envelope
    (by simpa only [i, U, outside] using hgap)
    (by
      have hg := hgap
      dsimp only [i, U, outside] at hg
      omega)
    (by simpa only [i, U, outside] using hUmaxDelta)
    (by simpa only [i, U, outside] using hdeltaMin)
    hsmallBase hrInc hrIncR htheta
    (by simpa only [fineOuterUpperJump, Nat.cast_one, mul_one] using hthetaUpper)
    hthetaLower hfailureScale
    (by simpa only [Fintype.card_fin] using hfailureRate)
    (by simpa only [fuel, Hout, U, outside, i] using hfailureRatio)
    (by simpa only [Fintype.card_fin] using hcard)
    (by simpa only [fuel, Hout, U, outside, i, Fintype.card_fin] using hfuel)
    (by simpa only [Fintype.card_fin] using hpointCoefficient)
    hCp hC
  simpa only [fuel, Hout, U, G, outside, i, Fintype.card_fin] using hlarge

end

end Erdos207
