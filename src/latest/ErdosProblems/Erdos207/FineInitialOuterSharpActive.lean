/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.FineInitialPowerOuterOnlyBounds
import ErdosProblems.Erdos207.OuterOnlyRecursiveSharpSchedule

/-!
# The packaged fine vortex starts the sharp outer process

This file removes the remaining structural hypotheses from the time-zero
sharp-process certificate.  The fine initial typicality supplies the pair
floor, while the inherited coarse typicality supplies outside-pair survival.
-/

namespace Erdos207

open Finset
open scoped Classical NNReal

noncomputable section

theorem FineInitialPowerVortexPackage.initialOuterSharpActive
    {q h n ell t rootPower step E : ℕ}
    (P : FineInitialPowerVortexPackage q h n ell t rootPower step)
    (hell : 0 < ell) (hh : 2 ≤ h) (ht : 12 ≤ t) (hq : 4 ≤ q)
    (hexponent : max rootPower (step * (ell - 1)) + 1 ≤ E)
    (hpower : t ^ E ≤ n)
    {Kpair Kglobal Kinc Delta delta I Dcut : ℕ}
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
    (buffer : ℝ) (hbuffer : 0 ≤ buffer)
    (hDcutPos : 0 < Dcut)
    (hDcut : Dcut ≤
      let i : Fin ell := ⟨0, hell⟩
      let U := P.W.U i.succ
      let G := graphDifference (SimpleGraph.completeGraph (Fin n)) P.H
      let Hout := (internalOuterGraph G U)ᶜ
      let outer := (univ \ U).card
      let lower₀ : ℕ :=
        outer - 2 * (n / t ^ fineInitialExponent) - 4 + 1
      outerSharpLowerAvailability Hout U
        (outer : ℝ) (lower₀ : ℝ) buffer Kinc 0) :
    let F := absorberErdosForbiddenConfigurationsOn q P.B
    let i : Fin ell := ⟨0, hell⟩
    let U := P.W.U i.succ
    let G := graphDifference (SimpleGraph.completeGraph (Fin n)) P.H
    let A := (absorberGreedyInitialState F
      (outsideAvailableTriangles P.H P.B)).available
    let Hout := (internalOuterGraph G U)ᶜ
    let outer := (univ \ U).card
    let lower₀ : ℕ :=
      outer - 2 * (n / t ^ fineInitialExponent) - 4 + 1
    timedSharpScheduledAggregatePairBandActive F
      Kpair Kglobal Kinc Delta delta I Dcut
      (outerSharpLowerAvailability Hout U
        (outer : ℝ) (lower₀ : ℝ) buffer Kinc)
      (outerSharpLowerSchedule Hout U
        (outer : ℝ) (lower₀ : ℝ) buffer Kinc)
      (outerSharpUpperAvailability Hout U
        (outer : ℝ) (lower₀ : ℝ) buffer Kinc)
      (outerSharpUpperSchedule Hout U
        (outer : ℝ) (lower₀ : ℝ) buffer Kinc) 0
      (absorberGreedyInitialState F (outerOnlyAvailable U A)) := by
  dsimp only
  let F := absorberErdosForbiddenConfigurationsOn q P.B
  let i : Fin ell := ⟨0, hell⟩
  let U := P.W.U i.succ
  let G := graphDifference (SimpleGraph.completeGraph (Fin n)) P.H
  let A := (absorberGreedyInitialState F
    (outsideAvailableTriangles P.H P.B)).available
  let outer := (univ \ U).card
  let m := outer - 2 * (n / t ^ fineInitialExponent) - 4
  have hlevelSmall : 2 * U.card + 8 ≤ n := by
    simpa only [U, i] using
      P.firstLevel_twice_add_eight_le hell ht hexponent hpower
  have hcoarseGap : (((U.card + 2 : ℕ) : ℝ≥0) <
      (1 - (t : ℝ≥0)⁻¹) *
        ((1 : ℝ≥0) ^ 2 * 1 * (P.W.U i.castSucc).card)) := by
    have hfull := P.initialOuterOnlyNearFullGap hell
      ((by norm_num : 8 ≤ 12).trans ht) hlevelSmall
    have hleft : U.card + 2 ≤ U.card + 2 +
        (outer - 2 * (n / t) - 4) := Nat.le_add_right _ _
    have hleftNN : ((U.card + 2 : ℕ) : ℝ≥0) ≤
        ((U.card + 2 + (outer - 2 * (n / t) - 4) : ℕ) : ℝ≥0) := by
      exact_mod_cast hleft
    exact hleftNN.trans_lt (by
      simpa only [U, i, outer] using hfull)
  have hready := P.initialOuterOnlyReady hell hh (by
    simpa only [U, i] using hcoarseGap)
  have hfloor := P.initialOuterOnlyFineNearFullPairFloor hell hh
    ((by norm_num : 2 ≤ 12).trans ht) hlevelSmall
  have hpoint : IsMasterStagePointwiseGood P.W 0 F G A
      ∅ ∅ 1 1 (fineInitialError t) h := by
    simpa only [F, G, A] using
      initialMasterStagePointwiseGood_of_typical P.typicalFine
  have htri : ConsistsOfTriangles G A := hpoint.2.2.2.2.2.1
  apply timedSharpScheduledAggregatePairBandActive_outerSharp_initial
    (q := q) (Mloc := 12 * (q + 2) ^ 2) (m := m)
    (Habs := P.H) (G := G) (X := P.X) (U := U) (B := P.B) (A := A)
    hq P.localization htri
    (by simpa only [F, G, A, U, i] using hready.2.1)
    (by simpa only [F, A, U, i, outer, m] using hfloor)
    hKpair hKglobal (by simpa only [Fintype.card_fin] using hKinc)
    (by simpa only [U, i] using hOuterDelta)
    (by simpa only [U, i, outer, m] using hdelta)
    (by simpa using hI) buffer hbuffer hDcutPos
  simpa only [G, U, i, outer, m] using hDcut

end

end Erdos207
