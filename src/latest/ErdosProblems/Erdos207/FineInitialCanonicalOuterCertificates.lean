/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.FineOuterCanonicalCertificates
import ErdosProblems.Erdos207.FineInitialOuterCorridorStart
import ErdosProblems.Erdos207.FineOffsetOuterQuadraticBarrier

/-!
# Canonical outer certificates from the packaged initial vortex

This file connects the deterministic canonical-corridor interface to the
fine initial power-vortex package.  All graph-valued hypotheses are discharged
here; the eventual hierarchy is left only with explicit arithmetic bounds.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem FineInitialPowerVortexPackage.canonicalOuterCertificates
    {q h n ell t T rootPower step : ℕ}
    (P : FineInitialPowerVortexPackage q h n ell t rootPower step)
    (hell : 0 < ell) (hT : 3 ≤ T)
    {Kinc K Kpair Kglobal : ℕ}
    (hlevelSmall :
      2 * (P.W.U ((⟨0, hell⟩ : Fin ell).succ)).card + 8 ≤ n)
    (hsmall : ((fineOuterCorridorError T : ℝ≥0) : ℝ) ≤ 1 / 100)
    (habsorberFits :
      (highGirthAbsorberCardCoefficient (q + 2) *
          (2 * t ^ rootPower) ^ 156) ^ 2 ≤
        Nat.choose
          (univ \ P.W.U ((⟨0, hell⟩ : Fin ell).succ)).card 2)
    (hdefect :
      let outside :=
        (univ \ P.W.U ((⟨0, hell⟩ : Fin ell).succ)).card
      let absorberBound := highGirthAbsorberCardCoefficient (q + 2) *
        (2 * t ^ rootPower) ^ 156
      ((outside + 2 * absorberBound ^ 2 : ℕ) : ℝ) ≤
        3 * (fineOuterCorridorError T : ℝ≥0) * outside ^ 2)
    (hlower₀ :
      let outside :=
        (univ \ P.W.U ((⟨0, hell⟩ : Fin ell).succ)).card
      let lower₀ := outside - 2 * (n / t ^ fineInitialExponent) - 4 + 1
      (1 - 16 * (fineOuterCorridorError T : ℝ≥0)) * outside ≤
        (lower₀ : ℝ))
    (hsmallPower : 12800 ≤ T ^ 31)
    (hoffsetPower :
      let outside :=
        (univ \ P.W.U ((⟨0, hell⟩ : Fin ell).succ)).card
      T ^ fineOuterCorridorExponent ≤ 16 * outside)
    (hclockPower :
      let outside :=
        (univ \ P.W.U ((⟨0, hell⟩ : Fin ell).succ)).card
      50 * T ^ 101 ≤ outside ^ 2)
    (haggregatePower :
      let outside :=
        (univ \ P.W.U ((⟨0, hell⟩ : Fin ell).succ)).card
      T ^ 102 * Kinc ≤ 8 * outside ^ 2)
    (hreserveFour :
      let outside :=
        (univ \ P.W.U ((⟨0, hell⟩ : Fin ell).succ)).card
      4 ≤ fineOuterReserve outside T)
    (hdegreePos :
      let outside :=
        (univ \ P.W.U ((⟨0, hell⟩ : Fin ell).succ)).card
      0 < fineOuterCoarseDegreeFloor outside T)
    (hgap :
      let outside :=
        (univ \ P.W.U ((⟨0, hell⟩ : Fin ell).succ)).card
      5 * outside < fineOuterCoarseAvailabilityFloor outside T)
    (hupper :
      let outside :=
        (univ \ P.W.U ((⟨0, hell⟩ : Fin ell).succ)).card
      12 * (5 * outside) ≤ fineOuterReserve outside T)
    (hlower :
      let outside :=
        (univ \ P.W.U ((⟨0, hell⟩ : Fin ell).succ)).card
      2 * (5 * outside) ^ 2 + Kinc ≤
        fineOuterCoarseDegreeFloor outside T *
          (fineOuterCoarseAvailabilityFloor outside T - 5 * outside))
    (hpairScalar :
      let i : Fin ell := ⟨0, hell⟩
      let U := P.W.U i.succ
      let G := graphDifference (SimpleGraph.completeGraph (Fin n)) P.H
      let Hout := (internalOuterGraph G U)ᶜ
      let outside := (univ \ U).card
      ((outerSharpEligiblePairs Hout U 0 : ℕ) : ℝ≥0) ^ 2 ≤
        (64 * T ^ 2 : ℕ) * (n : ℝ≥0) ^ 3 *
          fineOuterCoarseDegreeFloor outside T)
    (hquadratic :
      let i : Fin ell := ⟨0, hell⟩
      let U := P.W.U i.succ
      let G := graphDifference (SimpleGraph.completeGraph (Fin n)) P.H
      let Hout := (internalOuterGraph G U)ᶜ
      (n : ℝ≥0) ^ 2 ≤
        20 * (outerSharpEligiblePairs Hout U 0 : ℕ)) :
    let i : Fin ell := ⟨0, hell⟩
    let U := P.W.U i.succ
    let G := graphDifference (SimpleGraph.completeGraph (Fin n)) P.H
    let Hout := (internalOuterGraph G U)ᶜ
    let outside := (univ \ U).card
    let lower₀ := outside - 2 * (n / t ^ fineInitialExponent) - 4 + 1
    FineOuterCanonicalCertificates Hout U lower₀ outside T
      Kinc K Kpair Kglobal := by
  dsimp only
  let i : Fin ell := ⟨0, hell⟩
  let U := P.W.U i.succ
  let G := graphDifference (SimpleGraph.completeGraph (Fin n)) P.H
  let Hout := (internalOuterGraph G U)ᶜ
  let outside := (univ \ U).card
  let lower₀ := outside - 2 * (n / t ^ fineInitialExponent) - 4 + 1
  have houtside : 0 < outside := by
    have hUcard : U.card ≤ n := by
      simpa only [Fintype.card_fin] using Finset.card_le_univ U
    have houtsideCard : outside = n - U.card := by
      simp [outside, card_sdiff]
    rw [houtsideCard]
    have hsmallU : 2 * U.card + 8 ≤ n := by
      simpa only [U, i] using hlevelSmall
    omega
  have hpairs := P.initialOuter_eligiblePair_bounds (T := T) hell habsorberFits hdefect
  have hreserveInitial : fineOuterReserve outside T ≤
      outerSharpEligiblePairs Hout U 0 := by
    apply fineOuterReserve_le_initialEligible Hout U outside T hT hsmall
    simpa only [Hout, U, G, outside, i] using hpairs.1
  have hinitial := P.initialOuter_offset_barrier_bounds (T := T) hell houtside hsmall
    habsorberFits hdefect hlower₀
  have hinput : FineOuterCanonicalInput Hout U lower₀ outside T Kinc := by
    refine ⟨houtside, (by omega), hreserveInitial, ?_, hsmallPower,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [Hout, U, G, outside, i] using hpairs.2
    · simpa only [outside, U, i] using hoffsetPower
    · simpa only [outside, U, i] using hclockPower
    · simpa only [outside, U, i] using haggregatePower
    · dsimp only [lower₀]
      omega
    · simpa only [Hout, U, G, outside, lower₀, i] using hinitial
    · simpa only [outside, U, i] using hreserveFour
    · simpa only [outside, U, i] using hdegreePos
  apply fineOuterCanonicalCertificates Hout U lower₀ outside T
    Kinc K Kpair Kglobal hinput
  · simpa only [outside, U, i] using hgap
  · simpa only [outside, U, i] using hupper
  · simpa only [outside, U, i] using hlower
  · simpa only [Hout, U, G, outside, i, Fintype.card_fin] using hpairScalar
  · simpa only [Hout, U, G, i, Fintype.card_fin] using hquadratic

end

end Erdos207
