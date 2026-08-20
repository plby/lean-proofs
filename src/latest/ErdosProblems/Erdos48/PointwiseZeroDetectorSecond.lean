/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos48.PointwiseZeroDetector
import ErdosProblems.Erdos48.ZeroDetector

/-!
# Variable-order pointwise zero detector

This module combines Turan's second main theorem with the local zero-count
and logarithmic-derivative estimates.  Unlike the fixed-order detector, the
starting derivative order is a free parameter; this is the form needed when
`eta * log B` is unbounded.
-/

namespace Erdos48

open Complex Metric
open BoundedGaps.Maynard

noncomputable section

/-- A zero within `2 * eta` of `1 + eta + t * I` forces a large derivative
at one of the next `K` orders, where `K` is the number of local zeros. -/
theorem exists_pointwise_zero_detector_second_of_error_budget :
    ∃ Am Al Af Ad : ℕ,
      37 ≤ Am ∧ 37 ≤ Al ∧ 37 ≤ Af ∧ 37 ≤ Ad ∧
      ∀ (q : ℕ) [NeZero q], ∀ (hq : 1 < q),
        ∀ (chi : DirichletCharacter ℂ q), ∀ (hchi : chi.IsPrimitive),
          ∀ (t eta : ℝ), 0 < eta → eta ≤ 1 / 8 →
            ∀ (rho₀ : ℂ),
              DirichletCharacter.LFunction chi rho₀ = 0 →
              dist rho₀ (((1 + eta : ℝ) : ℂ) + t * I) ≤ 2 * eta →
              ∀ (M : ℕ), 1 ≤ M →
                let z : ℂ := ((1 + eta : ℝ) : ℂ) + t * I
                let Z := smallDiskZeroFinsupp hq chi hchi t eta
                let K := Z.support.card
                (∀ j ∈ Finset.Icc (M + 1) (M + K),
                  turanSecondLoss K M * (2 * eta) ^ j *
                    pointwiseZeroDetectorError Al Af Ad q t eta j ≤ 1 / 4) →
                ∃ j ∈ Finset.Icc (M + 1) (M + K),
                  ((j - 1).factorial : ℝ) * (1 / 2 : ℝ) <
                    turanSecondLoss K M * (2 * eta) ^ j *
                      ‖iteratedDeriv (j - 1)
                        (fun w ↦ -logDeriv
                          (DirichletCharacter.LFunction chi) w) z‖ := by
  obtain ⟨Am, hAm, hmass⟩ := exists_smallDiskZeroMultiplicity_bound
  obtain ⟨Al, Af, hAl, hAf, htail⟩ :=
    exists_norm_radiusSix_sub_smallDisk_powerSum_le
  obtain ⟨Ad, hAd, hderiv⟩ := exists_radiusSix_iteratedDeriv_approximation
  refine ⟨Am, Al, Af, Ad, hAm, hAl, hAf, hAd, ?_⟩
  intro q _ hq chi hchi t eta heta0 heta8 rho₀ hzero hrho₀ M hM
  dsimp only
  let z : ℂ := ((1 + eta : ℝ) : ℂ) + t * I
  let Z := smallDiskZeroFinsupp hq chi hchi t eta
  let D := radiusSixZeroFinsupp hq chi hchi t
  let K := Z.support.card
  intro hbudget
  have hrhoRe : rho₀.re < 1 :=
    LFunction_zero_re_lt_one_of_isPrimitive hq chi hchi hzero
  have hzre : z.re = 1 + eta := by simp [z]
  have hzrho₀ : z ≠ rho₀ := by
    intro hzr
    have := congrArg Complex.re hzr
    rw [hzre] at this
    linarith
  have horder : 0 < analyticOrderNatAt
      (DirichletCharacter.LFunction chi) rho₀ :=
    (LFunction_zero_local_logDeriv_expansion
      (character_ne_one_of_isPrimitive hq chi hchi) hzero).1
  have hZrho₀ : Z rho₀ ≠ 0 := by
    dsimp [Z]
    rw [smallDiskZeroFinsupp_apply, smallDiskZeroMultiplicity,
      if_pos (hrho₀.trans (by linarith : 2 * eta ≤ 4 * eta))]
    exact horder.ne'
  have hne : ∀ rho ∈ Z.support, z ≠ rho := by
    intro rho hrho hzrho
    have hZrho : Z rho ≠ 0 := Finsupp.mem_support_iff.mp hrho
    have hm : analyticOrderNatAt
        (DirichletCharacter.LFunction chi) rho ≠ 0 := by
      dsimp [Z] at hZrho
      rw [smallDiskZeroFinsupp_apply, smallDiskZeroMultiplicity] at hZrho
      split at hZrho
      · exact hZrho
      · exact False.elim (hZrho rfl)
    have hzeroRho : DirichletCharacter.LFunction chi rho = 0 :=
      apply_eq_zero_of_analyticOrderNatAt_ne_zero hm
    have hrhoRe : rho.re < 1 :=
      LFunction_zero_re_lt_one_of_isPrimitive hq chi hchi hzeroRho
    have hre := congrArg Complex.re hzrho
    rw [hzre] at hre
    linarith
  obtain ⟨j, hjrange, hjlarge⟩ :=
    exists_weightedReciprocalPowerSum_second Z hZrho₀ hne
      (M := M) (R := 2 * eta) (by positivity) hrho₀
  refine ⟨j, hjrange, ?_⟩
  have hj2 : 2 ≤ j := by
    have := (Finset.mem_Icc.mp hjrange).1
    omega
  let Sz : ℂ := Z.sum
    (fun rho m ↦ (m : ℂ) / (z - rho) ^ j)
  let Sd : ℂ := D.sum
    (fun rho m ↦ (m : ℂ) / (z - rho) ^ j)
  have hlocal : 1 ≤ turanSecondLoss K M * (2 * eta) ^ j * ‖Sz‖ := by
    simpa only [K, Z, Sz, turanSecondLoss] using hjlarge
  have htail' := htail q hq chi hchi t eta heta0 heta8 j hj2
  have htailNorm : ‖Sd - Sz‖ ≤
      64 * (Real.log 4 + 4) / (4 * eta) ^ j +
        ((1024 * (Al : ℝ) / 3) *
          Real.log ((q : ℝ) * (|t| + 2))) / (4 * eta) ^ (j - 1) +
        (2 * (Af : ℝ) * Real.log ((q : ℝ) * (|t| + 2))) /
          (1 / 2 : ℝ) ^ j := by
    simpa only [Sd, Sz, D, Z, z] using htail'
  have hderiv' := hderiv q hq chi hchi t eta heta0
    (by linarith : eta ≤ 1) (j - 1)
  have hjpred : j - 1 + 1 = j := by omega
  have hderivNorm :
      ‖iteratedDeriv (j - 1)
            (fun w ↦ -logDeriv (DirichletCharacter.LFunction chi) w) z -
          (-1 : ℂ) ^ j * (j - 1).factorial * Sd‖ ≤
        (j - 1).factorial *
          (16 * ((Ad : ℝ) *
            Real.log ((q : ℝ) * (|t| + 2))) / 3) := by
    simpa only [hjpred, Sd, D, z] using hderiv'
  have hbudget' := hbudget j hjrange
  have herror :
      turanSecondLoss K M * (2 * eta) ^ j *
        ((64 * (Real.log 4 + 4) / (4 * eta) ^ j +
          ((1024 * (Al : ℝ) / 3) *
            Real.log ((q : ℝ) * (|t| + 2))) / (4 * eta) ^ (j - 1) +
          (2 * (Af : ℝ) *
            Real.log ((q : ℝ) * (|t| + 2))) /
              (1 / 2 : ℝ) ^ j) +
          16 * ((Ad : ℝ) *
            Real.log ((q : ℝ) * (|t| + 2))) / 3) ≤ 1 / 4 := by
    simpa only [pointwiseZeroDetectorError, add_assoc] using hbudget'
  have hSz : ‖Sz‖ ≤ ‖Sd‖ + ‖Sd - Sz‖ := by
    calc
      ‖Sz‖ = ‖Sd - (Sd - Sz)‖ := by ring_nf
      _ ≤ ‖Sd‖ + ‖Sd - Sz‖ := norm_sub_le _ _
  let F : ℂ := iteratedDeriv (j - 1)
    (fun w ↦ -logDeriv (DirichletCharacter.LFunction chi) w) z
  have hscaled : ((j - 1).factorial : ℝ) * ‖Sd‖ ≤
      ‖F‖ + ‖F - (-1 : ℂ) ^ j * (j - 1).factorial * Sd‖ := by
    have htri : ‖(-1 : ℂ) ^ j * (j - 1).factorial * Sd‖ ≤
        ‖F‖ + ‖F - (-1 : ℂ) ^ j * (j - 1).factorial * Sd‖ := by
      calc
        ‖(-1 : ℂ) ^ j * (j - 1).factorial * Sd‖ =
            ‖F - (F - (-1 : ℂ) ^ j * (j - 1).factorial * Sd)‖ := by
          congr 1
          ring
        _ ≤ _ := norm_sub_le _ _
    simpa [norm_mul] using htri
  have hfacPos : (0 : ℝ) < (j - 1).factorial := by positivity
  have hlossPos : 0 < turanSecondLoss K M := by
    apply turanSecondLoss_pos
    dsimp [K]
    exact Finset.card_pos.mpr ⟨rho₀, Finsupp.mem_support_iff.mpr hZrho₀⟩
  have hXpos : 0 < turanSecondLoss K M * (2 * eta) ^ j := by positivity
  have htailNonneg : 0 ≤ ‖Sd - Sz‖ := norm_nonneg _
  have hderivNonneg : 0 ≤
      ‖F - (-1 : ℂ) ^ j * (j - 1).factorial * Sd‖ := norm_nonneg _
  have hderivUse :
      ‖F - (-1 : ℂ) ^ j * (j - 1).factorial * Sd‖ ≤
        (j - 1).factorial *
          (16 * ((Ad : ℝ) *
            Real.log ((q : ℝ) * (|t| + 2))) / 3) := by
    simpa only [F] using hderivNorm
  let Etail : ℝ :=
    64 * (Real.log 4 + 4) / (4 * eta) ^ j +
      ((1024 * (Al : ℝ) / 3) *
        Real.log ((q : ℝ) * (|t| + 2))) / (4 * eta) ^ (j - 1) +
      (2 * (Af : ℝ) * Real.log ((q : ℝ) * (|t| + 2))) /
        (1 / 2 : ℝ) ^ j
  let Ederiv : ℝ :=
    16 * ((Ad : ℝ) * Real.log ((q : ℝ) * (|t| + 2))) / 3
  have htailUse : ‖Sd - Sz‖ ≤ Etail := by
    simpa only [Etail] using htailNorm
  have hderivUse' :
      ‖F - (-1 : ℂ) ^ j * (j - 1).factorial * Sd‖ ≤
        (j - 1).factorial * Ederiv := by
    simpa only [Ederiv] using hderivUse
  have herror' :
      turanSecondLoss K M * (2 * eta) ^ j * (Etail + Ederiv) ≤ 1 / 4 := by
    simpa only [Etail, Ederiv] using herror
  let X : ℝ := turanSecondLoss K M * (2 * eta) ^ j
  let f : ℝ := ((j - 1).factorial : ℝ)
  have hXnonneg : 0 ≤ X := le_of_lt (by simpa only [X] using hXpos)
  have hfnonneg : 0 ≤ f := le_of_lt (by simpa only [f] using hfacPos)
  have hlocalFac : f ≤ f * (X * ‖Sz‖) := by
    calc
      f = f * 1 := by ring
      _ ≤ f * (X * ‖Sz‖) := by
        apply mul_le_mul_of_nonneg_left _ hfnonneg
        simpa only [X] using hlocal
  have hsumBound :
      f * ‖Sz‖ ≤ ‖F‖ +
        ‖F - (-1 : ℂ) ^ j * (j - 1).factorial * Sd‖ +
        f * ‖Sd - Sz‖ := by
    calc
      f * ‖Sz‖ ≤ f * (‖Sd‖ + ‖Sd - Sz‖) := by
        exact mul_le_mul_of_nonneg_left hSz hfnonneg
      _ = f * ‖Sd‖ + f * ‖Sd - Sz‖ := by ring
      _ ≤ (‖F‖ +
          ‖F - (-1 : ℂ) ^ j * (j - 1).factorial * Sd‖) +
          f * ‖Sd - Sz‖ := by
        simpa only [f, add_comm] using
          add_le_add_right hscaled (f * ‖Sd - Sz‖)
  have herrBound :
      ‖F - (-1 : ℂ) ^ j * (j - 1).factorial * Sd‖ +
          f * ‖Sd - Sz‖ ≤ f * (Ederiv + Etail) := by
    calc
      ‖F - (-1 : ℂ) ^ j * (j - 1).factorial * Sd‖ +
          f * ‖Sd - Sz‖ ≤ f * Ederiv + f * Etail := by
        exact add_le_add (by simpa only [f] using hderivUse')
          (mul_le_mul_of_nonneg_left htailUse hfnonneg)
      _ = f * (Ederiv + Etail) := by ring
  have hscaledError : X *
        (‖F - (-1 : ℂ) ^ j * (j - 1).factorial * Sd‖ +
          f * ‖Sd - Sz‖) ≤ f * (1 / 4) := by
    calc
      X * (‖F - (-1 : ℂ) ^ j * (j - 1).factorial * Sd‖ +
          f * ‖Sd - Sz‖) ≤ X * (f * (Ederiv + Etail)) := by
        exact mul_le_mul_of_nonneg_left herrBound hXnonneg
      _ = f * (X * (Etail + Ederiv)) := by ring
      _ ≤ f * (1 / 4) := by
        apply mul_le_mul_of_nonneg_left _ hfnonneg
        simpa only [X] using herror'
  have hfacUpper : f ≤ X * ‖F‖ + f * (1 / 4) := by
    calc
      f ≤ f * (X * ‖Sz‖) := hlocalFac
      _ = X * (f * ‖Sz‖) := by ring
      _ ≤ X * (‖F‖ +
          ‖F - (-1 : ℂ) ^ j * (j - 1).factorial * Sd‖ +
          f * ‖Sd - Sz‖) := by
        exact mul_le_mul_of_nonneg_left hsumBound hXnonneg
      _ = X * ‖F‖ + X *
          (‖F - (-1 : ℂ) ^ j * (j - 1).factorial * Sd‖ +
            f * ‖Sd - Sz‖) := by ring
      _ ≤ X * ‖F‖ + f * (1 / 4) :=
        add_le_add (le_refl _) hscaledError
  have hfpos : 0 < f := by simpa only [f] using hfacPos
  change f * (1 / 2) < X * ‖F‖
  nlinarith

end

end Erdos48
