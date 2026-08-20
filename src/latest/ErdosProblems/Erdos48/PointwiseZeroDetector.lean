/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos48.RadiusSixTail
import BoundedGaps.BombieriVinogradov.Analytic.LocalLogarithmicResidue

/-!
# Pointwise Turán detector for a zero near one

The theorem in this file is the completed local detector.  Its only
remaining hypothesis is an explicit real inequality saying that the
annular, far-zero, and regularized analytic errors fit inside half of the
distinguished-zero contribution.  A later parameter lemma verifies that
inequality uniformly in the log-free density range.
-/

namespace Erdos48

open Complex Metric
open BoundedGaps.Maynard

noncomputable section

/-- The explicit error envelope in the pointwise zero detector. -/
noncomputable def pointwiseZeroDetectorError
    (Al Af Ad : ℕ) (q : ℕ) (t eta : ℝ) (j : ℕ) : ℝ :=
  64 * (Real.log 4 + 4) / (4 * eta) ^ j +
    ((1024 * (Al : ℝ) / 3) *
      Real.log ((q : ℝ) * (|t| + 2))) / (4 * eta) ^ (j - 1) +
    (2 * (Af : ℝ) * Real.log ((q : ℝ) * (|t| + 2))) /
      (1 / 2 : ℝ) ^ j +
    16 * ((Ad : ℝ) * Real.log ((q : ℝ) * (|t| + 2))) / 3

/-- A zero within `2*eta` of `1+eta+it` forces a large high derivative of
`-L'/L`, provided the displayed explicit error budget holds throughout the
finite range of derivative orders selected by Turán's theorem. -/
theorem exists_pointwise_zero_detector_of_error_budget :
    ∃ Am Al Af Ad : ℕ,
      37 ≤ Am ∧ 37 ≤ Al ∧ 37 ≤ Af ∧ 37 ≤ Ad ∧
      ∀ (q : ℕ) [NeZero q], ∀ (hq : 1 < q),
        ∀ (chi : DirichletCharacter ℂ q), ∀ (hchi : chi.IsPrimitive),
          ∀ (t eta : ℝ), 0 < eta → eta ≤ 1 / 8 →
            ∀ (rho₀ : ℂ),
              DirichletCharacter.LFunction chi rho₀ = 0 →
              dist rho₀ (((1 + eta : ℝ) : ℂ) + t * I) ≤ 2 * eta →
              ∀ (L : ℕ), 2 ≤ L →
                let z : ℂ := ((1 + eta : ℝ) : ℂ) + t * I
                let Z := smallDiskZeroFinsupp hq chi hchi t eta
                (∀ j : ℕ, L ≤ j → j ≤ L * Z.sum (fun _ m ↦ m) →
                  pointwiseZeroDetectorError Al Af Ad q t eta j ≤
                    (1 / 12 : ℝ) * (2 * eta)⁻¹ ^ j) →
                ∃ j : ℕ,
                  L ≤ j ∧ j ≤ L * Z.sum (fun _ m ↦ m) ∧
                    (j - 1).factorial * (1 / 12 : ℝ) *
                        (2 * eta)⁻¹ ^ j <
                      ‖iteratedDeriv (j - 1)
                        (fun w ↦ -logDeriv
                          (DirichletCharacter.LFunction chi) w) z‖ := by
  obtain ⟨Am, hAm, hmass⟩ := exists_smallDiskZeroMultiplicity_bound
  obtain ⟨Al, Af, hAl, hAf, htail⟩ :=
    exists_norm_radiusSix_sub_smallDisk_powerSum_le
  obtain ⟨Ad, hAd, hderiv⟩ := exists_radiusSix_iteratedDeriv_approximation
  refine ⟨Am, Al, Af, Ad, hAm, hAl, hAf, hAd, ?_⟩
  intro q _ hq chi hchi t eta heta0 heta8 rho₀ hzero hrho₀ L hL
  dsimp only
  let z : ℂ := ((1 + eta : ℝ) : ℂ) + t * I
  let Z := smallDiskZeroFinsupp hq chi hchi t eta
  let D := radiusSixZeroFinsupp hq chi hchi t
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
  obtain ⟨j, hjL, hjupper, hjlarge⟩ :=
    exists_norm_sparseWeightedReciprocalPowerSum_gt_distinguished
      Z hZrho₀ hzrho₀ (Nat.zero_lt_of_lt hL)
  refine ⟨j, hjL, hjupper, ?_⟩
  have hj2 : 2 ≤ j := hL.trans hjL
  let Sz : ℂ := Z.sum
    (fun rho m ↦ (m : ℂ) / (z - rho) ^ j)
  let Sd : ℂ := D.sum
    (fun rho m ↦ (m : ℂ) / (z - rho) ^ j)
  have hinv : (2 * eta)⁻¹ ≤ ‖(z - rho₀)⁻¹‖ := by
    rw [norm_inv]
    have hnormPos : 0 < ‖z - rho₀‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hzrho₀)
    apply inv_anti₀ hnormPos
    simpa [z, dist_eq_norm, norm_sub_rev] using hrho₀
  have hinvpow : (2 * eta)⁻¹ ^ j ≤ ‖(z - rho₀)⁻¹‖ ^ j :=
    pow_le_pow_left₀ (by positivity) hinv j
  have hlocal : (1 / 6 : ℝ) * (2 * eta)⁻¹ ^ j < ‖Sz‖ := by
    exact (mul_le_mul_of_nonneg_left hinvpow (by norm_num)).trans_lt (by
      simpa only [Sz] using hjlarge)
  have htail' := htail q hq chi hchi t eta heta0 heta8 j hj2
  have htailNorm : ‖Sd - Sz‖ ≤
      64 * (Real.log 4 + 4) / (4 * eta) ^ j +
        ((1024 * (Al : ℝ) / 3) *
          Real.log ((q : ℝ) * (|t| + 2))) / (4 * eta) ^ (j - 1) +
        (2 * (Af : ℝ) *
          Real.log ((q : ℝ) * (|t| + 2))) /
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
  have hbudget' := hbudget j hjL hjupper
  have herror :
      (64 * (Real.log 4 + 4) / (4 * eta) ^ j +
        ((1024 * (Al : ℝ) / 3) *
          Real.log ((q : ℝ) * (|t| + 2))) / (4 * eta) ^ (j - 1) +
        (2 * (Af : ℝ) *
          Real.log ((q : ℝ) * (|t| + 2))) /
            (1 / 2 : ℝ) ^ j) +
        16 * ((Ad : ℝ) *
          Real.log ((q : ℝ) * (|t| + 2))) / 3 ≤
        (1 / 12 : ℝ) * (2 * eta)⁻¹ ^ j := by
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
  have hFbound :
      ((j - 1).factorial : ℝ) * (1 / 12 : ℝ) *
          (2 * eta)⁻¹ ^ j < ‖F‖ := by
    have htailNonneg : 0 ≤ ‖Sd - Sz‖ := norm_nonneg _
    have hderivNonneg : 0 ≤
        ‖F - (-1 : ℂ) ^ j * (j - 1).factorial * Sd‖ := norm_nonneg _
    have htailUse := htailNorm
    have hderivUse :
        ‖F - (-1 : ℂ) ^ j * (j - 1).factorial * Sd‖ ≤
          (j - 1).factorial *
            (16 * ((Ad : ℝ) *
              Real.log ((q : ℝ) * (|t| + 2))) / 3) := by
      simpa only [F] using hderivNorm
    nlinarith
  simpa only [F] using hFbound

end

end Erdos48
