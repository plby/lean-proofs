/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos48.PointwiseZeroDetectorSecondParameters

/-!
# Uniform variable-order pointwise zero detector

This file combines the local zero-multiplicity estimate with the numerical
contraction for Turan's second theorem.  The resulting derivative order is
bounded linearly in `1 + eta * log (q * (|t| + 2))`, with no boundedness
assumption on that logarithmic height.
-/

namespace Erdos48

open Complex Metric
open BoundedGaps.Maynard

noncomputable section

/-- The integral height which controls the variable detector order. -/
noncomputable def variableDetectorHeight (q : ℕ) (t eta : ℝ) : ℕ :=
  Nat.ceil (1 + eta * Real.log ((q : ℝ) * (|t| + 2)))

/-- Every primitive zero in the local disk forces a large logarithmic
derivative at an order bounded linearly by `variableDetectorHeight`.  All
constants are absolute and chosen before the conductor, height, width, and
zero. -/
theorem exists_variable_pointwise_zero_detector :
    ∃ κ D : ℕ, 1 ≤ κ ∧ 1 ≤ D ∧
      ∀ (q : ℕ) [NeZero q], ∀ (hq : 1 < q),
        ∀ (chi : DirichletCharacter ℂ q), ∀ (hchi : chi.IsPrimitive),
          ∀ (t eta : ℝ), 0 < eta → eta ≤ 1 / 8 →
            ∀ (rho₀ : ℂ),
              DirichletCharacter.LFunction chi rho₀ = 0 →
              dist rho₀ (((1 + eta : ℝ) : ℂ) + t * I) ≤ 2 * eta →
              ∀ H : ℕ, variableDetectorHeight q t eta ≤ H →
              let Z := smallDiskZeroFinsupp hq chi hchi t eta
              ∃ j ∈ Finset.Icc (D * H + 1) (D * H + Z.support.card),
                Z.support.card ≤ κ * H ∧
                  j ≤ (D + κ) * H ∧
                  ((j - 1).factorial : ℝ) * (1 / 2 : ℝ) <
                    turanSecondLoss Z.support.card (D * H) *
                      (2 * eta) ^ j *
                        ‖iteratedDeriv (j - 1)
                          (fun w ↦ -logDeriv
                            (DirichletCharacter.LFunction chi) w)
                          (((1 + eta : ℝ) : ℂ) + t * I)‖ := by
  obtain ⟨Am, Al, Af, Ad, hAm, hAl, hAf, hAd, hdetector⟩ :=
    exists_pointwise_zero_detector_second_of_error_budget
  obtain ⟨Am', hAm', hmass⟩ := exists_smallDiskZeroMultiplicity_bound
  let Cmass : ℝ := 32 * (Real.log 4 + 4) + 256 * (Am' : ℝ) / 3
  let κ : ℕ := max 1 (Nat.ceil Cmass)
  let Cerr : ℝ := 64 * (Real.log 4 + 4) +
    (4096 * (Al : ℝ) / 3 + 16 * (Af : ℝ) + 64 * (Ad : ℝ) / 3)
  have hCmass : 0 ≤ Cmass := by dsimp [Cmass]; positivity
  have hκ : 1 ≤ κ := le_max_left _ _
  have hCerr : 0 ≤ Cerr := by dsimp [Cerr]; positivity
  obtain ⟨D, hD, hcontract⟩ :=
    exists_turanSecond_contraction_parameter κ Cerr hCerr
  refine ⟨κ, D, hκ, hD, ?_⟩
  intro q _ hq chi hchi t eta heta heta8 rho₀ hzero hrho H hHeight
  dsimp only
  let B : ℝ := (q : ℝ) * (|t| + 2)
  let h : ℝ := eta * Real.log B
  let Z := smallDiskZeroFinsupp hq chi hchi t eta
  let K : ℕ := Z.support.card
  have hB4 : 4 ≤ B := by
    have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq
    have ht2 : (2 : ℝ) ≤ |t| + 2 := by linarith [abs_nonneg t]
    dsimp [B]
    nlinarith
  have hlog : 0 ≤ Real.log B := Real.log_nonneg (by linarith)
  have hh : 0 ≤ h := by dsimp [h]; positivity
  have hceilLocal :
      1 + h ≤ (variableDetectorHeight q t eta : ℝ) := by
    simpa only [variableDetectorHeight, h, B] using
      (Nat.le_ceil (1 + h))
  have hHeightCast :
      (variableDetectorHeight q t eta : ℝ) ≤ (H : ℝ) := by
    exact_mod_cast hHeight
  have hceil : 1 + h ≤ (H : ℝ) := hceilLocal.trans hHeightCast
  have hHcast : (1 : ℝ) ≤ H := by linarith
  have hH : 1 ≤ H := by exact_mod_cast hHcast
  have hhH : h ≤ (H : ℝ) := by linarith
  have heta1 : eta ≤ 1 := by linarith
  have hmass' := hmass q hq chi hchi t eta heta heta1
  have hmassC : Z.sum (fun _ m ↦ (m : ℝ)) ≤ Cmass * H := by
    have hfirst :
        16 * (Real.log 4 + 4) * (1 + eta) ≤
          32 * (Real.log 4 + 4) := by
      have hlog4 : 0 ≤ Real.log 4 + 4 := by positivity
      nlinarith
    have hsecond :
        (256 * (Am' : ℝ) / 3) * eta * Real.log B ≤
          (256 * (Am' : ℝ) / 3) * H := by
      calc
        (256 * (Am' : ℝ) / 3) * eta * Real.log B =
            (256 * (Am' : ℝ) / 3) * h := by simp only [h]; ring
        _ ≤ (256 * (Am' : ℝ) / 3) * H := by gcongr
    calc
      Z.sum (fun _ m ↦ (m : ℝ)) ≤
          16 * (Real.log 4 + 4) * (1 + eta) +
            (256 * (Am' : ℝ) / 3) * eta * Real.log B := by
        simpa only [Z, B] using hmass'
      _ ≤ 32 * (Real.log 4 + 4) +
            (256 * (Am' : ℝ) / 3) * H := add_le_add hfirst hsecond
      _ ≤ Cmass * H := by
        dsimp [Cmass]
        have hbase : (0 : ℝ) ≤ 32 * (Real.log 4 + 4) := by positivity
        nlinarith
  have hcardMass : (K : ℝ) ≤ Z.sum (fun _ m ↦ (m : ℝ)) := by
    have hnat := finsupp_support_card_le_sum_nat Z
    exact_mod_cast hnat
  have hCmassκ : Cmass ≤ (κ : ℝ) := by
    exact (Nat.le_ceil Cmass).trans (by
      exact_mod_cast (le_max_right 1 (Nat.ceil Cmass)))
  have hKcast : (K : ℝ) ≤ (κ * H : ℕ) := by
    calc
      (K : ℝ) ≤ Z.sum (fun _ m ↦ (m : ℝ)) := hcardMass
      _ ≤ Cmass * H := hmassC
      _ ≤ (κ : ℝ) * H := mul_le_mul_of_nonneg_right hCmassκ (by positivity)
      _ = (κ * H : ℕ) := by norm_cast
  have hKκ : K ≤ κ * H := by exact_mod_cast hKcast
  have hrhoRe : rho₀.re < 1 :=
    LFunction_zero_re_lt_one_of_isPrimitive hq chi hchi hzero
  have horder : 0 < analyticOrderNatAt
      (DirichletCharacter.LFunction chi) rho₀ :=
    (LFunction_zero_local_logDeriv_expansion
      (character_ne_one_of_isPrimitive hq chi hchi) hzero).1
  have hZrho₀ : Z rho₀ ≠ 0 := by
    dsimp [Z]
    rw [smallDiskZeroFinsupp_apply, smallDiskZeroMultiplicity,
      if_pos (hrho.trans (by linarith : 2 * eta ≤ 4 * eta))]
    exact horder.ne'
  have hK : 1 ≤ K := by
    dsimp [K]
    exact Finset.card_pos.mpr ⟨rho₀, Finsupp.mem_support_iff.mpr hZrho₀⟩
  have hcoeff :
      pointwiseSecondErrorCoefficient Al Af Ad h ≤ Cerr * H := by
    unfold pointwiseSecondErrorCoefficient
    dsimp [Cerr]
    have hconst : 0 ≤ 64 * (Real.log 4 + 4) := by positivity
    have hslope : 0 ≤ 4096 * (Al : ℝ) / 3 + 16 * (Af : ℝ) +
        64 * (Ad : ℝ) / 3 := by positivity
    nlinarith
  have hbudget :
      ∀ j ∈ Finset.Icc (D * H + 1) (D * H + K),
        turanSecondLoss K (D * H) * (2 * eta) ^ j *
          pointwiseZeroDetectorError Al Af Ad q t eta j ≤ 1 / 4 := by
    intro j hj
    have hjPos : 1 ≤ j :=
      (Nat.succ_le_succ (Nat.zero_le (D * H))).trans
        (Finset.mem_Icc.mp hj).1
    have hscaled := pointwiseZeroDetectorError_second_scaled_le
      Al Af Ad q j t eta heta heta8 hjPos
      (by simpa only [B] using hlog)
    have hlossNonneg : 0 ≤ turanSecondLoss K (D * H) :=
      (turanSecondLoss_pos (by omega : 0 < K)).le
    calc
      turanSecondLoss K (D * H) * (2 * eta) ^ j *
          pointwiseZeroDetectorError Al Af Ad q t eta j =
          turanSecondLoss K (D * H) *
            ((2 * eta) ^ j *
              pointwiseZeroDetectorError Al Af Ad q t eta j) := by ring
      _ ≤ turanSecondLoss K (D * H) *
          ((1 / 2 : ℝ) ^ j *
            pointwiseSecondErrorCoefficient Al Af Ad h) := by gcongr
      _ ≤ turanSecondLoss K (D * H) *
          ((1 / 2 : ℝ) ^ j * (Cerr * H)) := by gcongr
      _ = turanSecondLoss K (D * H) * (1 / 2 : ℝ) ^ j *
          (Cerr * H) := by ring
      _ ≤ 1 / 4 := hcontract H K j hH hK hKκ (Finset.mem_Icc.mp hj).1
  obtain ⟨j, hj, hjlarge⟩ :=
    hdetector q hq chi hchi t eta heta heta8 rho₀ hzero hrho
      (D * H) (Nat.mul_pos (by omega) (by omega))
        (by simpa only [K, Z] using hbudget)
  refine ⟨j, by simpa only [Z, K] using hj,
    by simpa only [Z, K] using hKκ, ?_, ?_⟩
  · have hjupper := (Finset.mem_Icc.mp hj).2
    calc
      j ≤ D * H + K := hjupper
      _ ≤ D * H + κ * H := Nat.add_le_add_left hKκ _
      _ = (D + κ) * H := by rw [add_mul]
  · simpa only [Z, K] using hjlarge

end

end Erdos48
