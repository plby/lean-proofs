/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos48.VariablePointwiseZeroDetector
import ErdosProblems.Erdos48.FiniteSeriesDetector

/-!
# Truncating the variable-order zero detector

The truncation radius now depends linearly on an ambient order bound.  Its
explicit exponential factor absorbs both the Dirichlet-series tail and the
coefficient loss in Turan's second theorem.
-/

namespace Erdos48

open Complex Metric LSeries
open BoundedGaps.Maynard

noncomputable section

/-- Radius used to truncate all variable-order detectors of order at most
`J`. -/
noncomputable def variableZeroDetectorTailRadius (J : ℕ) : ℝ :=
  4 * Real.log
    (1 + 12 * (Real.log 4 + 4) * (4624 : ℝ) ^ J)

theorem variableZeroDetectorTailRadius_pos (J : ℕ) :
    0 < variableZeroDetectorTailRadius J := by
  unfold variableZeroDetectorTailRadius
  have hpos : 0 < 12 * (Real.log 4 + 4) * (4624 : ℝ) ^ J := by positivity
  exact mul_pos (by norm_num) (Real.log_pos (by linarith))

/-- Uniform elementary upper bound for Turan's coefficient loss when both
its number of points and its starting order are at most `J`. -/
theorem turanSecondLoss_le_orderEnvelope
    {K M J : ℕ} (hK : 1 ≤ K) (hKJ : K ≤ J) (hMJ : M ≤ J) :
    turanSecondLoss K M ≤ (578 : ℝ) ^ J / 2 := by
  rw [turanSecondLoss_eq_closed]
  have hpolyNat := nat_mul_succ_le_four_pow hK
  have hpoly : (K : ℝ) * (K + 1 : ℝ) ≤ (4 : ℝ) ^ K := by
    exact_mod_cast hpolyNat
  have h17 : (17 / 16 : ℝ) ^ M ≤ (17 / 16 : ℝ) ^ J :=
    pow_le_pow_right₀ (by norm_num) hMJ
  have h544 : (544 : ℝ) ^ K ≤ (544 : ℝ) ^ J :=
    pow_le_pow_right₀ (by norm_num) hKJ
  calc
    ((K : ℝ) * (K + 1 : ℝ) / 2) * (17 / 16 : ℝ) ^ M *
        (136 : ℝ) ^ K ≤
      ((4 : ℝ) ^ K / 2) * (17 / 16 : ℝ) ^ J *
        (136 : ℝ) ^ K := by gcongr
    _ = ((17 / 16 : ℝ) ^ J * (544 : ℝ) ^ K) / 2 := by
      have hcombine : (4 : ℝ) ^ K * (136 : ℝ) ^ K =
          (544 : ℝ) ^ K := by
        rw [← mul_pow]
        norm_num
      rw [← hcombine]
      ring
    _ ≤ ((17 / 16 : ℝ) ^ J * (544 : ℝ) ^ J) / 2 := by gcongr
    _ = (578 : ℝ) ^ J / 2 := by
      rw [← mul_pow]
      norm_num

/-- The explicit variable truncation radius makes the scaled tail no larger
than one quarter of the distinguished-zero contribution. -/
theorem variable_weighted_vonMangoldt_tail_budget
    {K M j J : ℕ} (hK : 1 ≤ K) (hKJ : K ≤ J)
    (hMJ : M ≤ J) (hjJ : j ≤ J) (hjPos : 1 ≤ j)
    {eta : ℝ} (heta : 0 < eta) (heta1 : eta ≤ 1) :
    turanSecondLoss K M * (2 * eta) ^ j *
        (Real.exp (-variableZeroDetectorTailRadius J / 4) *
          ((j - 1).factorial : ℝ) * (4 / eta) ^ (j - 1) *
            ((Real.log 4 + 4) * (1 + eta / 2) / (eta / 2))) ≤
      ((j - 1).factorial : ℝ) * (1 / 4 : ℝ) := by
  let C : ℝ := Real.log 4 + 4
  let E : ℝ := 1 + 12 * C * (4624 : ℝ) ^ J
  have hC : 0 < C := by dsimp [C]; positivity
  have hE : 0 < E := by dsimp [E]; positivity
  have hexp : Real.exp (-variableZeroDetectorTailRadius J / 4) = E⁻¹ := by
    have harg : -variableZeroDetectorTailRadius J / 4 = -Real.log E := by
      dsimp [variableZeroDetectorTailRadius, E, C]
      ring
    rw [harg, Real.exp_neg, Real.exp_log hE]
  have hratio : C * (1 + eta / 2) / (eta / 2) ≤ 3 * C / eta := by
    rw [div_le_div_iff₀ (by positivity : 0 < eta / 2) heta]
    have hsmall : 1 + eta / 2 ≤ (3 / 2 : ℝ) := by linarith
    have hCeta : 0 ≤ C * eta := by positivity
    calc
      C * (1 + eta / 2) * eta = (1 + eta / 2) * (C * eta) := by ring
      _ ≤ (3 / 2 : ℝ) * (C * eta) :=
        mul_le_mul_of_nonneg_right hsmall hCeta
      _ = 3 * C * (eta / 2) := by ring
  have hJ : 1 ≤ J := hjPos.trans hjJ
  have hkJ : j - 1 ≤ J := by omega
  have h4 : (4 : ℝ) ^ (j - 1) ≤ (4 : ℝ) ^ J :=
    pow_le_pow_right₀ (by norm_num) hkJ
  have h2 : (2 : ℝ) ^ j ≤ (2 : ℝ) ^ J :=
    pow_le_pow_right₀ (by norm_num) hjJ
  have hloss := turanSecondLoss_le_orderEnvelope hK hKJ hMJ
  have hcoef :
      E⁻¹ * turanSecondLoss K M * (3 * C) *
          (4 : ℝ) ^ (j - 1) * (2 : ℝ) ^ j ≤ 1 / 4 := by
    calc
      E⁻¹ * turanSecondLoss K M * (3 * C) *
          (4 : ℝ) ^ (j - 1) * (2 : ℝ) ^ j ≤
        E⁻¹ * ((578 : ℝ) ^ J / 2) * (3 * C) *
          (4 : ℝ) ^ J * (2 : ℝ) ^ J := by gcongr
      _ = E⁻¹ * ((3 * C / 2) * (4624 : ℝ) ^ J) := by
        have hpow : (578 : ℝ) ^ J * (4 : ℝ) ^ J * (2 : ℝ) ^ J =
            (4624 : ℝ) ^ J := by
          rw [← mul_pow, ← mul_pow]
          norm_num
        rw [← hpow]
        ring
      _ ≤ 1 / 4 := by
        rw [inv_mul_eq_div]
        apply (div_le_iff₀ hE).2
        dsimp [E]
        have hpowNonneg : 0 ≤ (4624 : ℝ) ^ J := by positivity
        nlinarith
  have htailRatio :
      Real.exp (-variableZeroDetectorTailRadius J / 4) *
          ((j - 1).factorial : ℝ) * (4 / eta) ^ (j - 1) *
            (C * (1 + eta / 2) / (eta / 2)) ≤
        E⁻¹ * ((j - 1).factorial : ℝ) * (4 / eta) ^ (j - 1) *
          (3 * C / eta) := by
    rw [hexp]
    gcongr
  have hcancel :
      (2 * eta) ^ j * (4 / eta) ^ (j - 1) * eta⁻¹ =
        (2 : ℝ) ^ j * (4 : ℝ) ^ (j - 1) := by
    let k := j - 1
    have hjEq : j = k + 1 := by dsimp [k]; omega
    rw [hjEq, pow_succ, mul_pow, div_pow]
    field_simp [heta.ne']
    rw [show k + 1 - 1 = k by omega, pow_succ]
    ring
  calc
    turanSecondLoss K M * (2 * eta) ^ j *
        (Real.exp (-variableZeroDetectorTailRadius J / 4) *
          ((j - 1).factorial : ℝ) * (4 / eta) ^ (j - 1) *
            ((Real.log 4 + 4) * (1 + eta / 2) / (eta / 2))) ≤
      turanSecondLoss K M * (2 * eta) ^ j *
        (E⁻¹ * ((j - 1).factorial : ℝ) * (4 / eta) ^ (j - 1) *
          (3 * C / eta)) := by
            simpa only [C] using
              mul_le_mul_of_nonneg_left htailRatio
                (mul_nonneg (turanSecondLoss_pos (by omega : 0 < K)).le
                  (by positivity))
    _ = (E⁻¹ * turanSecondLoss K M * (3 * C) *
          (4 : ℝ) ^ (j - 1) * (2 : ℝ) ^ j) *
            ((j - 1).factorial : ℝ) := by
      calc
        turanSecondLoss K M * (2 * eta) ^ j *
            (E⁻¹ * ((j - 1).factorial : ℝ) * (4 / eta) ^ (j - 1) *
              (3 * C / eta)) =
            E⁻¹ * turanSecondLoss K M * (3 * C) *
              ((2 * eta) ^ j * (4 / eta) ^ (j - 1) * eta⁻¹) *
                ((j - 1).factorial : ℝ) := by
                  rw [div_eq_mul_inv]
                  ring
        _ = _ := by rw [hcancel]; ring
    _ ≤ (1 / 4 : ℝ) * ((j - 1).factorial : ℝ) := by gcongr
    _ = ((j - 1).factorial : ℝ) * (1 / 4 : ℝ) := by ring

/-- Variable-order pointwise detector after truncation to a finite weighted
von Mangoldt polynomial.  The ambient bound `J` may be chosen globally for
all conductors and ordinates in a density rectangle. -/
theorem exists_variable_finite_series_detector :
    ∃ κ D : ℕ, 1 ≤ κ ∧ 1 ≤ D ∧
      ∀ (q : ℕ) [NeZero q], ∀ (hq : 1 < q),
        ∀ (chi : DirichletCharacter ℂ q), ∀ (hchi : chi.IsPrimitive),
          ∀ (t eta : ℝ), 0 < eta → eta ≤ 1 / 8 →
            ∀ (rho₀ : ℂ),
              DirichletCharacter.LFunction chi rho₀ = 0 →
              dist rho₀ (((1 + eta : ℝ) : ℂ) + t * I) ≤ 2 * eta →
              ∀ H J : ℕ, variableDetectorHeight q t eta ≤ H →
              (D + κ) * H ≤ J →
              let Z := smallDiskZeroFinsupp hq chi hchi t eta
              let K := Z.support.card
              let M := D * H
              let R := variableZeroDetectorTailRadius J
              let N := zeroDetectorCutoff R eta
              ∃ j ∈ Finset.Icc (M + 1) (M + K),
                K ≤ κ * H ∧ j ≤ J ∧
                  ((j - 1).factorial : ℝ) * (1 / 4 : ℝ) <
                    turanSecondLoss K M * (2 * eta) ^ j *
                      ‖∑ n ∈ Finset.Icc 1 N,
                        LSeries.term (fun m : ℕ ↦
                          (Real.log m : ℂ) ^ (j - 1) * chi m *
                            (ArithmeticFunction.vonMangoldt m : ℂ))
                          (((1 + eta : ℝ) : ℂ) + t * I) n‖ := by
  obtain ⟨κ, D, hκ, hD, hdetector⟩ :=
    exists_variable_pointwise_zero_detector
  refine ⟨κ, D, hκ, hD, ?_⟩
  intro q _ hq chi hchi t eta heta heta8 rho₀ hzero hrho H J hHeight hJ
  dsimp only
  let Z := smallDiskZeroFinsupp hq chi hchi t eta
  let K := Z.support.card
  let M := D * H
  let R := variableZeroDetectorTailRadius J
  let N := zeroDetectorCutoff R eta
  obtain ⟨j, hj, hKκ, hjBound, hjfullDeriv⟩ :=
    hdetector q hq chi hchi t eta heta heta8 rho₀ hzero hrho H hHeight
  have hjJ : j ≤ J := hjBound.trans hJ
  have hweighted :
      ((j - 1).factorial : ℝ) * (1 / 2 : ℝ) <
        turanSecondLoss K M * (2 * eta) ^ j *
          ‖LSeries (fun n : ℕ ↦
              (Real.log n : ℂ) ^ (j - 1) * chi n *
                (ArithmeticFunction.vonMangoldt n : ℂ))
            (((1 + eta : ℝ) : ℂ) + t * I)‖ := by
    let z : ℂ := ((1 + eta : ℝ) : ℂ) + t * I
    have hzre : z.re = 1 + eta := by simp [z]
    have hz1 : 1 < z.re := by rw [hzre]; linarith
    have hid := iteratedDeriv_neg_logDeriv_LFunction_eq_weighted_LSeries
      (k := j - 1) chi hz1
    rw [hid] at hjfullDeriv
    simpa only [Z, K, M, z, norm_mul, norm_pow, norm_neg,
      norm_one, one_pow, one_mul] using hjfullDeriv
  let z : ℂ := ((1 + eta : ℝ) : ℂ) + t * I
  let c : ℕ → ℂ := fun m ↦
    (Real.log m : ℂ) ^ (j - 1) * chi m *
      (ArithmeticFunction.vonMangoldt m : ℂ)
  let P : ℂ := ∑ n ∈ Finset.Icc 1 N, LSeries.term c z n
  have hNpos : 0 < N := by
    simpa only [N] using zeroDetectorCutoff_pos R eta
  have hNexp : Real.exp (R / eta) ≤ (N : ℝ) := by
    simpa only [N] using exp_div_le_zeroDetectorCutoff R eta
  have htailRaw := norm_weighted_vonMangoldt_LSeries_sub_sum_le
    chi eta R t heta (by linarith : eta ≤ 1) N (j - 1)
      hNpos hNexp
  have hjLocal : j ∈ Finset.Icc (M + 1) (M + K) := by
    simpa only [Z, K, M] using hj
  have hK : 1 ≤ K := by
    have hjLower := (Finset.mem_Icc.mp hjLocal).1
    have hjUpper := (Finset.mem_Icc.mp hjLocal).2
    omega
  have hjPos : 1 ≤ j :=
    (Nat.succ_le_succ (Nat.zero_le M)).trans (Finset.mem_Icc.mp hjLocal).1
  have hKJ : K ≤ J := by
    have hKH : K ≤ κ * H := by simpa only [Z, K] using hKκ
    exact hKH.trans (by
      calc
        κ * H ≤ (D + κ) * H := by gcongr <;> omega
        _ ≤ J := hJ)
  have hMJ : M ≤ J := by
    dsimp [M]
    calc
      D * H ≤ (D + κ) * H := by gcongr <;> omega
      _ ≤ J := hJ
  have htailBudget := variable_weighted_vonMangoldt_tail_budget
    hK hKJ hMJ hjJ hjPos heta (by linarith : eta ≤ 1)
  have htailScaled :
      turanSecondLoss K M * (2 * eta) ^ j * ‖LSeries c z - P‖ ≤
        ((j - 1).factorial : ℝ) * (1 / 4 : ℝ) := by
    exact (mul_le_mul_of_nonneg_left htailRaw
      (mul_nonneg (turanSecondLoss_pos (by omega : 0 < K)).le
        (by positivity))).trans
        (by simpa only [R, c, z, N, P] using htailBudget)
  have htri : ‖LSeries c z‖ ≤ ‖P‖ + ‖LSeries c z - P‖ := by
    calc
      ‖LSeries c z‖ = ‖P + (LSeries c z - P)‖ := by congr 1; ring
      _ ≤ ‖P‖ + ‖LSeries c z - P‖ := norm_add_le _ _
  refine ⟨j, by simpa only [Z, K, M] using hj,
    by simpa only [Z, K] using hKκ, hjJ, ?_⟩
  have hscale : 0 ≤ turanSecondLoss K M * (2 * eta) ^ j :=
    mul_nonneg (turanSecondLoss_pos (by omega : 0 < K)).le (by positivity)
  have hscaledTri := mul_le_mul_of_nonneg_left htri hscale
  change ((j - 1).factorial : ℝ) * (1 / 4 : ℝ) <
    turanSecondLoss K M * (2 * eta) ^ j * ‖P‖
  have hfull : ((j - 1).factorial : ℝ) * (1 / 2 : ℝ) <
      turanSecondLoss K M * (2 * eta) ^ j * ‖LSeries c z‖ := by
    simpa only [c, z] using hweighted
  nlinarith

end

end Erdos48
