/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos48.VariableFiniteSeriesDetector
import ErdosProblems.Erdos48.DetectorPropagation

/-!
# Propagation of the variable-order detector

The variable detector carries the coefficient loss from Turan's second
theorem.  A radius exponentially small in the ambient order absorbs this
loss uniformly.  Since the ambient order is linear in
`1 + eta * log (q * (|t| + 2))`, this radius is still a power of the global
conductor-height parameter in the later density estimate.
-/

namespace Erdos48

open Complex LSeries
open BoundedGaps.Maynard

noncomputable section

/-- Relative propagation radius for all detector orders at most `J`. -/
noncomputable def variableDetectorPropagationRadius (J : ℕ) : ℝ :=
  (12 * (Real.log 4 + 4) * (J : ℝ) * (2312 : ℝ) ^ J)⁻¹

theorem variableDetectorPropagationRadius_pos {J : ℕ} (hJ : 1 ≤ J) :
    0 < variableDetectorPropagationRadius J := by
  unfold variableDetectorPropagationRadius
  have hJR : (0 : ℝ) < J := by exact_mod_cast hJ
  positivity

theorem variableDetectorPropagationRadius_le_one {J : ℕ} (hJ : 1 ≤ J) :
    variableDetectorPropagationRadius J ≤ 1 := by
  apply inv_le_one_of_one_le₀
  have hC : (1 : ℝ) ≤ Real.log 4 + 4 := by
    have hlog : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    linarith
  have hJR : (1 : ℝ) ≤ J := by exact_mod_cast hJ
  have hpow : (1 : ℝ) ≤ (2312 : ℝ) ^ J := one_le_pow₀ (by norm_num)
  calc
    (1 : ℝ) ≤ 12 * 1 * 1 * 1 := by norm_num
    _ ≤ 12 * (Real.log 4 + 4) * (J : ℝ) * (2312 : ℝ) ^ J := by
      gcongr

/-- The propagation error, after multiplication by the Turan scale, costs
at most one eighth of the distinguished factorial term. -/
theorem variable_detector_propagation_budget
    {K M j J : ℕ} (hK : 1 ≤ K) (hKJ : K ≤ J)
    (hMJ : M ≤ J) (hj : 1 ≤ j) (hjJ : j ≤ J)
    {eta : ℝ} (heta : 0 < eta) :
    turanSecondLoss K M * (2 * eta) ^ j *
        (variableDetectorPropagationRadius J * eta *
          (3 * (Real.log 4 + 4) * j.factorial *
            (2 / eta) ^ j / eta)) ≤
      ((j - 1).factorial : ℝ) * (1 / 8 : ℝ) := by
  let C : ℝ := Real.log 4 + 4
  let delta : ℝ := variableDetectorPropagationRadius J
  have hC : 0 < C := by dsimp [C]; positivity
  have hJ : 1 ≤ J := hj.trans hjJ
  have hJR : (0 : ℝ) < J := by exact_mod_cast hJ
  have hdelta : 0 < delta := by
    simpa only [delta] using variableDetectorPropagationRadius_pos hJ
  have hloss := turanSecondLoss_le_orderEnvelope hK hKJ hMJ
  have h4 : (4 : ℝ) ^ j ≤ (4 : ℝ) ^ J :=
    pow_le_pow_right₀ (by norm_num) hjJ
  have hjR : (j : ℝ) ≤ J := by exact_mod_cast hjJ
  have hfac : (j.factorial : ℝ) =
      (j : ℝ) * ((j - 1).factorial : ℝ) := by
    exact_mod_cast (Nat.mul_factorial_pred (by omega : j ≠ 0)).symm
  have hcancel :
      (2 * eta) ^ j * eta * ((2 / eta) ^ j / eta) = (4 : ℝ) ^ j := by
    rw [div_pow]
    field_simp [heta.ne']
    calc
      (2 * eta) ^ j * (2 : ℝ) ^ j = ((2 * eta) * 2) ^ j :=
        (mul_pow _ _ _).symm
      _ = (eta * 4) ^ j := by congr 1 <;> ring
      _ = eta ^ j * (4 : ℝ) ^ j := mul_pow _ _ _
  have hcoef :
      delta * 3 * C * turanSecondLoss K M *
          (j : ℝ) * (4 : ℝ) ^ j ≤ 1 / 8 := by
    calc
      delta * 3 * C * turanSecondLoss K M *
          (j : ℝ) * (4 : ℝ) ^ j ≤
        delta * 3 * C * ((578 : ℝ) ^ J / 2) *
          (J : ℝ) * (4 : ℝ) ^ J := by gcongr <;> positivity
      _ = delta * (3 * C / 2) * (J : ℝ) * (2312 : ℝ) ^ J := by
        have hp : (578 : ℝ) ^ J * (4 : ℝ) ^ J =
            (2312 : ℝ) ^ J := by rw [← mul_pow]; norm_num
        calc
          delta * 3 * C * ((578 : ℝ) ^ J / 2) *
              (J : ℝ) * (4 : ℝ) ^ J =
            delta * (3 * C / 2) * (J : ℝ) *
              ((578 : ℝ) ^ J * (4 : ℝ) ^ J) := by ring
          _ = _ := by rw [hp]
      _ = 1 / 8 := by
        dsimp [delta, variableDetectorPropagationRadius]
        field_simp
        ring
  calc
    turanSecondLoss K M * (2 * eta) ^ j *
        (variableDetectorPropagationRadius J * eta *
          (3 * (Real.log 4 + 4) * j.factorial *
            (2 / eta) ^ j / eta)) =
      (delta * 3 * C * turanSecondLoss K M *
        (j : ℝ) * (4 : ℝ) ^ j) *
          ((j - 1).factorial : ℝ) := by
        rw [hfac]
        calc
          turanSecondLoss K M * (2 * eta) ^ j *
              (variableDetectorPropagationRadius J * eta *
                (3 * (Real.log 4 + 4) *
                  ((j : ℝ) * ((j - 1).factorial : ℝ)) *
                    (2 / eta) ^ j / eta)) =
            (delta * 3 * C * turanSecondLoss K M * (j : ℝ) *
              ((2 * eta) ^ j * eta * ((2 / eta) ^ j / eta))) *
                ((j - 1).factorial : ℝ) := by
                  dsimp [delta, C]
                  ring
          _ = _ := by rw [hcancel]
    _ ≤ (1 / 8 : ℝ) * ((j - 1).factorial : ℝ) := by gcongr
    _ = ((j - 1).factorial : ℝ) * (1 / 8 : ℝ) := by ring

/-- A detected zero gives an interval on which the scaled variable-order
finite polynomial remains large. -/
theorem exists_variable_propagated_finite_series_detector :
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
                    ∀ u : ℝ,
                      |u - t| ≤ variableDetectorPropagationRadius J * eta →
                      ((j - 1).factorial : ℝ) * (1 / 8 : ℝ) <
                        turanSecondLoss K M * (2 * eta) ^ j *
                          ‖finiteZeroDetectorPolynomial chi eta (j - 1) N u‖ := by
  obtain ⟨κ, D, hκ, hD, hdetector⟩ :=
    exists_variable_finite_series_detector
  refine ⟨κ, D, hκ, hD, ?_⟩
  intro q _ hq chi hchi t eta heta heta8 rho₀ hzero hrho
    H J hHeight hJ
  dsimp only
  let Z := smallDiskZeroFinsupp hq chi hchi t eta
  let K := Z.support.card
  let M := D * H
  let R := variableZeroDetectorTailRadius J
  let N := zeroDetectorCutoff R eta
  obtain ⟨j, hj, hKκ, hjJ, hjlarge⟩ :=
    hdetector q hq chi hchi t eta heta heta8 rho₀ hzero hrho
      H J hHeight hJ
  have hjLocal : j ∈ Finset.Icc (M + 1) (M + K) := by
    simpa only [Z, K, M] using hj
  have hK : 1 ≤ K := by
    have hlower := (Finset.mem_Icc.mp hjLocal).1
    have hupper := (Finset.mem_Icc.mp hjLocal).2
    omega
  have hjPos : 1 ≤ j :=
    (Nat.succ_le_succ (Nat.zero_le M)).trans
      (Finset.mem_Icc.mp hjLocal).1
  have hKH : K ≤ κ * H := by simpa only [Z, K] using hKκ
  have hKJ : K ≤ J := hKH.trans <| by
    calc
      κ * H ≤ (D + κ) * H := by gcongr <;> omega
      _ ≤ J := hJ
  have hMJ : M ≤ J := by
    dsimp [M]
    calc
      D * H ≤ (D + κ) * H := by gcongr <;> omega
      _ ≤ J := hJ
  let P : ℝ → ℂ := fun u ↦
    finiteZeroDetectorPolynomial chi eta (j - 1) N u
  have htlarge : ((j - 1).factorial : ℝ) * (1 / 4 : ℝ) <
      turanSecondLoss K M * (2 * eta) ^ j * ‖P t‖ := by
    rw [show P t =
        ∑ n ∈ Finset.Icc 1 N,
          LSeries.term (fun m : ℕ ↦
            (Real.log m : ℂ) ^ (j - 1) * chi m *
              (ArithmeticFunction.vonMangoldt m : ℂ))
            (((1 + eta : ℝ) : ℂ) + t * I) n by
      dsimp [P]
      exact (weighted_vonMangoldt_LSeries_sum_eq_polynomial
        chi eta t (j - 1) N).symm]
    simpa only [R, N, Z, K, M] using hjlarge
  refine ⟨j, by simpa only [Z, K, M] using hj, hKH, hjJ, ?_⟩
  intro u hu
  have heta1 : eta ≤ 1 := by linarith
  have hsum := weightedVonMangoldtMajorant_tsum_le eta heta heta1 j
  have hsum0 : 0 ≤ ∑' n, weightedVonMangoldtMajorant eta j n :=
    tsum_nonneg fun n ↦ by unfold weightedVonMangoldtMajorant; positivity
  have htu : |t - u| ≤ variableDetectorPropagationRadius J * eta := by
    simpa only [abs_sub_comm] using hu
  have hlip := norm_finiteZeroDetectorPolynomial_sub_le_tsum
    chi eta heta (j - 1) N t u
  have hlip' :
      ‖P t - P u‖ ≤ |t - u| *
        ∑' n, weightedVonMangoldtMajorant eta j n := by
    simpa only [P, show j - 1 + 1 = j by omega] using hlip
  have hdiffScaled :
      turanSecondLoss K M * (2 * eta) ^ j * ‖P t - P u‖ ≤
        ((j - 1).factorial : ℝ) * (1 / 8 : ℝ) := by
    have hlipBudget : ‖P t - P u‖ ≤
        variableDetectorPropagationRadius J * eta *
          (3 * (Real.log 4 + 4) * j.factorial *
            (2 / eta) ^ j / eta) :=
      hlip'.trans (mul_le_mul htu hsum hsum0
        (mul_nonneg (variableDetectorPropagationRadius_pos
          (hjPos.trans hjJ)).le heta.le))
    exact (mul_le_mul_of_nonneg_left hlipBudget
      (mul_nonneg (turanSecondLoss_pos (by omega : 0 < K)).le
        (by positivity))).trans
      (variable_detector_propagation_budget hK hKJ hMJ hjPos hjJ heta)
  have htri : ‖P t‖ ≤ ‖P u‖ + ‖P t - P u‖ := by
    calc
      ‖P t‖ = ‖P u + (P t - P u)‖ := by congr 1; ring
      _ ≤ ‖P u‖ + ‖P t - P u‖ := norm_add_le _ _
  have hscale : 0 ≤ turanSecondLoss K M * (2 * eta) ^ j :=
    mul_nonneg (turanSecondLoss_pos (by omega : 0 < K)).le (by positivity)
  have hscaledTri := mul_le_mul_of_nonneg_left htri hscale
  dsimp only [P] at htlarge hscaledTri ⊢
  nlinarith

end

end Erdos48
