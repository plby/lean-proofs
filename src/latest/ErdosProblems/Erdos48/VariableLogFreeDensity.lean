/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos48.VariableLogFreeDensityEnvelope

/-!
# A usable variable-order log-free density estimate

The detector envelope is especially simple at the logarithmic scale
`eta = lambda / log (Q * (T + 2))`.  The product `eta * log B` is then the
fixed number `lambda`, so the detector order is independent of `Q` and `T`.
This file records the elementary estimates which turn the raw envelope into
a polynomial in `log B`.
-/

namespace Erdos48

open scoped BigOperators

noncomputable section

/-- The dyadic logarithmic length of the exponential detector cutoff is at
most its defining real logarithmic length, up to an absolute additive
constant. -/
theorem variableDetectorDyadicLength_zeroDetectorCutoff_le
    {R eta : ℝ} (hR : 0 ≤ R) (heta : 0 < eta) :
    variableDetectorDyadicLength (zeroDetectorCutoff R eta) ≤
      R / eta + 2 := by
  let N : ℕ := zeroDetectorCutoff R eta
  have hquot : 0 ≤ R / eta := div_nonneg hR heta.le
  have hexpOne : (1 : ℝ) ≤ Real.exp (R / eta) := by
    simpa only [Real.exp_zero] using Real.exp_le_exp.mpr hquot
  have hNpos : 0 < N := by
    dsimp [N]
    exact zeroDetectorCutoff_pos R eta
  have hlogTwoPos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogTwoLeOne : Real.log 2 ≤ 1 :=
    Real.log_two_lt_d9.le.trans (by norm_num)
  change (((Nat.log 2 (N - 1) + 1 : ℕ) : ℝ) * Real.log 2) ≤
    R / eta + 2
  by_cases hpred : N - 1 = 0
  · simp [hpred]
    linarith
  · have hpow : 2 ^ Nat.log 2 (N - 1) ≤ N - 1 :=
      Nat.pow_log_le_self 2 hpred
    have hpowReal : (2 : ℝ) ^ Nat.log 2 (N - 1) ≤ (N - 1 : ℕ) := by
      exact_mod_cast hpow
    have hlogPow :
        Real.log ((2 : ℝ) ^ Nat.log 2 (N - 1)) ≤
          Real.log ((N - 1 : ℕ) : ℝ) :=
      Real.log_le_log (by positivity) hpowReal
    have hnatLog :
        (Nat.log 2 (N - 1) : ℝ) * Real.log 2 ≤
          Real.log ((N - 1 : ℕ) : ℝ) := by
      simpa only [Real.log_pow] using hlogPow
    have hpredLe : ((N - 1 : ℕ) : ℝ) ≤ (N : ℝ) := by
      exact_mod_cast Nat.sub_le N 1
    have hlogPredN : Real.log ((N - 1 : ℕ) : ℝ) ≤ Real.log (N : ℝ) :=
      Real.log_le_log (by positivity) hpredLe
    have hNlt : (N : ℝ) < Real.exp (R / eta) + 1 := by
      dsimp [N, zeroDetectorCutoff]
      exact_mod_cast Nat.ceil_lt_add_one (Real.exp_pos (R / eta)).le
    have hsumLe : Real.exp (R / eta) + 1 ≤
        2 * Real.exp (R / eta) := by nlinarith
    have hlogN : Real.log (N : ℝ) ≤ R / eta + 1 := by
      have hNtwoExp : (N : ℝ) ≤ 2 * Real.exp (R / eta) :=
        hNlt.le.trans hsumLe
      have hlog := Real.log_le_log (by positivity) hNtwoExp
      calc
        Real.log (N : ℝ) ≤ Real.log (2 * Real.exp (R / eta)) := hlog
        _ = Real.log 2 + R / eta := by
          rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
            (Real.exp_ne_zero (R / eta)), Real.log_exp]
        _ ≤ R / eta + 1 := by linarith
    push_cast
    rw [add_mul]
    calc
      (Nat.log 2 (N - 1) : ℝ) * Real.log 2 + 1 * Real.log 2 ≤
          Real.log (N : ℝ) + 1 := add_le_add
            (hnatLog.trans hlogPredN) (by simpa using hlogTwoLeOne)
      _ ≤ R / eta + 2 := by linarith

/-- Log-free density at the Page scale.  For fixed positive `lambda`, the
number of primitive zeros in the rectangle `re rho ≥ 1 - lambda / log B`
is bounded polynomially in `log B`. -/
theorem exists_variable_logFreeDensity_logarithmic_bound
    {lambda : ℝ} (hlambda : 0 < lambda) (hlambdaSmall : lambda ≤ 1 / 16) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (Q T : ℕ), 2 ≤ Q → 2 ≤ T →
        let B := (Q : ℝ) * ((T : ℝ) + 2)
        let eta := lambda / Real.log B
        (primitiveHighZeroMass Q eta T : ℝ) ≤
          C * Real.log B ^ 3 := by
  obtain ⟨κ, D, A, hκ, hD, hA, hdensity⟩ :=
    exists_variable_logFreeDensity_envelope_parameters
  let E : ℕ := D + κ
  let H : ℕ := variableDetectorHeightDilation E * 2
  let J : ℕ := (D + κ) * H
  let delta : ℝ := variableDetectorPropagationRadius J
  let R : ℝ := variableZeroDetectorTailRadius J
  let P₀ : ℝ := R / lambda + 2
  let U : ℝ := 2 * lambda * P₀
  let K₀ : ℝ := 32 * (Real.log 4 + 4) +
    (256 * (A : ℝ) / 3) * lambda
  let Cenv : ℝ :=
    (578 : ℝ) ^ (2 * J) * (U * Real.exp U) ^ 2 *
      ((2 * Real.exp 2 * (1 + 8 * Real.pi)) * (2 * P₀) ^ 2)
  let C : ℝ := 256 * (K₀ * ((J + 1 : ℕ) : ℝ) * Cenv) /
    (delta * lambda)
  have hJ : 1 ≤ J := by
    dsimp [J, H, E]
    exact Nat.mul_pos (by omega)
      (Nat.mul_pos (variableDetectorHeightDilation_pos (D + κ)) (by norm_num))
  have hdelta : 0 < delta := by
    simpa only [delta] using variableDetectorPropagationRadius_pos hJ
  have hR : 0 < R := by
    simpa only [R] using variableZeroDetectorTailRadius_pos J
  have hP₀ : 0 < P₀ := by dsimp [P₀]; positivity
  have hU : 0 < U := by dsimp [U]; positivity
  have hK₀ : 0 < K₀ := by
    dsimp [K₀]
    have hlogFour : 0 < Real.log 4 := Real.log_pos (by norm_num)
    positivity
  have hCenv : 0 < Cenv := by
    dsimp [Cenv]
    positivity
  have hC : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro Q T hQ hT
  dsimp only
  let B : ℝ := (Q : ℝ) * ((T : ℝ) + 2)
  let eta : ℝ := lambda / Real.log B
  let N : ℕ := zeroDetectorCutoff R eta
  have hB8 : (8 : ℝ) ≤ B := by
    dsimp [B]
    have hQR : (2 : ℝ) ≤ Q := by exact_mod_cast hQ
    have hTR : (2 : ℝ) ≤ T := by exact_mod_cast hT
    nlinarith
  have hlogB : 0 < Real.log B :=
    Real.log_pos (lt_of_lt_of_le (by norm_num : (1 : ℝ) < 8) hB8)
  have hlogBone : (1 : ℝ) ≤ Real.log B := by
    have hlog8 : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
      norm_num
    have hlogMono : Real.log 8 ≤ Real.log B :=
      Real.log_le_log (by norm_num) hB8
    nlinarith [Real.log_two_gt_d9]
  have heta : 0 < eta := by dsimp [eta]; positivity
  have hetaLog : eta * Real.log B = lambda := by
    dsimp [eta]
    field_simp
  have heta8 : eta ≤ 1 / 8 := by
    have hetaLe : eta ≤ lambda := by
      dsimp [eta]
      rw [div_le_iff₀ hlogB]
      nlinarith
    linarith
  have hceilLambda : Nat.ceil (1 + lambda) = 2 := by
    exact (Nat.ceil_eq_iff (by norm_num : (2 : ℕ) ≠ 0)).2
      ⟨by push_cast; linarith, by push_cast; linarith⟩
  have hceil : Nat.ceil (1 + eta * Real.log B) = 2 := by
    rw [hetaLog]
    exact hceilLambda
  have hP : variableDetectorDyadicLength N ≤ P₀ * Real.log B := by
    have hcut := variableDetectorDyadicLength_zeroDetectorCutoff_le
      hR.le heta
    have hcut' : variableDetectorDyadicLength N ≤ R / eta + 2 := by
      simpa only [N] using hcut
    calc
      variableDetectorDyadicLength N ≤ R / eta + 2 := hcut'
      _ = (R / lambda) * Real.log B + 2 := by
        dsimp [eta]
        field_simp
      _ ≤ (R / lambda + 2) * Real.log B := by
        nlinarith
      _ = P₀ * Real.log B := rfl
  have hM : (((Nat.log 2 (N - 1) + 1 : ℕ) : ℝ)) ≤
      2 * P₀ * Real.log B := by
    have hlogTwoHalf : (1 / 2 : ℝ) < Real.log 2 :=
      lt_trans (by norm_num) Real.log_two_gt_d9
    have hMnonneg : (0 : ℝ) ≤ ((Nat.log 2 (N - 1) + 1 : ℕ) : ℝ) := by
      positivity
    have hlength :
        (((Nat.log 2 (N - 1) + 1 : ℕ) : ℝ)) * Real.log 2 ≤
          P₀ * Real.log B := by
      simpa only [variableDetectorDyadicLength] using hP
    nlinarith
  have hetaP : 2 * eta * variableDetectorDyadicLength N ≤ U := by
    have hmul := mul_le_mul_of_nonneg_left hP
      (by positivity : 0 ≤ 2 * eta)
    calc
      2 * eta * variableDetectorDyadicLength N ≤
          2 * eta * (P₀ * Real.log B) := by
        simpa only [mul_assoc] using hmul
      _ = 2 * P₀ * (eta * Real.log B) := by ring
      _ = 2 * lambda * P₀ := by rw [hetaLog]; ring
      _ = U := rfl
  have hetaP0 : 0 ≤ 2 * eta * variableDetectorDyadicLength N := by
    unfold variableDetectorDyadicLength
    positivity
  have hdetectorFactor :
      ((2 * eta * variableDetectorDyadicLength N) *
          Real.exp (2 * eta * variableDetectorDyadicLength N)) ^ 2 ≤
        (U * Real.exp U) ^ 2 := by
    apply pow_le_pow_left₀ (mul_nonneg hetaP0 (Real.exp_pos _).le)
    exact mul_le_mul hetaP (Real.exp_le_exp.mpr hetaP)
      (Real.exp_pos _).le hU.le
  have henvelope : variableLogFreeDensityEnvelope T N J eta ≤
      Cenv * Real.log B ^ 2 := by
    unfold variableLogFreeDensityEnvelope
    have hMpow :
        (((Nat.log 2 (N - 1) + 1 : ℕ) : ℝ)) ^ 2 ≤
          (2 * P₀ * Real.log B) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hM 2
    calc
      (578 : ℝ) ^ (2 * J) *
          ((2 * eta * variableDetectorDyadicLength N) *
            Real.exp (2 * eta * variableDetectorDyadicLength N)) ^ 2 *
          ((2 * Real.exp 2 * (1 + 8 * Real.pi)) *
            ((Nat.log 2 (N - 1) + 1 : ℕ) : ℝ) ^ 2) ≤
        (578 : ℝ) ^ (2 * J) * (U * Real.exp U) ^ 2 *
          ((2 * Real.exp 2 * (1 + 8 * Real.pi)) *
            (2 * P₀ * Real.log B) ^ 2) := by
        gcongr
      _ = Cenv * Real.log B ^ 2 := by
        dsimp [Cenv]
        ring
  have hbase := hdensity Q T hQ eta heta heta8
  dsimp only at hbase
  have hbase' : (primitiveHighZeroMass Q eta T : ℝ) ≤
      (K₀ * ((J + 1 : ℕ) : ℝ) *
          variableLogFreeDensityEnvelope T N J eta) /
        ((delta * eta) * (1 / 16 : ℝ) ^ 2) := by
    simpa only [E, B, eta, H, J, delta, R, N, hceil, K₀,
      hceilLambda, hetaLog] using hbase
  calc
    (primitiveHighZeroMass Q eta T : ℝ) ≤
        (K₀ * ((J + 1 : ℕ) : ℝ) *
          variableLogFreeDensityEnvelope T N J eta) /
            ((delta * eta) * (1 / 16 : ℝ) ^ 2) := hbase'
    _ ≤ (K₀ * ((J + 1 : ℕ) : ℝ) *
          (Cenv * Real.log B ^ 2)) /
            ((delta * eta) * (1 / 16 : ℝ) ^ 2) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left henvelope (by positivity)
    _ = C * Real.log B ^ 3 := by
      dsimp [C, eta]
      field_simp
      ring

end

end Erdos48
