/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos48.VariableRawLogFreeDensity

/-!
# An order-independent envelope for variable log-free density

The factorial in the normalized detector absorbs the power of the dyadic
logarithmic length.  This file records that cancellation before any choices
of the global parameters are estimated.
-/

namespace Erdos48

open scoped BigOperators

noncomputable section

noncomputable def variableDetectorDyadicLength (N : ℕ) : ℝ :=
  ((Nat.log 2 (N - 1) + 1 : ℕ) : ℝ) * Real.log 2

noncomputable def variableLogFreeDensityEnvelope
    (T N J : ℕ) (eta : ℝ) : ℝ :=
  (578 : ℝ) ^ (2 * J) *
    ((2 * eta * variableDetectorDyadicLength N) *
      Real.exp (2 * eta * variableDetectorDyadicLength N)) ^ 2 *
    ((2 * Real.exp 2 * (1 + 8 * Real.pi)) *
      ((Nat.log 2 (N - 1) + 1 : ℕ) : ℝ) ^ 2)

theorem variableLogFreeDensityEnvelope_nonneg
    (T N J : ℕ) {eta : ℝ} (heta : 0 ≤ eta) :
    0 ≤ variableLogFreeDensityEnvelope T N J eta := by
  unfold variableLogFreeDensityEnvelope variableDetectorDyadicLength
  positivity

private theorem normalized_order_power_le_exp_envelope
    {eta P : ℝ} {J j : ℕ}
    (heta : 0 ≤ eta) (hP : 0 ≤ P) (hj : 1 ≤ j) :
    variableDetectorNormalization eta J j ^ 2 * P ^ (2 * j) ≤
      (578 : ℝ) ^ (2 * J) *
        ((2 * eta * P) * Real.exp (2 * eta * P)) ^ 2 := by
  let x : ℝ := 2 * eta * P
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hfac : (0 : ℝ) < ((j - 1).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos (j - 1)
  have hjSplit : j = (j - 1) + 1 := by omega
  have hseries : x ^ (j - 1) / ((j - 1).factorial : ℝ) ≤
      Real.exp x := Real.pow_div_factorial_le_exp x hx (j - 1)
  have hpow : x ^ j = x * x ^ (j - 1) := by
    conv_lhs => rw [hjSplit]
    rw [pow_succ]
    ring
  have horder : x ^ j / ((j - 1).factorial : ℝ) ≤
      x * Real.exp x := by
    calc
      x ^ j / ((j - 1).factorial : ℝ) =
          x * (x ^ (j - 1) / ((j - 1).factorial : ℝ)) := by
        rw [hpow]
        ring
      _ ≤ x * Real.exp x := mul_le_mul_of_nonneg_left hseries hx
  have horder0 : 0 ≤ x ^ j / ((j - 1).factorial : ℝ) := by positivity
  have hsq :
      (x ^ j / ((j - 1).factorial : ℝ)) ^ 2 ≤
        (x * Real.exp x) ^ 2 :=
    pow_le_pow_left₀ horder0 horder 2
  have h578 : 0 ≤ (578 : ℝ) ^ (2 * J) := by positivity
  calc
    variableDetectorNormalization eta J j ^ 2 * P ^ (2 * j) =
        (((578 : ℝ) ^ J / 2) ^ 2) *
          (x ^ j / ((j - 1).factorial : ℝ)) ^ 2 := by
      dsimp [variableDetectorNormalization, x]
      rw [pow_mul]
      field_simp
      ring
    _ ≤ ((578 : ℝ) ^ J) ^ 2 *
          (x ^ j / ((j - 1).factorial : ℝ)) ^ 2 := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      nlinarith [sq_nonneg ((578 : ℝ) ^ J)]
    _ ≤ ((578 : ℝ) ^ J) ^ 2 * (x * Real.exp x) ^ 2 := by
      exact mul_le_mul_of_nonneg_left hsq (by positivity)
    _ = (578 : ℝ) ^ (2 * J) *
          ((2 * eta * P) * Real.exp (2 * eta * P)) ^ 2 := by
      dsimp [x]
      rw [← pow_mul]
      congr 2
      omega

/-- Every normalized detector order is bounded by one common envelope. -/
theorem variableRawLogFreeDensityTerm_le_envelope
    {T E N J j : ℕ} {eta : ℝ}
    (heta : 0 ≤ eta) (hj : 1 ≤ j)
    (hY : 2 ≤ variableDetectorLowerCutoff E eta j) :
    variableRawLogFreeDensityTerm T E N J j eta ≤
      variableLogFreeDensityEnvelope T N J eta := by
  let M : ℝ := ((Nat.log 2 (N - 1) + 1 : ℕ) : ℝ)
  let P : ℝ := M * Real.log 2
  let C : ℝ := 2 * Real.exp 2 * (1 + 8 * Real.pi)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hbase : (1 : ℝ) ≤
      (variableDetectorLowerCutoff E eta j : ℝ) / 2 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
    exact_mod_cast hY
  have hYpow :
      ((variableDetectorLowerCutoff E eta j : ℝ) / 2) ^ (-(2 * eta)) ≤ 1 := by
    simpa only [Real.rpow_zero] using
      Real.rpow_le_rpow_of_exponent_le hbase (by linarith : -(2 * eta) ≤ 0)
  have hnorm := normalized_order_power_le_exp_envelope
    (J := J) (j := j) heta hP hj
  unfold variableRawLogFreeDensityTerm variableLogFreeDensityEnvelope
  change variableDetectorNormalization eta J j ^ 2 *
      (C * M ^ 2 *
        P ^ (2 * ((j - 1) + 1)) *
          ((variableDetectorLowerCutoff E eta j : ℝ) / 2) ^ (-(2 * eta))) ≤
    (578 : ℝ) ^ (2 * J) *
      ((2 * eta * P) * Real.exp (2 * eta * P)) ^ 2 *
        (C * M ^ 2)
  have hjEq : (j - 1) + 1 = j := by omega
  rw [hjEq]
  have hD : 0 ≤ C * M ^ 2 := by
    positivity
  have hR : 0 ≤ (578 : ℝ) ^ (2 * J) *
      ((2 * eta * P) * Real.exp (2 * eta * P)) ^ 2 := by
    positivity
  have hYnonneg : 0 ≤
      ((variableDetectorLowerCutoff E eta j : ℝ) / 2) ^ (-(2 * eta)) := by
    positivity
  calc
    variableDetectorNormalization eta J j ^ 2 *
        (C * M ^ 2 * P ^ (2 * j) *
          ((variableDetectorLowerCutoff E eta j : ℝ) / 2) ^ (-(2 * eta))) =
      (variableDetectorNormalization eta J j ^ 2 * P ^ (2 * j)) *
        (C * M ^ 2) *
          ((variableDetectorLowerCutoff E eta j : ℝ) / 2) ^ (-(2 * eta)) := by
        ring
    _ ≤ ((578 : ℝ) ^ (2 * J) *
          ((2 * eta * P) * Real.exp (2 * eta * P)) ^ 2) *
        (C * M ^ 2) * 1 := by
      calc
        (variableDetectorNormalization eta J j ^ 2 * P ^ (2 * j)) *
              (C * M ^ 2) *
              ((variableDetectorLowerCutoff E eta j : ℝ) / 2) ^ (-(2 * eta)) ≤
            ((578 : ℝ) ^ (2 * J) *
              ((2 * eta * P) * Real.exp (2 * eta * P)) ^ 2) *
              (C * M ^ 2) *
              ((variableDetectorLowerCutoff E eta j : ℝ) / 2) ^ (-(2 * eta)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hnorm hD) hYnonneg
        _ ≤ _ := mul_le_mul_of_nonneg_left hYpow (mul_nonneg hR hD)
    _ = _ := by ring

/-- Summing over the possible orders costs at most `J+1` copies of the
common envelope. -/
theorem sum_variableRawLogFreeDensityTerm_le_envelope
    {T E N L J : ℕ} {eta : ℝ}
    (heta : 0 ≤ eta)
    (hY : ∀ j ∈ Finset.Icc L J,
      2 ≤ variableDetectorLowerCutoff E eta j)
    (hL : 1 ≤ L) :
    (∑ j ∈ Finset.Icc L J,
        variableRawLogFreeDensityTerm T E N J j eta) ≤
      ((J + 1 : ℕ) : ℝ) *
        variableLogFreeDensityEnvelope T N J eta := by
  calc
    (∑ j ∈ Finset.Icc L J,
        variableRawLogFreeDensityTerm T E N J j eta) ≤
      ∑ _j ∈ Finset.Icc L J,
        variableLogFreeDensityEnvelope T N J eta := by
      apply Finset.sum_le_sum
      intro j hj
      exact variableRawLogFreeDensityTerm_le_envelope heta
        (hL.trans (Finset.mem_Icc.mp hj).1) (hY j hj)
    _ = ((Finset.Icc L J).card : ℝ) *
        variableLogFreeDensityEnvelope T N J eta := by simp
    _ ≤ ((J + 1 : ℕ) : ℝ) *
        variableLogFreeDensityEnvelope T N J eta := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast (show (Finset.Icc L J).card ≤ J + 1 by
          rw [Nat.card_Icc]
          omega)
      · exact variableLogFreeDensityEnvelope_nonneg T N J heta

/-- The variable-order detector estimate with the finite order sum removed
and the positive propagation factor divided out.  All parameters are kept
explicit so that the subsequent elementary estimates can be proved without
reopening the analytic detector argument. -/
theorem exists_variable_logFreeDensity_envelope_parameters :
    ∃ κ D A : ℕ, 1 ≤ κ ∧ 1 ≤ D ∧ 37 ≤ A ∧
      ∀ (Q T : ℕ), 2 ≤ Q →
        ∀ eta : ℝ, 0 < eta → eta ≤ 1 / 8 →
          let E := D + κ
          let B := (Q : ℝ) * ((T : ℝ) + 2)
          let H₀ := Nat.ceil (1 + eta * Real.log B)
          let H := variableDetectorHeightDilation E * H₀
          let J := (D + κ) * H
          let delta := variableDetectorPropagationRadius J
          let R := variableZeroDetectorTailRadius J
          let N := zeroDetectorCutoff R eta
          let Klocal := 32 * (Real.log 4 + 4) +
            (256 * (A : ℝ) / 3) * (eta * Real.log B)
          (primitiveHighZeroMass Q eta T : ℝ) ≤
            (Klocal * ((J + 1 : ℕ) : ℝ) *
                variableLogFreeDensityEnvelope T N J eta) /
              ((delta * eta) * (1 / 16 : ℝ) ^ 2) := by
  obtain ⟨κ, D, A, hκ, hD, hA, hraw⟩ :=
    exists_variable_raw_logFreeDensity_parameters
  refine ⟨κ, D, A, hκ, hD, hA, ?_⟩
  intro Q T hQ eta heta heta8
  dsimp only
  let E := D + κ
  let B : ℝ := (Q : ℝ) * ((T : ℝ) + 2)
  let H₀ : ℕ := Nat.ceil (1 + eta * Real.log B)
  let H : ℕ := variableDetectorHeightDilation E * H₀
  let J : ℕ := (D + κ) * H
  let delta : ℝ := variableDetectorPropagationRadius J
  let R : ℝ := variableZeroDetectorTailRadius J
  let N : ℕ := zeroDetectorCutoff R eta
  let L : ℕ := D * H + 1
  let Klocal : ℝ := 32 * (Real.log 4 + 4) +
    (256 * (A : ℝ) / 3) * (eta * Real.log B)
  have hB : (1 : ℝ) ≤ B := by
    dsimp [B]
    have hQR : (2 : ℝ) ≤ Q := by exact_mod_cast hQ
    have hT0 : (0 : ℝ) ≤ T := by positivity
    nlinarith
  have hH₀pos : 1 ≤ H₀ := by
    have harg : (1 : ℝ) ≤ 1 + eta * Real.log B := by
      have hlog : 0 ≤ Real.log B := Real.log_nonneg hB
      nlinarith [mul_nonneg heta.le hlog]
    have hcast : (1 : ℝ) ≤ (H₀ : ℕ) := by
      exact harg.trans (by
        simpa only [H₀] using Nat.le_ceil (1 + eta * Real.log B))
    exact_mod_cast hcast
  have hHpos : 1 ≤ H := by
    dsimp [H]
    exact Nat.mul_pos (variableDetectorHeightDilation_pos E) (by omega)
  have hJpos : 1 ≤ J := by
    dsimp [J]
    exact Nat.mul_pos (by omega) (by omega)
  have hdelta : 0 < delta := by
    simpa only [delta] using variableDetectorPropagationRadius_pos hJpos
  have hden : 0 < (delta * eta) * (1 / 16 : ℝ) ^ 2 := by
    positivity
  have hraw' := hraw Q T hQ eta heta heta8
  have hY : ∀ j ∈ Finset.Icc L J,
      2 ≤ variableDetectorLowerCutoff E eta j := by
    intro j hj
    have hjLower : D * H + 1 ≤ j := by
      simpa only [L] using (Finset.mem_Icc.mp hj).1
    have hcompare : zeroDetectorLowerCutoff B ≤
        variableDetectorLowerCutoff E eta j :=
      zeroDetectorLowerCutoff_le_variableDetectorLowerCutoff
        hD hB heta (by exact le_rfl) (by exact le_rfl) hjLower
    have htwo : 2 ≤ zeroDetectorLowerCutoff B := by
      unfold zeroDetectorLowerCutoff
      have hlarge : 1 ≤ zeroDetectorLowerLog B := by
        unfold zeroDetectorLowerLog
        have hBtwo : (2 : ℝ) ≤ B := by
          dsimp [B]
          have hQR : (2 : ℝ) ≤ Q := by exact_mod_cast hQ
          have hTtwo : (2 : ℝ) ≤ (T : ℝ) + 2 := by
            exact_mod_cast (show 2 ≤ T + 2 by omega)
          nlinarith
        have hlogLower : Real.log 2 ≤ Real.log B :=
          Real.log_le_log (by norm_num) hBtwo
        have hlogTwoHalf : (1 / 2 : ℝ) < Real.log 2 :=
          lt_trans (by norm_num) Real.log_two_gt_d9
        have hone : (1 : ℝ) ≤ 8 * Real.log B := by nlinarith
        exact Nat.le_floor (show ((1 : ℕ) : ℝ) ≤ 8 * Real.log B by
          simpa using hone)
      simpa only [pow_one] using
        (Nat.pow_le_pow_right (by norm_num : 0 < 2) hlarge)
    exact htwo.trans hcompare
  have hsum := sum_variableRawLogFreeDensityTerm_le_envelope
    (T := T) (E := E) (N := N) (L := L) (J := J)
      heta.le hY (by dsimp [L]; omega)
  have hKlocal : 0 ≤ Klocal := by
    dsimp [Klocal]
    have hlog : 0 ≤ Real.log B := Real.log_nonneg hB
    positivity
  have hcombined :
      (primitiveHighZeroMass Q eta T : ℝ) *
          ((delta * eta) * (1 / 16 : ℝ) ^ 2) ≤
        Klocal * (((J + 1 : ℕ) : ℝ) *
          variableLogFreeDensityEnvelope T N J eta) := by
    calc
      (primitiveHighZeroMass Q eta T : ℝ) *
          ((delta * eta) * (1 / 16 : ℝ) ^ 2) =
          (primitiveHighZeroMass Q eta T : ℝ) *
            (delta * eta) * (1 / 16 : ℝ) ^ 2 := by ring
      _ ≤ Klocal *
          ∑ j ∈ Finset.Icc L J,
            variableRawLogFreeDensityTerm T E N J j eta := by
        simpa only [E, B, H₀, H, J, delta, R, N, L, Klocal] using hraw'
      _ ≤ Klocal * (((J + 1 : ℕ) : ℝ) *
          variableLogFreeDensityEnvelope T N J eta) :=
        mul_le_mul_of_nonneg_left hsum hKlocal
  apply (le_div_iff₀ hden).2
  simpa only [mul_assoc] using hcombined

end

end Erdos48
