/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos48.LogFreeDensity

/-!
# A uniform envelope for the log-free density estimate

The detector theorem naturally leaves a finite sum over its possible
derivative orders.  This file bounds every member of that sum by one common
positive expression.  Keeping this purely finite reduction separate makes
the later explicit-formula summation independent of the implementation of
the Turan detector.
-/

namespace Erdos48

open scoped BigOperators

noncomputable section

/-- The common upper envelope for one derivative order in the detector
density estimate. -/
noncomputable def logFreeDensityEnvelope
    (T N Y J : ℕ) (eta : ℝ) : ℝ :=
  (2 * Real.exp 2 * (1 + 8 * Real.pi)) *
    (((T + 1) + 1 : ℕ) : ℝ) *
    ((Nat.log 2 (N - 1) + 1 : ℕ) : ℝ) ^ 2 *
    (max 1
      (((Nat.log 2 (N - 1) + 1 : ℕ) : ℝ) * Real.log 2) ^ (2 * J)) *
    (((Y : ℝ) / 2) ^ (-(2 * eta)))

theorem logFreeDensityEnvelope_nonneg
    (T N Y J : ℕ) (eta : ℝ) :
    0 ≤ logFreeDensityEnvelope T N Y J eta := by
  unfold logFreeDensityEnvelope
  positivity

/-- Every order in the fixed detector interval is bounded by the uniform
envelope. -/
theorem logFreeDensity_order_term_le_envelope
    {L J T N Y j : ℕ} (hL : 1 ≤ L)
    (hj : j ∈ Finset.Icc L J) (eta : ℝ) :
    (2 * Real.exp 2 * (1 + 8 * Real.pi)) *
        (((T + 1) + 1 : ℕ) : ℝ) *
        ((Nat.log 2 (N - 1) + 1 : ℕ) : ℝ) ^ 2 *
        ((((Nat.log 2 (N - 1) + 1 : ℕ) : ℝ) * Real.log 2) ^
          (2 * ((j - 1) + 1))) *
        (((Y : ℝ) / 2) ^ (-(2 * eta))) ≤
      logFreeDensityEnvelope T N Y J eta := by
  let P : ℝ :=
    ((Nat.log 2 (N - 1) + 1 : ℕ) : ℝ) * Real.log 2
  let W : ℝ := max 1 P
  have hjJ : j ≤ J := (Finset.mem_Icc.mp hj).2
  have hP : 0 ≤ P := by
    dsimp [P]
    positivity
  have hPW : P ≤ W := by
    exact le_max_right 1 P
  have hW : 1 ≤ W := le_max_left 1 P
  have hpowBase : P ^ (2 * j) ≤ W ^ (2 * j) := by
    exact pow_le_pow_left₀ hP hPW _
  have hpowExponent : W ^ (2 * j) ≤ W ^ (2 * J) := by
    exact pow_le_pow_right₀ hW (Nat.mul_le_mul_left 2 hjJ)
  have hpow : P ^ (2 * ((j - 1) + 1)) ≤ W ^ (2 * J) := by
    have hjPos : 1 ≤ j := by
      have hLJ := (Finset.mem_Icc.mp hj).1
      omega
    rw [show (j - 1) + 1 = j by omega]
    exact hpowBase.trans hpowExponent
  unfold logFreeDensityEnvelope
  dsimp only [P, W] at hpow
  gcongr

/-- The finite order sum costs at most `J+1` copies of the common envelope.
The deliberately loose cardinal factor avoids carrying endpoint arithmetic
into later analytic estimates. -/
theorem sum_logFreeDensity_order_terms_le_envelope
    {L J T N Y : ℕ} (hL : 1 ≤ L) (eta : ℝ) :
    (∑ j ∈ Finset.Icc L J,
        (2 * Real.exp 2 * (1 + 8 * Real.pi)) *
          (((T + 1) + 1 : ℕ) : ℝ) *
          ((Nat.log 2 (N - 1) + 1 : ℕ) : ℝ) ^ 2 *
          ((((Nat.log 2 (N - 1) + 1 : ℕ) : ℝ) * Real.log 2) ^
            (2 * ((j - 1) + 1))) *
          (((Y : ℝ) / 2) ^ (-(2 * eta)))) ≤
      ((J + 1 : ℕ) : ℝ) * logFreeDensityEnvelope T N Y J eta := by
  calc
    (∑ j ∈ Finset.Icc L J,
        (2 * Real.exp 2 * (1 + 8 * Real.pi)) *
          (((T + 1) + 1 : ℕ) : ℝ) *
          ((Nat.log 2 (N - 1) + 1 : ℕ) : ℝ) ^ 2 *
          ((((Nat.log 2 (N - 1) + 1 : ℕ) : ℝ) * Real.log 2) ^
            (2 * ((j - 1) + 1))) *
          (((Y : ℝ) / 2) ^ (-(2 * eta)))) ≤
        ∑ _j ∈ Finset.Icc L J,
          logFreeDensityEnvelope T N Y J eta := by
      exact Finset.sum_le_sum fun j hj ↦
        logFreeDensity_order_term_le_envelope hL hj eta
    _ = ((Finset.Icc L J).card : ℝ) *
        logFreeDensityEnvelope T N Y J eta := by simp
    _ ≤ ((J + 1 : ℕ) : ℝ) *
        logFreeDensityEnvelope T N Y J eta := by
      apply mul_le_mul_of_nonneg_right _
        (logFreeDensityEnvelope_nonneg T N Y J eta)
      exact_mod_cast (show (Finset.Icc L J).card ≤ J + 1 by
        rw [Nat.card_Icc]
        omega)

/-- Log-free density with the detector-order sum replaced by its common
envelope. -/
theorem exists_logFreeDensity_envelope_parameters :
    ∃ L J : ℕ, 2 ≤ L ∧ L ≤ J ∧
      ∃ lambda R delta eta₀ : ℝ,
        0 < lambda ∧ 0 < R ∧ 0 < delta ∧ delta ≤ 1 ∧
        0 < eta₀ ∧ eta₀ ≤ 1 / 8 ∧
        ∃ A : ℕ, 37 ≤ A ∧
        ∀ (Q T : ℕ), 2 ≤ Q →
          ∀ eta : ℝ, 0 < eta → eta ≤ eta₀ →
          eta * Real.log ((Q : ℝ) * ((T : ℝ) + 2)) ≤ lambda →
          let Y := zeroDetectorLowerCutoff
            ((Q : ℝ) * ((T : ℝ) + 2))
          let N := zeroDetectorCutoff R eta
          (primitiveHighZeroMass Q eta T : ℝ) *
              (delta * eta) * (1 / 96 : ℝ) ^ 2 ≤
            (32 * (Real.log 4 + 4) +
                (256 * (A : ℝ) / 3) * lambda) *
              ((J + 1 : ℕ) : ℝ) *
                logFreeDensityEnvelope T N Y J eta := by
  obtain ⟨L, J, hL2, hLJ, lambda, R, delta, eta₀,
      hlambda, hR, hdelta, hdelta1, heta₀, heta₀8,
      A, hA, hdensity⟩ := exists_logFreeDensity_parameters
  refine ⟨L, J, hL2, hLJ, lambda, R, delta, eta₀,
    hlambda, hR, hdelta, hdelta1, heta₀, heta₀8, A, hA, ?_⟩
  intro Q T hQ eta heta hetaSmall hglobal
  dsimp only
  let Y := zeroDetectorLowerCutoff ((Q : ℝ) * ((T : ℝ) + 2))
  let N := zeroDetectorCutoff R eta
  let C : ℝ := 32 * (Real.log 4 + 4) +
    (256 * (A : ℝ) / 3) * lambda
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have hraw := hdensity Q T hQ eta heta hetaSmall hglobal
  have hsum := sum_logFreeDensity_order_terms_le_envelope
    (L := L) (J := J) (T := T) (N := N) (Y := Y)
      (by omega) eta
  calc
    (primitiveHighZeroMass Q eta T : ℝ) *
        (delta * eta) * (1 / 96 : ℝ) ^ 2 ≤
      C *
        ∑ j ∈ Finset.Icc L J,
          (2 * Real.exp 2 * (1 + 8 * Real.pi)) *
            (((T + 1) + 1 : ℕ) : ℝ) *
            ((Nat.log 2 (N - 1) + 1 : ℕ) : ℝ) ^ 2 *
            ((((Nat.log 2 (N - 1) + 1 : ℕ) : ℝ) * Real.log 2) ^
              (2 * ((j - 1) + 1))) *
            (((Y : ℝ) / 2) ^ (-(2 * eta))) := by
      simpa only [C, Y, N] using hraw
    _ ≤ C * (((J + 1 : ℕ) : ℝ) *
        logFreeDensityEnvelope T N Y J eta) :=
      mul_le_mul_of_nonneg_left hsum hC
    _ = C * ((J + 1 : ℕ) : ℝ) *
        logFreeDensityEnvelope T N Y J eta := by ring

end

end Erdos48
