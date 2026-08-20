/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos48.GallagherPageEnvelope
import ErdosProblems.Erdos48.VariableLogFreeDensity

/-!
# Constant zero density at Page width

The amplified Gallagher mean is inserted into the variable-order zero
selection.  When `eta = lambda / log (Q * (T + 2))`, every quantity on the
right is bounded by a constant depending only on `lambda`.
-/

open scoped BigOperators

noncomputable section

namespace Erdos48

/-- Constant Page-width density, conditional only on the two explicit
eventual inequalities required by the rough-modulus amplifier. -/
theorem exists_gallagher_pageDensity_of_amplifier
    {lambda : ℝ} (hlambda : 0 < lambda) (hlambdaSmall : lambda ≤ 1 / 16) :
    ∃ K C Cdensity : ℝ, 0 < K ∧ 0 < Cdensity ∧
      ∀ (Q T : ℕ), 2 ≤ Q →
        let b := Q * (T + 2)
        let B := (Q : ℝ) * ((T : ℝ) + 2)
        let eta := lambda / Real.log B
        2 ≤ Real.log b →
        20 * (K + (Real.log (Real.log b) + C + 2) + Real.log 2) ≤
          Real.log b →
        (primitiveHighZeroMass Q eta T : ℝ) ≤ Cdensity := by
  obtain ⟨κ, D, A, K, C, hκ, hD, hA, hK, hraw⟩ :=
    exists_gallagher_rawDensity_globalProduct_parameters
  let E : ℕ := D + κ
  let Hdet : ℕ := variableDetectorHeightDilation E * 2
  let J : ℕ := (D + κ) * Hdet
  let delta : ℝ := variableDetectorPropagationRadius J
  let R : ℝ := variableZeroDetectorTailRadius J
  let L : ℕ := D * Hdet + 1
  let P0 : ℝ := R / lambda + 2
  let P : ℝ := 2 * P0
  let S : ℝ := gallagherPageMeanEnvelope P
  let U : ℝ := gallagherPageEndpointEnvelope R J
  let Gsum : ℝ :=
    ∑ j ∈ Finset.Icc L J,
      (U * lambda ^ 2 +
        2 * normalizedGallagherDerivativeGammaCoefficient (1 / 8) J
          (j - 1) * lambda ^ 3 * P0)
  let Klocal : ℝ := 32 * (Real.log 4 + 4) +
    (256 * (A : ℝ) / 3) * lambda
  let C0 : ℝ :=
    2 * (Klocal * (S * Gsum)) /
      ((delta * lambda) * (1 / 16 : ℝ) ^ 2)
  let Cdensity : ℝ := C0 + 1
  have hJ : 1 ≤ J := by
    dsimp [J, Hdet, E]
    exact Nat.mul_pos (by omega)
      (Nat.mul_pos (variableDetectorHeightDilation_pos (D + κ)) (by norm_num))
  have hdelta : 0 < delta := by
    simpa only [delta] using variableDetectorPropagationRadius_pos hJ
  have hR : 0 < R := by
    simpa only [R] using variableZeroDetectorTailRadius_pos J
  have hP0 : 0 < P0 := by dsimp [P0]; positivity
  have hP : 0 < P := by dsimp [P]; positivity
  have hS : 0 ≤ S := by
    dsimp [S]
    exact gallagherPageMeanEnvelope_nonneg hP.le
  have hU : 0 < U := by dsimp [U, gallagherPageEndpointEnvelope]; positivity
  have hLJ : L ≤ J := by
    dsimp [L, J]
    have hHdet : 1 ≤ Hdet := by
      dsimp [Hdet, E]
      exact Nat.mul_pos (variableDetectorHeightDilation_pos (D + κ)) (by norm_num)
    nlinarith
  have hGsum : 0 ≤ Gsum := by
    dsimp [Gsum]
    apply Finset.sum_nonneg
    intro j hj
    have hgamma : 0 ≤
        normalizedGallagherDerivativeGammaCoefficient (1 / 8) J (j - 1) := by
      unfold normalizedGallagherDerivativeGammaCoefficient
      positivity
    positivity
  have hKlocal : 0 < Klocal := by
    dsimp [Klocal]
    have : 0 < Real.log 4 := Real.log_pos (by norm_num)
    positivity
  have hC0 : 0 ≤ C0 := by dsimp [C0]; positivity
  have hCdensity : 0 < Cdensity := by dsimp [Cdensity]; linarith
  refine ⟨K, C, Cdensity, hK, hCdensity, ?_⟩
  intro Q T hQ
  dsimp only
  intro hlogb hamp
  let b : ℕ := Q * (T + 2)
  let B : ℝ := (Q : ℝ) * ((T : ℝ) + 2)
  let eta : ℝ := lambda / Real.log B
  let N : ℕ := zeroDetectorCutoff R eta
  have hbCast : (b : ℝ) = B := by
    dsimp [b, B]
    push_cast
    ring
  have hb2 : 2 ≤ b := by dsimp [b]; nlinarith
  have hlogB : 0 < Real.log B := by
    rw [← hbCast]
    exact Real.log_pos (by exact_mod_cast (show 1 < b by omega))
  have hlogBone : (1 : ℝ) ≤ Real.log B := by
    rw [← hbCast]
    linarith
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
  have hNlength :
      (((Nat.log 2 (N - 1) + 1 : ℕ) : ℝ)) ≤
        P * Real.log b := by
    have hdyadic := variableDetectorDyadicLength_zeroDetectorCutoff_le
      hR.le heta
    have hdyadic' :
        (((Nat.log 2 (N - 1) + 1 : ℕ) : ℝ)) * Real.log 2 ≤
          R / eta + 2 := by
      simpa only [N, variableDetectorDyadicLength] using hdyadic
    have hright : R / eta + 2 ≤ P0 * Real.log b := by
      rw [show Real.log (b : ℝ) = Real.log B by rw [hbCast]]
      have hEq : R / eta = (R / lambda) * Real.log B := by
        dsimp [eta]
        field_simp
      rw [hEq]
      dsimp [P0]
      nlinarith
    have hprod := hdyadic'.trans hright
    have hlogTwoHalf : (1 / 2 : ℝ) < Real.log 2 :=
      lt_trans (by norm_num) Real.log_two_gt_d9
    have hM0 : 0 ≤ (((Nat.log 2 (N - 1) + 1 : ℕ) : ℝ)) := by positivity
    dsimp [P]
    nlinarith
  have hharm : ∀ j ∈ Finset.Icc L J,
      (∑ m ∈ Finset.Icc (variableDetectorLowerCutoff E eta j) N,
        (m : ℝ)⁻¹) ≤ P0 * Real.log b := by
    intro j hj
    have hjLower : D * Hdet + 1 ≤ j := by
      simpa only [L] using (Finset.mem_Icc.mp hj).1
    have hB : (1 : ℝ) ≤ B := by
      have hQreal : (2 : ℝ) ≤ Q := by exact_mod_cast hQ
      have hT : (2 : ℝ) ≤ (T : ℝ) + 2 := by
        exact_mod_cast (show 2 ≤ T + 2 by omega)
      dsimp [B]
      nlinarith
    have hYcompare : zeroDetectorLowerCutoff B ≤
        variableDetectorLowerCutoff E eta j :=
      zeroDetectorLowerCutoff_le_variableDetectorLowerCutoff
        hD hB heta (by exact le_rfl) (by
          simpa only [Hdet, E, hceil] using le_rfl) (by
            simpa only [Hdet, E, hceil] using hjLower)
    have hY1 : 1 ≤ variableDetectorLowerCutoff E eta j := by
      have hzero : 1 ≤ zeroDetectorLowerCutoff B := by
        unfold zeroDetectorLowerCutoff
        exact Nat.one_le_pow (zeroDetectorLowerLog B) 2 (by omega)
      exact hzero.trans hYcompare
    have hsum := sum_Icc_inv_le_one_add_log (N := N) hY1
    have hlogN := log_zeroDetectorCutoff_le hR.le heta
    have hright : 1 + (R / eta + 1) ≤ P0 * Real.log b := by
      rw [show Real.log (b : ℝ) = Real.log B by rw [hbCast]]
      have hEq : R / eta = (R / lambda) * Real.log B := by
        dsimp [eta]
        field_simp
      rw [hEq]
      dsimp [P0]
      nlinarith
    calc
      _ ≤ 1 + Real.log N := hsum
      _ ≤ 1 + (R / eta + 1) := by linarith
      _ ≤ P0 * Real.log b := hright
  have hpow : ∀ j ∈ Finset.Icc L J,
      b ^ 4 ≤ variableDetectorLowerCutoff E eta j := by
    intro j hj
    have hjLower : D * Hdet + 1 ≤ j := by
      simpa only [L] using (Finset.mem_Icc.mp hj).1
    have hB : (1 : ℝ) ≤ B := by
      have hQreal : (2 : ℝ) ≤ Q := by exact_mod_cast hQ
      have hT : (2 : ℝ) ≤ (T : ℝ) + 2 := by
        exact_mod_cast (show 2 ≤ T + 2 by omega)
      dsimp [B]
      nlinarith
    have hcompare : zeroDetectorLowerCutoff B ≤
        variableDetectorLowerCutoff E eta j :=
      zeroDetectorLowerCutoff_le_variableDetectorLowerCutoff
        hD hB heta (by exact le_rfl) (by
          simpa only [Hdet, E, hceil] using le_rfl) (by
            simpa only [Hdet, E, hceil] using hjLower)
    have hbpow : b ^ 4 ≤ zeroDetectorLowerCutoff B := by
      rw [← hbCast]
      exact pow_four_le_zeroDetectorLowerCutoff b hb2
    exact hbpow.trans hcompare
  have hterm : ∀ j ∈ Finset.Icc L J,
      gallagherRawDensityTermAt Q (T + 1) E N J j
          (Real.log b / 2) eta R ≤
        S * (U * lambda ^ 2 +
          2 * normalizedGallagherDerivativeGammaCoefficient (1 / 8) J
            (j - 1) * lambda ^ 3 * P0) := by
    intro j hj
    apply gallagherRawDensityTermAt_le_page hb2 hlambda heta heta8
      (by dsimp [eta]; rw [hbCast]) hR.le
      (by
        have := (Finset.mem_Icc.mp hj).1
        dsimp [L] at this
        omega)
      (hpow j hj) hP.le hP0.le
      (by simpa only [N, P] using hNlength)
      (by simpa only [N] using hharm j hj)
  have hsum :
      (∑ j ∈ Finset.Icc L J,
        gallagherRawDensityTermAt Q (T + 1) E N J j
          (Real.log b / 2) eta R) ≤ S * Gsum := by
    calc
      _ ≤ ∑ j ∈ Finset.Icc L J,
          S * (U * lambda ^ 2 +
            2 * normalizedGallagherDerivativeGammaCoefficient (1 / 8) J
              (j - 1) * lambda ^ 3 * P0) := Finset.sum_le_sum hterm
      _ = S * Gsum := by
        rw [Finset.mul_sum]
  have hbase := hraw Q T hQ eta heta heta8
  dsimp only at hbase
  have hraw' : (Real.log b / 2) *
      ((primitiveHighZeroMass Q eta T : ℝ) * (delta * eta) *
        (1 / 16 : ℝ) ^ 2) ≤
      Klocal * (S * Gsum) := by
    have h := hbase
      (by simpa only [b] using hlogb)
      (by simpa only [b] using hamp)
    have h' : (Real.log b / 2) *
        ((primitiveHighZeroMass Q eta T : ℝ) * (delta * eta) *
          (1 / 16 : ℝ) ^ 2) ≤
        Klocal *
          ∑ j ∈ Finset.Icc L J,
            gallagherRawDensityTermAt Q (T + 1) E N J j
              (Real.log b / 2) eta R := by
      simpa only [E, B, eta, Hdet, J, delta, R, N, L, Klocal,
        hceil, hceilLambda, hetaLog] using h
    exact h'.trans (mul_le_mul_of_nonneg_left hsum hKlocal.le)
  have hleft : (Real.log b / 2) *
      ((primitiveHighZeroMass Q eta T : ℝ) * (delta * eta) *
        (1 / 16 : ℝ) ^ 2) =
      (primitiveHighZeroMass Q eta T : ℝ) *
        (((delta * lambda) * (1 / 16 : ℝ) ^ 2) / 2) := by
    have hlogNe : Real.log (b : ℝ) ≠ 0 := ne_of_gt (by linarith : 0 < Real.log b)
    dsimp [eta]
    rw [hbCast]
    field_simp [hlogNe]
  rw [hleft] at hraw'
  have hden0 : 0 < (delta * lambda) * (1 / 16 : ℝ) ^ 2 := by positivity
  have hbound : (primitiveHighZeroMass Q eta T : ℝ) ≤ C0 := by
    dsimp [C0]
    apply (le_div_iff₀ hden0).2
    have htw := mul_le_mul_of_nonneg_left hraw' (by norm_num : (0 : ℝ) ≤ 2)
    calc
      (primitiveHighZeroMass Q eta T : ℝ) *
          ((delta * lambda) * (1 / 16 : ℝ) ^ 2) =
        2 * ((primitiveHighZeroMass Q eta T : ℝ) *
          (((delta * lambda) * (1 / 16 : ℝ) ^ 2) / 2)) := by ring
      _ ≤ 2 * (Klocal * (S * Gsum)) := htw
      _ = _ := by ring
  exact hbound.trans (by dsimp [Cdensity]; linarith)

end Erdos48

end
