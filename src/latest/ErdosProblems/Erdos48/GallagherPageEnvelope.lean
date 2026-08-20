/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos48.GallagherTailBound
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# The Gallagher mean at the Page scale

This file records the elementary estimates which make the amplified
Gallagher mean uniform when `eta * log B` is fixed.  In particular, the
terminal Abel term retains two powers of `eta`, while the differentiated
term retains three.
-/

open scoped BigOperators

noncomputable section

namespace Erdos48

/-- The logarithm of the integral exponential cutoff is at most its defining
real logarithmic length, up to one. -/
theorem log_zeroDetectorCutoff_le
    {R eta : ℝ} (hR : 0 ≤ R) (heta : 0 < eta) :
    Real.log (zeroDetectorCutoff R eta : ℝ) ≤ R / eta + 1 := by
  have hquot : 0 ≤ R / eta := div_nonneg hR heta.le
  have hexpOne : (1 : ℝ) ≤ Real.exp (R / eta) := by
    simpa only [Real.exp_zero] using Real.exp_le_exp.mpr hquot
  have hNlt : (zeroDetectorCutoff R eta : ℝ) <
      Real.exp (R / eta) + 1 := by
    unfold zeroDetectorCutoff
    exact_mod_cast Nat.ceil_lt_add_one (Real.exp_pos (R / eta)).le
  have hsumLe : Real.exp (R / eta) + 1 ≤
      2 * Real.exp (R / eta) := by nlinarith
  have hNtwoExp : (zeroDetectorCutoff R eta : ℝ) ≤
      2 * Real.exp (R / eta) := hNlt.le.trans hsumLe
  have hlog := Real.log_le_log (by
    exact_mod_cast zeroDetectorCutoff_pos R eta) hNtwoExp
  calc
    Real.log (zeroDetectorCutoff R eta : ℝ) ≤
        Real.log (2 * Real.exp (R / eta)) := hlog
    _ = Real.log 2 + R / eta := by
      rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
        (Real.exp_ne_zero (R / eta)), Real.log_exp]
    _ ≤ R / eta + 1 := by
      nlinarith [Real.log_two_lt_d9]

/-- A cutoff logarithm is nonnegative. -/
theorem zeroDetectorCutoff_log_nonneg (R eta : ℝ) :
    0 ≤ Real.log (zeroDetectorCutoff R eta : ℝ) := by
  apply Real.log_nonneg
  exact_mod_cast zeroDetectorCutoff_pos R eta

/-- The terminal Gallagher weight, after detector normalization, has the
two powers of `eta` needed at Page width. -/
theorem normalizedGallagherEndpointCoefficient_le
    {eta R : ℝ} (heta : 0 < eta) (heta8 : eta ≤ 1 / 8)
    (hR : 0 ≤ R) (J j : ℕ) (hj : 1 ≤ j) :
    variableDetectorNormalization eta J j ^ 2 *
        (2 * |gallagherWeight eta (j - 1)
          (zeroDetectorCutoff R eta)| ^ 2) ≤
      2 * (578 : ℝ) ^ (2 * J) * eta ^ 2 * Real.exp (4 * R + 1) := by
  let N : ℕ := zeroDetectorCutoff R eta
  let P : ℝ := Real.log (N : ℝ)
  let x : ℝ := 2 * eta * P
  let F : ℝ := (((j - 1).factorial : ℕ) : ℝ)
  have hNpos : 0 < N := by dsimp [N]; exact zeroDetectorCutoff_pos R eta
  have hNone : (1 : ℝ) ≤ N := by exact_mod_cast hNpos
  have hP : 0 ≤ P := by dsimp [P, N]; exact zeroDetectorCutoff_log_nonneg R eta
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hF : 0 < F := by dsimp [F]; positivity
  have hjEq : j = (j - 1) + 1 := by omega
  have hseries : x ^ (j - 1) / F ≤ Real.exp x := by
    simpa only [F] using Real.pow_div_factorial_le_exp x hx (j - 1)
  have hseries0 : 0 ≤ x ^ (j - 1) / F := by positivity
  have hseriesSq : (x ^ (j - 1) / F) ^ 2 ≤ Real.exp x ^ 2 :=
    pow_le_pow_left₀ hseries0 hseries 2
  have hrpow : (N : ℝ) ^ (-eta) ≤ 1 := by
    simpa only [Real.rpow_zero] using
      Real.rpow_le_rpow_of_exponent_le hNone (by linarith : -eta ≤ 0)
  have hrpow0 : 0 ≤ (N : ℝ) ^ (-eta) :=
    Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hrpowSq : ((N : ℝ) ^ (-eta)) ^ 2 ≤ 1 := by nlinarith
  have hlog : P ≤ R / eta + 1 := by
    simpa only [P, N] using log_zeroDetectorCutoff_le hR heta
  have hxUpper : x ≤ 2 * R + 1 / 4 := by
    have hmul := mul_le_mul_of_nonneg_left hlog (by positivity : 0 ≤ 2 * eta)
    dsimp [x] at hmul ⊢
    have hetaQuarter : 2 * eta ≤ 1 / 4 := by linarith
    calc
      2 * eta * P ≤ 2 * eta * (R / eta + 1) := hmul
      _ = 2 * R + 2 * eta := by field_simp
      _ ≤ 2 * R + 1 / 4 := by linarith
  have hexp : Real.exp x ^ 2 ≤ Real.exp (4 * R + 1) := by
    rw [pow_two, ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  have hweight :
      |gallagherWeight eta (j - 1) N| ^ 2 =
        P ^ (2 * (j - 1)) * ((N : ℝ) ^ (-eta)) ^ 2 := by
    unfold gallagherWeight
    rw [abs_of_nonneg (mul_nonneg (by positivity) hrpow0), mul_pow, ← pow_mul]
    congr 2
    omega
  rw [hweight]
  have hPpow : P ^ (2 * (j - 1)) = (P ^ (j - 1)) ^ 2 := by
    rw [← pow_mul]
    congr 1
    omega
  have hxpow : x ^ (j - 1) =
      (2 * eta) ^ (j - 1) * P ^ (j - 1) := by
    dsimp [x]
    rw [mul_pow]
  have hetapow : (2 * eta) ^ j =
      (2 * eta) ^ (j - 1) * (2 * eta) := by
    conv_lhs => rw [hjEq]
    rw [pow_succ]
  have halgebra :
      variableDetectorNormalization eta J j ^ 2 *
          (2 * (P ^ (2 * (j - 1)) * ((N : ℝ) ^ (-eta)) ^ 2)) =
        2 * (((578 : ℝ) ^ J / 2) ^ 2) * (2 * eta) ^ 2 *
          (x ^ (j - 1) / F) ^ 2 * ((N : ℝ) ^ (-eta)) ^ 2 := by
    unfold variableDetectorNormalization
    dsimp only [F]
    rw [hPpow, hxpow, hetapow]
    field_simp
  rw [halgebra]
  let C : ℝ := 2 * (((578 : ℝ) ^ J / 2) ^ 2) * (2 * eta) ^ 2
  have hC : 0 ≤ C := by dsimp [C]; positivity
  calc
    2 * (((578 : ℝ) ^ J / 2) ^ 2) * (2 * eta) ^ 2 *
          (x ^ (j - 1) / F) ^ 2 * ((N : ℝ) ^ (-eta)) ^ 2 ≤
        2 * (((578 : ℝ) ^ J / 2) ^ 2) * (2 * eta) ^ 2 *
          Real.exp x ^ 2 * ((N : ℝ) ^ (-eta)) ^ 2 := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hseriesSq hC) (by positivity)
    _ ≤ 2 * (((578 : ℝ) ^ J / 2) ^ 2) * (2 * eta) ^ 2 *
          Real.exp x ^ 2 * 1 := by
      exact mul_le_mul_of_nonneg_left hrpowSq (by positivity)
    _ ≤ 2 * (((578 : ℝ) ^ J / 2) ^ 2) * (2 * eta) ^ 2 *
          Real.exp (4 * R + 1) := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hexp hC
    _ = 2 * (578 : ℝ) ^ (2 * J) * eta ^ 2 *
          Real.exp (4 * R + 1) := by
      have h578 : (((578 : ℝ) ^ J) ^ 2) = (578 : ℝ) ^ (2 * J) := by
        rw [← pow_mul]
        congr 1
        omega
      rw [div_pow, h578]
      ring

/-- On the Page interval, the normalized Gamma coefficient is maximized at
the fixed endpoint `eta = 1/8`. -/
theorem normalizedGallagherDerivativeGammaCoefficient_le_eighth
    {eta : ℝ} (heta : 0 ≤ eta) (heta8 : eta ≤ 1 / 8)
    (J k : ℕ) :
    normalizedGallagherDerivativeGammaCoefficient eta J k ≤
      normalizedGallagherDerivativeGammaCoefficient (1 / 8) J k := by
  have hpow : (2 : ℝ) ^ (4 * eta) ≤ (2 : ℝ) ^ (4 * (1 / 8 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  unfold normalizedGallagherDerivativeGammaCoefficient
  gcongr

/-- Harmonic partial summation costs at most `1 + log N`. -/
theorem sum_Icc_inv_le_one_add_log
    {Y N : ℕ} (hY : 1 ≤ Y) :
    (∑ m ∈ Finset.Icc Y N, (m : ℝ)⁻¹) ≤ 1 + Real.log N := by
  calc
    (∑ m ∈ Finset.Icc Y N, (m : ℝ)⁻¹) ≤
        ∑ m ∈ Finset.Icc 1 N, (m : ℝ)⁻¹ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro m hm
        exact Finset.mem_Icc.mpr
          ⟨hY.trans (Finset.mem_Icc.mp hm).1, (Finset.mem_Icc.mp hm).2⟩
      · intro m hm hnot
        positivity
    _ ≤ 1 + Real.log N := by
      simpa only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv,
        Rat.cast_natCast] using harmonic_le_one_add_log N

/-- A fourth-power lower cutoff turns the square-root shell decay into the
inverse square of the global integral scale. -/
theorem inv_sqrt_le_inv_sq_of_pow_four_le
    {b Y : ℕ} (hb : 0 < b) (hpow : b ^ 4 ≤ Y) :
    (Real.sqrt (Y : ℝ))⁻¹ ≤ ((b : ℝ) ^ 2)⁻¹ := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hpowR : ((b : ℝ) ^ 4) ≤ (Y : ℝ) := by exact_mod_cast hpow
  have hsqrt : (b : ℝ) ^ 2 ≤ Real.sqrt (Y : ℝ) := by
    rw [Real.le_sqrt (sq_nonneg _) (Nat.cast_nonneg Y)]
    nlinarith [hpowR]
  exact inv_anti₀ (by positivity) hsqrt

/-- The higher-prime-power shell tail at a fourth-power lower cutoff. -/
theorem gallagherHigherPrimePowerShellTail_le_inv_sq
    {b Y N : ℕ} (hb : 0 < b) (hY : 1 ≤ Y) (hpow : b ^ 4 ≤ Y) :
    gallagherHigherPrimePowerShellTail Y N ≤
      2 * (((Nat.log 2 (N - 1) + 1 : ℕ) : ℝ) ^ 3 *
        Real.log 2 ^ 2) * ((b : ℝ) ^ 2)⁻¹ := by
  apply (gallagherHigherPrimePowerShellTail_le Y N hY).trans
  exact mul_le_mul_of_nonneg_left
    (inv_sqrt_le_inv_sq_of_pow_four_le hb hpow) (by positivity)

/-- A logarithmic square is absorbed by the inverse square of its positive
argument.  The deliberately loose constant keeps later ring calculations
simple. -/
theorem log_sq_mul_inv_sq_le_four {b : ℕ} (hb : 1 ≤ b) :
    Real.log (b : ℝ) ^ 2 * ((b : ℝ) ^ 2)⁻¹ ≤ 4 := by
  have hbR : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hbPos : (0 : ℝ) < b := zero_lt_one.trans_le hbR
  have hlog0 : 0 ≤ Real.log (b : ℝ) := Real.log_nonneg hbR
  have hlog := Real.log_le_rpow_div (Nat.cast_nonneg b)
    (show (0 : ℝ) < 1 / 2 by norm_num)
  norm_num at hlog
  rw [← Real.sqrt_eq_rpow] at hlog
  have hsq : Real.log (b : ℝ) ^ 2 ≤ 4 * (b : ℝ) := by
    have := pow_le_pow_left₀ hlog0 hlog 2
    calc
      Real.log (b : ℝ) ^ 2 ≤
          (Real.sqrt (b : ℝ) / (1 / 2 : ℝ)) ^ 2 := this
      _ = 4 * (b : ℝ) := by
        rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg b)]
        norm_num
        ring
  calc
    Real.log (b : ℝ) ^ 2 * ((b : ℝ) ^ 2)⁻¹ ≤
        (4 * (b : ℝ)) * ((b : ℝ) ^ 2)⁻¹ :=
      mul_le_mul_of_nonneg_right hsq (by positivity)
    _ ≤ 4 := by
      field_simp
      nlinarith

/-- The scale-independent part of the amplified cutoff mean after the
dyadic length is bounded by `P * log b`. -/
noncomputable def gallagherPageMeanEnvelope (P : ℝ) : ℝ :=
  8 * Real.exp 2 * (1 + 16 * Real.pi) * (Real.log 4 + 4) *
        P ^ 2 * Real.log 2 +
    32 * Real.exp 2 * (1 + 16 * Real.pi) *
        P ^ 3 * Real.log 2 ^ 2

theorem gallagherPageMeanEnvelope_nonneg {P : ℝ} (hP : 0 ≤ P) :
    0 ≤ gallagherPageMeanEnvelope P := by
  unfold gallagherPageMeanEnvelope
  positivity

/-- The complete-cutoff amplified band is quadratic in `log b`; the
higher-prime-power part is absorbed by its fourth-power lower cutoff. -/
theorem gallagherAmplifiedCutoffBandBound_le_page
    {b Y N : ℕ} {P : ℝ}
    (hb : 1 ≤ b) (hY : 1 ≤ Y) (hpow : b ^ 4 ≤ Y) (hP : 0 ≤ P)
    (hM : (((Nat.log 2 (N - 1) + 1 : ℕ) : ℝ)) ≤
      P * Real.log b) :
    gallagherAmplifiedCutoffBandBound (Real.log b / 2) Y N ≤
      gallagherPageMeanEnvelope P * Real.log b ^ 2 := by
  let M : ℝ := (((Nat.log 2 (N - 1) + 1 : ℕ) : ℝ))
  let z : ℝ := Real.log b
  let A : ℝ := 8 * Real.exp 2 * (1 + 16 * Real.pi) *
    (Real.log 4 + 4)
  let D : ℝ := 8 * Real.exp 2 * (1 + 16 * Real.pi)
  have hz : 0 ≤ z := by dsimp [z]; exact Real.log_nonneg (by exact_mod_cast hb)
  have hM0 : 0 ≤ M := by dsimp [M]; positivity
  have hM' : M ≤ P * z := by simpa only [M, z] using hM
  have hM2 : M ^ 2 ≤ (P * z) ^ 2 := pow_le_pow_left₀ hM0 hM' 2
  have hM3 : M ^ 3 ≤ (P * z) ^ 3 := pow_le_pow_left₀ hM0 hM' 3
  have hshell := sum_activeShell_log_le_logSquare Y N N le_rfl
  have htail := gallagherHigherPrimePowerShellTail_le_inv_sq
    (b := b) (Y := Y) (N := N) (by omega) hY hpow
  have hzinv : z ^ 2 * ((b : ℝ) ^ 2)⁻¹ ≤ 4 := by
    simpa only [z] using log_sq_mul_inv_sq_le_four hb
  have hmain :
      A * (∑ a ∈ detectorActiveShells Y N,
          ((a + 1 : ℕ) : ℝ) * Real.log 2) ≤
        A * (P * z) ^ 2 * Real.log 2 := by
    calc
      A * (∑ a ∈ detectorActiveShells Y N,
          ((a + 1 : ℕ) : ℝ) * Real.log 2) ≤
          A * (M ^ 2 * Real.log 2) :=
        mul_le_mul_of_nonneg_left (by simpa only [M] using hshell) (by
          dsimp [A]; positivity)
      _ ≤ A * ((P * z) ^ 2 * Real.log 2) := by gcongr
      _ = _ := by ring
  have htailTerm :
      D * (z / 2) * gallagherHigherPrimePowerShellTail Y N ≤
        4 * D * P ^ 3 * Real.log 2 ^ 2 * z ^ 2 := by
    calc
      D * (z / 2) * gallagherHigherPrimePowerShellTail Y N ≤
          D * (z / 2) *
            (2 * (M ^ 3 * Real.log 2 ^ 2) * ((b : ℝ) ^ 2)⁻¹) :=
        mul_le_mul_of_nonneg_left htail (by dsimp [D, z]; positivity)
      _ ≤ D * (z / 2) *
            (2 * ((P * z) ^ 3 * Real.log 2 ^ 2) *
              ((b : ℝ) ^ 2)⁻¹) := by gcongr
      _ = D * P ^ 3 * Real.log 2 ^ 2 * z ^ 2 *
            (z ^ 2 * ((b : ℝ) ^ 2)⁻¹) := by ring
      _ ≤ D * P ^ 3 * Real.log 2 ^ 2 * z ^ 2 * 4 :=
        mul_le_mul_of_nonneg_left hzinv (by dsimp [D]; positivity)
      _ = _ := by ring
  unfold gallagherAmplifiedCutoffBandBound
  calc
    8 * Real.exp 2 * (1 + 16 * Real.pi) * (Real.log 4 + 4) *
        (∑ a ∈ detectorActiveShells Y N,
          ((a + 1 : ℕ) : ℝ) * Real.log 2) +
        8 * (Real.log b / 2) * Real.exp 2 * (1 + 16 * Real.pi) *
          gallagherHigherPrimePowerShellTail Y N =
      A * (∑ a ∈ detectorActiveShells Y N,
        ((a + 1 : ℕ) : ℝ) * Real.log 2) +
        D * (z / 2) * gallagherHigherPrimePowerShellTail Y N := by
      dsimp [A, D, z]
      ring
    _ ≤
      A * (P * z) ^ 2 * Real.log 2 +
        4 * D * P ^ 3 * Real.log 2 ^ 2 * z ^ 2 :=
      add_le_add hmain htailTerm
    _ = gallagherPageMeanEnvelope P * Real.log b ^ 2 := by
      dsimp [A, D, z, gallagherPageMeanEnvelope]
      ring

/-- The corresponding partial-sum energy has one extra harmonic factor. -/
theorem gallagherAmplifiedCutoffEnergyBound_le_page
    {b Y N : ℕ} {P H : ℝ}
    (hb : 1 ≤ b) (hY : 1 ≤ Y) (hpow : b ^ 4 ≤ Y)
    (hP : 0 ≤ P) (hH : 0 ≤ H)
    (hM : (((Nat.log 2 (N - 1) + 1 : ℕ) : ℝ)) ≤
      P * Real.log b)
    (hharm : (∑ m ∈ Finset.Icc Y N, (m : ℝ)⁻¹) ≤
      H * Real.log b) :
    gallagherAmplifiedCutoffEnergyBound (Real.log b / 2) Y N ≤
      gallagherPageMeanEnvelope P * H * Real.log b ^ 3 := by
  let M : ℝ := (((Nat.log 2 (N - 1) + 1 : ℕ) : ℝ))
  let z : ℝ := Real.log b
  let A : ℝ := 8 * Real.exp 2 * (1 + 16 * Real.pi) *
    (Real.log 4 + 4)
  let D : ℝ := 8 * Real.exp 2 * (1 + 16 * Real.pi)
  have hz : 0 ≤ z := by dsimp [z]; exact Real.log_nonneg (by exact_mod_cast hb)
  have hM0 : 0 ≤ M := by dsimp [M]; positivity
  have hM' : M ≤ P * z := by simpa only [M, z] using hM
  have hM2 : M ^ 2 ≤ (P * z) ^ 2 := pow_le_pow_left₀ hM0 hM' 2
  have hM3 : M ^ 3 ≤ (P * z) ^ 3 := pow_le_pow_left₀ hM0 hM' 3
  have htail := gallagherHigherPrimePowerShellTail_le_inv_sq
    (b := b) (Y := Y) (N := N) (by omega) hY hpow
  have hzinv : z ^ 2 * ((b : ℝ) ^ 2)⁻¹ ≤ 4 := by
    simpa only [z] using log_sq_mul_inv_sq_le_four hb
  have hmain : A * M ^ 2 * Real.log 2 ≤
      A * (P * z) ^ 2 * Real.log 2 := by gcongr
  have htailTerm :
      D * (z / 2) * gallagherHigherPrimePowerShellTail Y N ≤
        4 * D * P ^ 3 * Real.log 2 ^ 2 * z ^ 2 := by
    calc
      D * (z / 2) * gallagherHigherPrimePowerShellTail Y N ≤
          D * (z / 2) *
            (2 * (M ^ 3 * Real.log 2 ^ 2) * ((b : ℝ) ^ 2)⁻¹) :=
        mul_le_mul_of_nonneg_left htail (by dsimp [D, z]; positivity)
      _ ≤ D * (z / 2) *
            (2 * ((P * z) ^ 3 * Real.log 2 ^ 2) *
              ((b : ℝ) ^ 2)⁻¹) := by gcongr
      _ = D * P ^ 3 * Real.log 2 ^ 2 * z ^ 2 *
            (z ^ 2 * ((b : ℝ) ^ 2)⁻¹) := by ring
      _ ≤ D * P ^ 3 * Real.log 2 ^ 2 * z ^ 2 * 4 :=
        mul_le_mul_of_nonneg_left hzinv (by dsimp [D]; positivity)
      _ = _ := by ring
  have hbase :
      A * M ^ 2 * Real.log 2 +
          (z / 2) * D * gallagherHigherPrimePowerShellTail Y N ≤
        gallagherPageMeanEnvelope P * z ^ 2 := by
    calc
      A * M ^ 2 * Real.log 2 +
          (z / 2) * D * gallagherHigherPrimePowerShellTail Y N =
        A * M ^ 2 * Real.log 2 +
          D * (z / 2) * gallagherHigherPrimePowerShellTail Y N := by ring
      _ ≤ A * (P * z) ^ 2 * Real.log 2 +
          4 * D * P ^ 3 * Real.log 2 ^ 2 * z ^ 2 :=
        add_le_add hmain htailTerm
      _ = gallagherPageMeanEnvelope P * z ^ 2 := by
        dsimp [A, D, gallagherPageMeanEnvelope]
        ring
  unfold gallagherAmplifiedCutoffEnergyBound at ⊢
  have henv : 0 ≤ gallagherPageMeanEnvelope P * z ^ 2 :=
    mul_nonneg (gallagherPageMeanEnvelope_nonneg hP) (sq_nonneg _)
  calc
    (8 * Real.exp 2 * (1 + 16 * Real.pi) * (Real.log 4 + 4) *
          (((Nat.log 2 (N - 1) + 1 : ℕ) : ℝ)) ^ 2 * Real.log 2 +
        8 * (Real.log b / 2) * Real.exp 2 * (1 + 16 * Real.pi) *
          gallagherHigherPrimePowerShellTail Y N) *
        ∑ m ∈ Finset.Icc Y N, (m : ℝ)⁻¹ =
      (A * M ^ 2 * Real.log 2 +
        (z / 2) * D * gallagherHigherPrimePowerShellTail Y N) *
        ∑ m ∈ Finset.Icc Y N, (m : ℝ)⁻¹ := by
      dsimp [A, D, M, z]
      ring
    _ ≤ (gallagherPageMeanEnvelope P * z ^ 2) *
        ∑ m ∈ Finset.Icc Y N, (m : ℝ)⁻¹ := by
      exact mul_le_mul_of_nonneg_right hbase (by positivity)
    _ ≤ (gallagherPageMeanEnvelope P * z ^ 2) *
        (H * z) := mul_le_mul_of_nonneg_left (by simpa only [z] using hharm) henv
    _ = gallagherPageMeanEnvelope P * H * Real.log b ^ 3 := by
      dsimp [z]
      ring

noncomputable def gallagherPageEndpointEnvelope (R : ℝ) (J : ℕ) : ℝ :=
  2 * (578 : ℝ) ^ (2 * J) * Real.exp (4 * R + 1)

theorem gallagherPageEndpointEnvelope_nonneg (R : ℝ) (J : ℕ) :
    0 ≤ gallagherPageEndpointEnvelope R J := by
  unfold gallagherPageEndpointEnvelope
  positivity

/-- Every selected detector order is uniformly bounded at Page width. -/
theorem gallagherRawDensityTermAt_le_page
    {b Q T E J j : ℕ} {lambda eta R P H : ℝ}
    (hb : 2 ≤ b) (hlambda : 0 < lambda)
    (heta : 0 < eta) (heta8 : eta ≤ 1 / 8)
    (hetaEq : eta = lambda / Real.log b) (hR : 0 ≤ R)
    (hj : 1 ≤ j)
    (hpow : b ^ 4 ≤ variableDetectorLowerCutoff E eta j)
    (hP : 0 ≤ P) (hH : 0 ≤ H)
    (hM : (((Nat.log 2 (zeroDetectorCutoff R eta - 1) + 1 : ℕ) : ℝ)) ≤
      P * Real.log b)
    (hharm : (∑ m ∈ Finset.Icc (variableDetectorLowerCutoff E eta j)
        (zeroDetectorCutoff R eta), (m : ℝ)⁻¹) ≤ H * Real.log b) :
    gallagherRawDensityTermAt Q T E (zeroDetectorCutoff R eta) J j
        (Real.log b / 2) eta R ≤
      gallagherPageMeanEnvelope P *
        (gallagherPageEndpointEnvelope R J * lambda ^ 2 +
          2 * normalizedGallagherDerivativeGammaCoefficient (1 / 8) J
            (j - 1) * lambda ^ 3 * H) := by
  let Y : ℕ := variableDetectorLowerCutoff E eta j
  let N : ℕ := zeroDetectorCutoff R eta
  let z : ℝ := Real.log b
  let S : ℝ := gallagherPageMeanEnvelope P
  let U : ℝ := gallagherPageEndpointEnvelope R J
  let G : ℝ := normalizedGallagherDerivativeGammaCoefficient (1 / 8) J (j - 1)
  have hbR : (1 : ℝ) < b := by exact_mod_cast (show 1 < b by omega)
  have hz : 0 < z := by dsimp [z]; exact Real.log_pos hbR
  have hY : 1 ≤ Y := by
    dsimp [Y]
    have hbpow : 1 ≤ b ^ 4 := by
      exact Nat.one_le_pow 4 b (by omega)
    omega
  have hendpoint :
      variableDetectorNormalization eta J j ^ 2 *
          (2 * |gallagherWeight eta (j - 1) N| ^ 2) ≤ U * eta ^ 2 := by
    convert normalizedGallagherEndpointCoefficient_le heta heta8 hR J j hj using 1 <;>
      dsimp [N, U, gallagherPageEndpointEnvelope] <;> ring
  have hgamma :
      normalizedGallagherDerivativeGammaCoefficient eta J (j - 1) ≤ G := by
    simpa only [G] using
      normalizedGallagherDerivativeGammaCoefficient_le_eighth heta.le heta8 J (j - 1)
  have hband : gallagherAmplifiedCutoffBandBound (z / 2) Y N ≤ S * z ^ 2 := by
    simpa only [Y, N, z, S] using
      gallagherAmplifiedCutoffBandBound_le_page
        (b := b) (Y := Y) (N := N) (by omega) hY (by simpa only [Y] using hpow) hP
          (by simpa only [N] using hM)
  have henergy : gallagherAmplifiedCutoffEnergyBound (z / 2) Y N ≤
      S * H * z ^ 3 := by
    simpa only [Y, N, z, S] using
      gallagherAmplifiedCutoffEnergyBound_le_page
        (b := b) (Y := Y) (N := N) (by omega) hY (by simpa only [Y] using hpow)
          hP hH (by simpa only [N] using hM) (by simpa only [Y, N] using hharm)
  have hS : 0 ≤ S := by dsimp [S]; exact gallagherPageMeanEnvelope_nonneg hP
  have hU : 0 ≤ U := by dsimp [U]; exact gallagherPageEndpointEnvelope_nonneg R J
  have hG : 0 ≤ G := by dsimp [G, normalizedGallagherDerivativeGammaCoefficient]; positivity
  have hband0 : 0 ≤ gallagherAmplifiedCutoffBandBound (z / 2) Y N := by
    unfold gallagherAmplifiedCutoffBandBound gallagherHigherPrimePowerShellTail
    positivity
  have henergy0 : 0 ≤ gallagherAmplifiedCutoffEnergyBound (z / 2) Y N := by
    unfold gallagherAmplifiedCutoffEnergyBound gallagherHigherPrimePowerShellTail
    positivity
  have hendpointR0 : 0 ≤ U * eta ^ 2 := mul_nonneg hU (sq_nonneg _)
  have hderivativeR0 : 0 ≤ 2 * eta ^ 3 * G := by positivity
  have heta2 : eta ^ 2 * z ^ 2 = lambda ^ 2 := by
    rw [hetaEq]
    dsimp [z]
    field_simp [ne_of_gt (Real.log_pos hbR)]
  have heta3 : eta ^ 3 * z ^ 3 = lambda ^ 3 := by
    rw [hetaEq]
    dsimp [z]
    field_simp [ne_of_gt (Real.log_pos hbR)]
  unfold gallagherRawDensityTermAt
  change (variableDetectorNormalization eta J j ^ 2 *
      (2 * |gallagherWeight eta (j - 1) N| ^ 2)) *
        gallagherAmplifiedCutoffBandBound (z / 2) Y N +
      (2 * eta ^ 3 *
        normalizedGallagherDerivativeGammaCoefficient eta J (j - 1)) *
        gallagherAmplifiedCutoffEnergyBound (z / 2) Y N ≤ _
  calc
    _ ≤ (U * eta ^ 2) * (S * z ^ 2) +
        (2 * eta ^ 3 * G) * (S * H * z ^ 3) := by
      apply add_le_add
      · exact mul_le_mul hendpoint hband hband0 hendpointR0
      · apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left hgamma (by positivity)
        · exact henergy
        · exact henergy0
        · exact hderivativeR0
    _ = S * (U * lambda ^ 2 + 2 * G * lambda ^ 3 * H) := by
      rw [show (U * eta ^ 2) * (S * z ^ 2) = U * S * (eta ^ 2 * z ^ 2) by ring,
        heta2,
        show (2 * eta ^ 3 * G) * (S * H * z ^ 3) =
          2 * G * S * H * (eta ^ 3 * z ^ 3) by ring,
        heta3]
      ring
    _ = _ := by rfl

end Erdos48

end
