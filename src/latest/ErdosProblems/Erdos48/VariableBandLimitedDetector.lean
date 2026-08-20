/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos48.VariableDetectorPropagation
import ErdosProblems.Erdos48.DetectorLowPrefix
import ErdosProblems.Erdos48.ZeroSelection
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# A band-limited variable-order detector

The initial segment is chosen from the detected order itself.  Its length is
small enough for Stirling's lower bound to absorb the Turan coefficient, but
the preliminary dilation of the detector height makes it a fixed large power
of the conductor-height parameter.
-/

namespace Erdos48

open Complex
open BoundedGaps.Maynard

noncomputable section

/-- Dilution constant used in the order-dependent lower cutoff. -/
def variableDetectorDilution (E : ℕ) : ℕ :=
  2 ^ 40 * 578 ^ E

/-- Binary logarithm of the order-dependent lower cutoff. -/
noncomputable def variableDetectorLowerLog
    (E : ℕ) (eta : ℝ) (j : ℕ) : ℕ :=
  ⌊(j : ℝ) / ((variableDetectorDilution E : ℕ) * eta)⌋₊

/-- Lower cutoff for a detector of order `j`. -/
noncomputable def variableDetectorLowerCutoff
    (E : ℕ) (eta : ℝ) (j : ℕ) : ℕ :=
  2 ^ variableDetectorLowerLog E eta j

/-- The variable-order detector restricted to its long-index band. -/
noncomputable def variableBandZeroDetectorPolynomial
    {q : ℕ} (chi : DirichletCharacter ℂ q)
    (E : ℕ) (eta : ℝ) (j N : ℕ) (t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Ioc (variableDetectorLowerCutoff E eta j) N,
    (weightedVonMangoldtMajorant eta (j - 1) n : ℂ) * chi n *
      Complex.exp (I * (((-t * Real.log n) : ℝ) : ℂ))

theorem pow_div_three_le_factorial {n : ℕ} (hn : 1 ≤ n) :
    ((n : ℝ) / 3) ^ n ≤ (n.factorial : ℝ) := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hsqrt : (1 : ℝ) ≤ Real.sqrt (2 * Real.pi * n) := by
    rw [Real.one_le_sqrt]
    nlinarith [Real.pi_gt_three]
  have hdiv : (n : ℝ) / 3 ≤ (n : ℝ) / Real.exp 1 := by
    apply div_le_div_of_nonneg_left (by positivity) (Real.exp_pos 1)
      Real.exp_one_lt_three.le
  have hpow : ((n : ℝ) / 3) ^ n ≤
      ((n : ℝ) / Real.exp 1) ^ n :=
    pow_le_pow_left₀ (by positivity) hdiv n
  calc
    ((n : ℝ) / 3) ^ n ≤
        Real.sqrt (2 * Real.pi * n) *
          ((n : ℝ) / Real.exp 1) ^ n := by
      exact hpow.trans (by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hsqrt
          (by positivity : 0 ≤ ((n : ℝ) / Real.exp 1) ^ n))
    _ ≤ (n.factorial : ℝ) := Stirling.le_factorial_stirling n

theorem variableDetectorDilution_pos (E : ℕ) :
    0 < variableDetectorDilution E := by
  unfold variableDetectorDilution
  positivity

theorem variableDetectorLowerLog_mul_le
    (E j : ℕ) {eta : ℝ} (heta : 0 < eta) :
    (eta : ℝ) * variableDetectorLowerLog E eta j ≤
      (j : ℝ) / variableDetectorDilution E := by
  have hden : 0 < (variableDetectorDilution E : ℝ) * eta := by
    exact mul_pos (by exact_mod_cast variableDetectorDilution_pos E) heta
  have hfloor : (variableDetectorLowerLog E eta j : ℝ) ≤
      (j : ℝ) / ((variableDetectorDilution E : ℕ) * eta) := by
    unfold variableDetectorLowerLog
    exact Nat.floor_le (div_nonneg (by positivity) hden.le)
  calc
    eta * (variableDetectorLowerLog E eta j : ℝ) ≤
        eta * ((j : ℝ) /
          ((variableDetectorDilution E : ℕ) * eta)) :=
      mul_le_mul_of_nonneg_left hfloor heta.le
    _ = (j : ℝ) / variableDetectorDilution E := by
      push_cast
      field_simp [heta.ne', (variableDetectorDilution_pos E).ne']

/-- The deliberately large dilution constant leaves enough room for both
the Turan loss and Stirling's factorial lower bound. -/
theorem variable_detector_dilution_budget
    {E J j : ℕ} (hE : 1 ≤ E) (hj : 2 ≤ j)
    (hJ : J ≤ E * (j - 1)) :
    7 * (578 : ℝ) ^ J * (2 : ℝ) ^ j *
        ((j : ℝ) / variableDetectorDilution E) *
        (2 * (j : ℝ) / variableDetectorDilution E) ^ (j - 1) ≤
      ((j - 1).factorial : ℝ) / 16 := by
  let n : ℕ := j - 1
  let G : ℝ := (578 : ℝ) ^ E
  let A : ℝ := variableDetectorDilution E
  have hn : 1 ≤ n := by dsimp [n]; omega
  have hnPos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hG : 1 ≤ G := by dsimp [G]; exact one_le_pow₀ (by norm_num)
  have hA : 0 < A := by
    dsimp [A]
    exact_mod_cast variableDetectorDilution_pos E
  have hjEq : j = n + 1 := by dsimp [n]; omega
  have hjTwoN : (j : ℝ) ≤ 2 * n := by exact_mod_cast (show j ≤ 2 * n by omega)
  have hja : (j : ℝ) / A ≤ (2 * n) / A :=
    div_le_div_of_nonneg_right hjTwoN hA.le
  have htwoja : 2 * (j : ℝ) / A ≤ (4 * n) / A := by
    apply div_le_div_of_nonneg_right _ hA.le
    linarith
  have hpowja : (2 * (j : ℝ) / A) ^ n ≤ ((4 * n) / A) ^ n :=
    pow_le_pow_left₀ (by positivity) htwoja n
  have hpow578 : (578 : ℝ) ^ J ≤ G ^ n := by
    calc
      (578 : ℝ) ^ J ≤ (578 : ℝ) ^ (E * n) :=
        pow_le_pow_right₀ (by norm_num) (by simpa only [n] using hJ)
      _ = G ^ n := by dsimp [G]; rw [pow_mul]
  have hfirst :
      7 * (578 : ℝ) ^ J * (2 : ℝ) ^ j *
          ((j : ℝ) / A) * (2 * (j : ℝ) / A) ^ n ≤
        7 * G ^ n * (2 : ℝ) ^ (n + 1) *
          ((2 * n) / A) * ((4 * n) / A) ^ n := by
    rw [hjEq]
    have h₁ : 7 * (578 : ℝ) ^ J ≤ 7 * G ^ n :=
      mul_le_mul_of_nonneg_left hpow578 (by norm_num)
    have h₂ : 7 * (578 : ℝ) ^ J * (2 : ℝ) ^ (n + 1) ≤
        7 * G ^ n * (2 : ℝ) ^ (n + 1) :=
      mul_le_mul_of_nonneg_right h₁ (by positivity)
    have h₃ : 7 * (578 : ℝ) ^ J * (2 : ℝ) ^ (n + 1) *
        (((n + 1 : ℕ) : ℝ) / A) ≤
        7 * G ^ n * (2 : ℝ) ^ (n + 1) * ((2 * n) / A) := by
      simpa only [Nat.cast_add, Nat.cast_one, hjEq] using
        mul_le_mul h₂ hja (by positivity) (by positivity)
    exact mul_le_mul h₃ (by simpa only [hjEq] using hpowja)
      (by positivity) (by positivity)
  have hAeq : A = (2 : ℝ) ^ 40 * G := by
    dsimp [A, G, variableDetectorDilution]
    push_cast
    norm_num
  have hrewrite :
      7 * G ^ n * (2 : ℝ) ^ (n + 1) *
          ((2 * n) / A) * ((4 * n) / A) ^ n =
        (28 * n / ((2 : ℝ) ^ 40 * G)) *
          ((8 * n / (2 : ℝ) ^ 40) ^ n) := by
    rw [hAeq, pow_succ]
    have hGpos : 0 < G := zero_lt_one.trans_le hG
    have hbase : G * 2 * (4 * (n : ℝ) / ((2 : ℝ) ^ 40 * G)) =
        8 * n / (2 : ℝ) ^ 40 := by
      field_simp [hGpos.ne']
      ring
    calc
      7 * G ^ n * ((2 : ℝ) ^ n * 2) *
          (2 * n / ((2 : ℝ) ^ 40 * G)) *
          (4 * n / ((2 : ℝ) ^ 40 * G)) ^ n =
        (28 * n / ((2 : ℝ) ^ 40 * G)) *
          (G ^ n * (2 : ℝ) ^ n *
            (4 * n / ((2 : ℝ) ^ 40 * G)) ^ n) := by ring
      _ = (28 * n / ((2 : ℝ) ^ 40 * G)) *
          (G * 2 * (4 * n / ((2 : ℝ) ^ 40 * G))) ^ n := by
        rw [mul_pow, mul_pow]
      _ = (28 * n / ((2 : ℝ) ^ 40 * G)) *
          ((8 * n / (2 : ℝ) ^ 40) ^ n) := by rw [hbase]
  have hdropG :
      (28 * n / ((2 : ℝ) ^ 40 * G)) *
          ((8 * n / (2 : ℝ) ^ 40) ^ n) ≤
        (28 * n / (2 : ℝ) ^ 40) *
          ((8 * n / (2 : ℝ) ^ 40) ^ n) := by
    have hdiv : 28 * (n : ℝ) / ((2 : ℝ) ^ 40 * G) ≤
        28 * n / (2 : ℝ) ^ 40 := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      calc
        (2 : ℝ) ^ 40 ≤ (2 : ℝ) ^ 40 * 1 := by norm_num
        _ ≤ (2 : ℝ) ^ 40 * G := by gcongr
    exact mul_le_mul_of_nonneg_right hdiv (by positivity)
  have hnTwoNat := nat_le_two_pow_pred hn
  have hnTwo : (n : ℝ) ≤ (2 : ℝ) ^ (n - 1) := by exact_mod_cast hnTwoNat
  have hnTwo' : (n : ℝ) ≤ (2 : ℝ) ^ n :=
    hnTwo.trans (pow_le_pow_right₀ (by norm_num) (by omega))
  have hcoefficient :
      (448 * n / (2 : ℝ) ^ 40) *
          ((8 : ℝ) / (2 : ℝ) ^ 40) ^ n ≤
        (1 / 3 : ℝ) ^ n := by
    calc
      (448 * n / (2 : ℝ) ^ 40) *
          ((8 : ℝ) / (2 : ℝ) ^ 40) ^ n ≤
        (448 * (2 : ℝ) ^ n / (2 : ℝ) ^ 40) *
          ((8 : ℝ) / (2 : ℝ) ^ 40) ^ n := by gcongr
      _ = (448 / (2 : ℝ) ^ 40) *
          ((16 : ℝ) / (2 : ℝ) ^ 40) ^ n := by
        calc
          (448 * (2 : ℝ) ^ n / (2 : ℝ) ^ 40) *
              ((8 : ℝ) / (2 : ℝ) ^ 40) ^ n =
            (448 / (2 : ℝ) ^ 40) *
              ((2 : ℝ) ^ n * ((8 : ℝ) / (2 : ℝ) ^ 40) ^ n) := by ring
          _ = (448 / (2 : ℝ) ^ 40) *
              ((2 : ℝ) * ((8 : ℝ) / (2 : ℝ) ^ 40)) ^ n := by
            rw [mul_pow]
          _ = (448 / (2 : ℝ) ^ 40) *
              ((16 : ℝ) / (2 : ℝ) ^ 40) ^ n := by
            rw [show (2 : ℝ) * (8 / (2 : ℝ) ^ 40) =
              16 / (2 : ℝ) ^ 40 by ring]
      _ ≤ 1 * (1 / 3 : ℝ) ^ n := by
        apply mul_le_mul
        · norm_num
        · exact pow_le_pow_left₀ (by positivity) (by norm_num) n
        · positivity
        · norm_num
      _ = (1 / 3 : ℝ) ^ n := one_mul _
  have hscaled :
      16 * ((28 * n / (2 : ℝ) ^ 40) *
          ((8 * n / (2 : ℝ) ^ 40) ^ n)) ≤
        ((n : ℝ) / 3) ^ n := by
    have hpowSplit :
        (8 * (n : ℝ) / (2 : ℝ) ^ 40) ^ n =
          ((8 : ℝ) / (2 : ℝ) ^ 40) ^ n * (n : ℝ) ^ n := by
      rw [show 8 * (n : ℝ) / (2 : ℝ) ^ 40 =
          ((8 : ℝ) / (2 : ℝ) ^ 40) * n by ring, mul_pow]
    rw [hpowSplit]
    calc
      16 * ((28 * n / (2 : ℝ) ^ 40) *
          (((8 : ℝ) / (2 : ℝ) ^ 40) ^ n * (n : ℝ) ^ n)) =
        ((448 * n / (2 : ℝ) ^ 40) *
          ((8 : ℝ) / (2 : ℝ) ^ 40) ^ n) * (n : ℝ) ^ n := by ring
      _ ≤ (1 / 3 : ℝ) ^ n * (n : ℝ) ^ n := by gcongr
      _ = ((1 / 3 : ℝ) * n) ^ n := by rw [mul_pow]
      _ = ((n : ℝ) / 3) ^ n := by congr 1 <;> ring
  have hfactorial := pow_div_three_le_factorial hn
  calc
    7 * (578 : ℝ) ^ J * (2 : ℝ) ^ j *
        ((j : ℝ) / variableDetectorDilution E) *
        (2 * (j : ℝ) / variableDetectorDilution E) ^ (j - 1) ≤
      7 * (578 : ℝ) ^ J * (2 : ℝ) ^ j *
        ((j : ℝ) / A) * (2 * (j : ℝ) / A) ^ n := by rfl
    _ ≤ 7 * G ^ n * (2 : ℝ) ^ (n + 1) *
        ((2 * n) / A) * ((4 * n) / A) ^ n := hfirst
    _ = (28 * n / ((2 : ℝ) ^ 40 * G)) *
        ((8 * n / (2 : ℝ) ^ 40) ^ n) := hrewrite
    _ ≤ (28 * n / (2 : ℝ) ^ 40) *
        ((8 * n / (2 : ℝ) ^ 40) ^ n) := hdropG
    _ ≤ ((n : ℝ) / 3) ^ n / 16 := by
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 16)]
      simpa only [mul_comm] using hscaled
    _ ≤ (n.factorial : ℝ) / 16 := by gcongr
    _ = ((j - 1).factorial : ℝ) / 16 := by simp only [n]

theorem norm_variable_detector_prefix_le_majorant
    {q : ℕ} (chi : DirichletCharacter ℂ q)
    (eta : ℝ) (k M : ℕ) (t : ℝ) :
    ‖∑ n ∈ Finset.Icc 1 (2 ^ M),
        (weightedVonMangoldtMajorant eta k n : ℂ) * chi n *
          Complex.exp (I * (((-t * Real.log n) : ℝ) : ℂ))‖ ≤
      ∑ n ∈ Finset.Icc 1 (2 ^ M),
        weightedVonMangoldtMajorant eta k n := by
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 (2 ^ M),
        ‖(weightedVonMangoldtMajorant eta k n : ℂ) * chi n *
          Complex.exp (I * (((-t * Real.log n) : ℝ) : ℂ))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.Icc 1 (2 ^ M),
        weightedVonMangoldtMajorant eta k n := by
      apply Finset.sum_le_sum
      intro n hn
      rw [norm_mul, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg (by
          unfold weightedVonMangoldtMajorant
          positivity), Complex.norm_exp]
      have him :
          (I * (((-t * Real.log n) : ℝ) : ℂ)).re = 0 := by
        rw [Complex.mul_re]
        simp only [Complex.I_re, Complex.I_im, Complex.ofReal_re,
          Complex.ofReal_im, zero_mul, one_mul, sub_self]
      rw [him, Real.exp_zero, mul_one]
      exact mul_le_of_le_one_right (by
        unfold weightedVonMangoldtMajorant
        positivity)
        (DirichletCharacter.norm_le_one chi (n : ZMod q))

theorem full_variable_detector_eq_prefix_add_band
    {q : ℕ} (chi : DirichletCharacter ℂ q)
    (E : ℕ) (eta : ℝ) (j N : ℕ) (t : ℝ)
    (hMN : variableDetectorLowerCutoff E eta j ≤ N) :
    finiteZeroDetectorPolynomial chi eta (j - 1) N t =
      (∑ n ∈ Finset.Icc 1 (variableDetectorLowerCutoff E eta j),
        (weightedVonMangoldtMajorant eta (j - 1) n : ℂ) * chi n *
          Complex.exp (I * (((-t * Real.log n) : ℝ) : ℂ))) +
      variableBandZeroDetectorPolynomial chi E eta j N t := by
  classical
  unfold finiteZeroDetectorPolynomial variableBandZeroDetectorPolynomial
  rw [← Finset.sum_union]
  · have hcut : 1 ≤ variableDetectorLowerCutoff E eta j := by
      unfold variableDetectorLowerCutoff
      exact Nat.one_le_pow _ _ (by omega)
    have hunion :
        Finset.Icc 1 (variableDetectorLowerCutoff E eta j) ∪
            Finset.Ioc (variableDetectorLowerCutoff E eta j) N =
          Finset.Icc 1 N := by
      ext n
      simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_Ioc]
      omega
    rw [hunion]
  · exact Finset.disjoint_left.mpr (by
      intro n hn₁ hn₂
      have h₁ := Finset.mem_Icc.mp hn₁
      have h₂ := Finset.mem_Ioc.mp hn₂
      omega)

/-- After multiplying by the variable detector scale, its order-dependent
prefix costs at most half of the propagated lower bound. -/
theorem variable_detector_prefix_small
    {E K M J j : ℕ} {eta : ℝ}
    (hE : 1 ≤ E) (hK : 1 ≤ K) (hj : 2 ≤ j)
    (hKJ : K ≤ J) (hMJ : M ≤ J) (hJ : J ≤ E * (j - 1))
    (heta : 0 < eta) :
    turanSecondLoss K M * (2 * eta) ^ j *
        (∑ n ∈ Finset.Icc 1
            (variableDetectorLowerCutoff E eta j),
          weightedVonMangoldtMajorant eta (j - 1) n) ≤
      ((j - 1).factorial : ℝ) / 16 := by
  let m : ℕ := variableDetectorLowerLog E eta j
  let A : ℝ := variableDetectorDilution E
  let C : ℝ := Real.log 4 + 4
  have hA : 0 < A := by
    dsimp [A]
    exact_mod_cast variableDetectorDilution_pos E
  have hCnonneg : 0 ≤ C := by dsimp [C]; positivity
  have hCseven : C ≤ 7 := by
    dsimp [C]
    have hlog := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
    norm_num at hlog ⊢
    linarith
  have hprefix :
      (∑ n ∈ Finset.Icc 1 (2 ^ m),
          weightedVonMangoldtMajorant eta (j - 1) n) ≤
        2 * C * (m : ℝ) *
          (((m + 1 : ℕ) : ℝ) * Real.log 2) ^ (j - 1) := by
    simpa only [C] using
      sum_weightedVonMangoldtMajorant_Icc_two_pow_le
        eta heta (j - 1) m
  change turanSecondLoss K M * (2 * eta) ^ j *
      (∑ n ∈ Finset.Icc 1 (2 ^ m),
        weightedVonMangoldtMajorant eta (j - 1) n) ≤ _
  by_cases hm : m = 0
  · have hsumNonneg : 0 ≤
        ∑ n ∈ Finset.Icc 1 (2 ^ m),
          weightedVonMangoldtMajorant eta (j - 1) n :=
      Finset.sum_nonneg fun _ _ ↦ by
        unfold weightedVonMangoldtMajorant
        positivity
    have hsumZero :
        (∑ n ∈ Finset.Icc 1 (2 ^ m),
          weightedVonMangoldtMajorant eta (j - 1) n) = 0 := by
      apply le_antisymm
      · simpa only [hm, Nat.cast_zero, mul_zero, zero_mul] using hprefix
      · exact hsumNonneg
    rw [hsumZero, mul_zero]
    positivity
  · have hmOne : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
    have hetaM : eta * (m : ℝ) ≤ (j : ℝ) / A := by
      simpa only [m, A] using variableDetectorLowerLog_mul_le E j heta
    have hmSucc : ((m + 1 : ℕ) : ℝ) ≤ 2 * (m : ℝ) := by
      exact_mod_cast (show m + 1 ≤ 2 * m by omega)
    have hetaMSucc : eta * ((m + 1 : ℕ) : ℝ) ≤
        2 * (j : ℝ) / A := by
      calc
        eta * ((m + 1 : ℕ) : ℝ) ≤ eta * (2 * (m : ℝ)) :=
          mul_le_mul_of_nonneg_left hmSucc heta.le
        _ = 2 * (eta * (m : ℝ)) := by ring
        _ ≤ 2 * ((j : ℝ) / A) := by gcongr
        _ = 2 * (j : ℝ) / A := by ring
    have hlogTwo : Real.log 2 ≤ 1 :=
      (Real.log_le_sub_one_of_pos (by norm_num)).trans_eq (by norm_num)
    have hbase :
        eta * (((m + 1 : ℕ) : ℝ) * Real.log 2) ≤
          2 * (j : ℝ) / A := by
      calc
        eta * (((m + 1 : ℕ) : ℝ) * Real.log 2) ≤
            eta * (((m + 1 : ℕ) : ℝ) * 1) := by gcongr
        _ = eta * ((m + 1 : ℕ) : ℝ) := by ring
        _ ≤ 2 * (j : ℝ) / A := hetaMSucc
    have hpowbase :
        (eta * (((m + 1 : ℕ) : ℝ) * Real.log 2)) ^ (j - 1) ≤
          (2 * (j : ℝ) / A) ^ (j - 1) :=
      pow_le_pow_left₀ (by positivity) hbase (j - 1)
    have hloss := turanSecondLoss_le_orderEnvelope hK hKJ hMJ
    have hsplit :
        turanSecondLoss K M * (2 * eta) ^ j *
            (2 * C * (m : ℝ) *
              (((m + 1 : ℕ) : ℝ) * Real.log 2) ^ (j - 1)) =
          turanSecondLoss K M * 2 * C * (eta * (m : ℝ)) *
            (2 : ℝ) ^ j *
              (eta * (((m + 1 : ℕ) : ℝ) * Real.log 2)) ^ (j - 1) := by
      have hpowsucc : (2 * eta) ^ j =
          (2 * eta) ^ (j - 1) * (2 * eta) := by
        rw [← pow_succ]
        congr 1
        omega
      have hpowTwo : (2 : ℝ) ^ j =
          (2 : ℝ) ^ (j - 1) * 2 := by
        rw [← pow_succ]
        congr 1
        omega
      rw [hpowsucc, hpowTwo, mul_pow, mul_pow]
      ring
    calc
      turanSecondLoss K M * (2 * eta) ^ j *
          (∑ n ∈ Finset.Icc 1 (2 ^ m),
            weightedVonMangoldtMajorant eta (j - 1) n) ≤
        turanSecondLoss K M * (2 * eta) ^ j *
          (2 * C * (m : ℝ) *
            (((m + 1 : ℕ) : ℝ) * Real.log 2) ^ (j - 1)) := by
        exact mul_le_mul_of_nonneg_left hprefix
          (mul_nonneg (turanSecondLoss_pos (by omega : 0 < K)).le
            (by positivity))
      _ = turanSecondLoss K M * 2 * C * (eta * (m : ℝ)) *
            (2 : ℝ) ^ j *
              (eta * (((m + 1 : ℕ) : ℝ) * Real.log 2)) ^ (j - 1) := hsplit
      _ ≤ ((578 : ℝ) ^ J / 2) * 2 * C *
            ((j : ℝ) / A) * (2 : ℝ) ^ j *
              (2 * (j : ℝ) / A) ^ (j - 1) := by
        gcongr
      _ = C * (578 : ℝ) ^ J * (2 : ℝ) ^ j *
            ((j : ℝ) / A) *
              (2 * (j : ℝ) / A) ^ (j - 1) := by ring
      _ ≤ 7 * (578 : ℝ) ^ J * (2 : ℝ) ^ j *
            ((j : ℝ) / A) *
              (2 * (j : ℝ) / A) ^ (j - 1) := by gcongr
      _ ≤ ((j - 1).factorial : ℝ) / 16 := by
        exact variable_detector_dilution_budget hE hj hJ

theorem variableDetectorLowerCutoff_le_zeroDetectorCutoff
    {E J j : ℕ} {eta : ℝ} (hjJ : j ≤ J) (heta : 0 < eta) :
    variableDetectorLowerCutoff E eta j ≤
      zeroDetectorCutoff (variableZeroDetectorTailRadius J) eta := by
  let m : ℕ := variableDetectorLowerLog E eta j
  let A : ℝ := variableDetectorDilution E
  let R : ℝ := variableZeroDetectorTailRadius J
  have hAone : 1 ≤ A := by
    dsimp [A]
    exact_mod_cast (variableDetectorDilution_pos E).nat_succ_le
  have hlogTwoNonneg : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlogTwoOne : Real.log 2 ≤ 1 :=
    (Real.log_le_sub_one_of_pos (by norm_num)).trans_eq (by norm_num)
  have hetaM : eta * (m : ℝ) ≤ (j : ℝ) / A := by
    simpa only [m, A] using variableDetectorLowerLog_mul_le E j heta
  have hlog4624 : 1 < Real.log (4624 : ℝ) := by
    apply (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 4624)).2
    exact Real.exp_one_lt_three.trans (by norm_num)
  have hRgeJ : (J : ℝ) ≤ R := by
    let C : ℝ := Real.log 4 + 4
    let X : ℝ := (4624 : ℝ) ^ J
    have hC : 1 ≤ 12 * C := by
      dsimp [C]
      have hlog : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
      nlinarith
    have hXpos : 0 < X := by dsimp [X]; positivity
    have hinside : X ≤ 1 + 12 * C * X := by
      nlinarith [mul_le_mul_of_nonneg_right hC hXpos.le]
    have hlogle : Real.log X ≤ Real.log (1 + 12 * C * X) :=
      Real.log_le_log hXpos hinside
    have hlogX : Real.log X = (J : ℝ) * Real.log 4624 := by
      dsimp [X]
      rw [Real.log_pow]
    dsimp [R, variableZeroDetectorTailRadius]
    change (J : ℝ) ≤ 4 * Real.log (1 + 12 * C * X)
    calc
      (J : ℝ) ≤ 4 * ((J : ℝ) * Real.log 4624) := by
        have hJnonneg : (0 : ℝ) ≤ J := by positivity
        nlinarith [mul_le_mul_of_nonneg_left hlog4624.le hJnonneg]
      _ = 4 * Real.log X := by rw [hlogX]
      _ ≤ 4 * Real.log (1 + 12 * C * X) := by gcongr
  have hetaLogM : eta * (Real.log 2 * (m : ℝ)) ≤ R := by
    calc
      eta * (Real.log 2 * (m : ℝ)) = Real.log 2 * (eta * (m : ℝ)) := by ring
      _ ≤ Real.log 2 * ((j : ℝ) / A) :=
        mul_le_mul_of_nonneg_left hetaM hlogTwoNonneg
      _ ≤ 1 * ((j : ℝ) / A) := by gcongr
      _ = (j : ℝ) / A := one_mul _
      _ ≤ (j : ℝ) := (div_le_self (by positivity) hAone)
      _ ≤ (J : ℝ) := by exact_mod_cast hjJ
      _ ≤ R := hRgeJ
  have hlogM : Real.log 2 * (m : ℝ) ≤ R / eta := by
    exact (le_div_iff₀ heta).2 (by simpa only [mul_comm] using hetaLogM)
  have hMNreal : ((2 ^ m : ℕ) : ℝ) ≤ Real.exp (R / eta) := by
    calc
      ((2 ^ m : ℕ) : ℝ) = (2 : ℝ) ^ m := by norm_cast
      _ = (2 : ℝ) ^ (m : ℝ) := (Real.rpow_natCast 2 m).symm
      _ = Real.exp (Real.log 2 * (m : ℝ)) :=
        Real.rpow_def_of_pos (by norm_num) _
      _ ≤ Real.exp (R / eta) := Real.exp_le_exp.mpr hlogM
  change 2 ^ m ≤ zeroDetectorCutoff R eta
  exact_mod_cast hMNreal.trans (exp_div_le_zeroDetectorCutoff R eta)

/-- The propagated variable-order detector may be restricted to its long
band without losing more than half of its normalized lower bound. -/
theorem exists_variable_propagated_band_series_detector :
    ∃ κ D : ℕ, 1 ≤ κ ∧ 1 ≤ D ∧
      ∀ (q : ℕ) [NeZero q], ∀ (hq : 1 < q),
        ∀ (chi : DirichletCharacter ℂ q), ∀ (hchi : chi.IsPrimitive),
          ∀ (t eta : ℝ), 0 < eta → eta ≤ 1 / 8 →
            ∀ (rho₀ : ℂ),
              DirichletCharacter.LFunction chi rho₀ = 0 →
              dist rho₀ (((1 + eta : ℝ) : ℂ) + t * I) ≤ 2 * eta →
              ∀ H J : ℕ, variableDetectorHeight q t eta ≤ H →
                (D + κ) * H ≤ J →
                let E := D + κ
                let Z := smallDiskZeroFinsupp hq chi hchi t eta
                let K := Z.support.card
                let M := D * H
                let R := variableZeroDetectorTailRadius J
                let N := zeroDetectorCutoff R eta
                ∃ j ∈ Finset.Icc (M + 1) (M + K),
                  K ≤ κ * H ∧ j ≤ J ∧
                  variableDetectorLowerCutoff E eta j ≤ N ∧
                    ∀ u : ℝ,
                      |u - t| ≤ variableDetectorPropagationRadius J * eta →
                      ((j - 1).factorial : ℝ) / 16 <
                        turanSecondLoss K M * (2 * eta) ^ j *
                          ‖variableBandZeroDetectorPolynomial
                            chi E eta j N u‖ := by
  obtain ⟨κ, D, hκ, hD, hdetector⟩ :=
    exists_variable_propagated_finite_series_detector
  refine ⟨κ, D, hκ, hD, ?_⟩
  intro q _ hq chi hchi t eta heta heta8 rho₀ hzero hrho
    H J hHeight hJ
  dsimp only
  let E := D + κ
  let Z := smallDiskZeroFinsupp hq chi hchi t eta
  let K := Z.support.card
  let M := D * H
  let R := variableZeroDetectorTailRadius J
  let N := zeroDetectorCutoff R eta
  obtain ⟨j, hjLocal, hKH, hjJ, hjlarge⟩ :=
    hdetector q hq chi hchi t eta heta heta8 rho₀ hzero hrho
      H J hHeight hJ
  have hB : (1 : ℝ) ≤
      1 + eta * Real.log ((q : ℝ) * (|t| + 2)) := by
    have hqTwo : (2 : ℝ) ≤ q := by exact_mod_cast hq
    have hinside : (1 : ℝ) ≤ (q : ℝ) * (|t| + 2) := by
      nlinarith [abs_nonneg t]
    have hlog : 0 ≤ Real.log ((q : ℝ) * (|t| + 2)) :=
      Real.log_nonneg hinside
    nlinarith [mul_nonneg heta.le hlog]
  have hheightOne : 1 ≤ variableDetectorHeight q t eta := by
    have hcast : (1 : ℝ) ≤
        (variableDetectorHeight q t eta : ℕ) := by
      exact hB.trans (by
        simpa only [variableDetectorHeight] using
          Nat.le_ceil (1 + eta * Real.log ((q : ℝ) * (|t| + 2))))
    exact_mod_cast hcast
  have hH : 1 ≤ H := hheightOne.trans hHeight
  have hK : 1 ≤ K := by
    have hjLower := (Finset.mem_Icc.mp hjLocal).1
    have hjUpper := (Finset.mem_Icc.mp hjLocal).2
    have hMK : M + 1 ≤ M + K := hjLower.trans hjUpper
    exact Nat.add_le_add_iff_left.mp hMK
  have hjTwo : 2 ≤ j := by
    have hjLower := (Finset.mem_Icc.mp hjLocal).1
    have hDH : 1 ≤ D * H := Nat.mul_pos (by omega) (by omega)
    omega
  have hHj : H ≤ j - 1 := by
    have hHDH : H ≤ D * H := by
      simpa only [one_mul] using Nat.mul_le_mul_right H hD
    have hDHj : D * H ≤ j - 1 := by
      have := (Finset.mem_Icc.mp hjLocal).1
      omega
    exact hHDH.trans hDHj
  have hE : 1 ≤ E := by dsimp [E]; omega
  have hKloss : K ≤ E * (j - 1) := by
    calc
      K ≤ κ * H := hKH
      _ ≤ κ * (j - 1) := Nat.mul_le_mul_left κ hHj
      _ ≤ E * (j - 1) := by
        apply Nat.mul_le_mul_right
        dsimp [E]
        omega
  have hMloss : M ≤ E * (j - 1) := by
    dsimp [M, E]
    calc
      D * H ≤ D * (j - 1) := Nat.mul_le_mul_left D hHj
      _ ≤ (D + κ) * (j - 1) := by gcongr <;> omega
  have hcut : variableDetectorLowerCutoff E eta j ≤ N := by
    simpa only [N, R] using
      variableDetectorLowerCutoff_le_zeroDetectorCutoff
        (E := E) hjJ heta
  refine ⟨j, by simpa only [Z, K, M] using hjLocal,
    by simpa only [Z, K] using hKH, hjJ, hcut, ?_⟩
  intro u hu
  have hfull := hjlarge u hu
  let lowPart : ℂ :=
    ∑ n ∈ Finset.Icc 1 (variableDetectorLowerCutoff E eta j),
      (weightedVonMangoldtMajorant eta (j - 1) n : ℂ) * chi n *
        Complex.exp (I * (((-u * Real.log n) : ℝ) : ℂ))
  have hprefixNorm :
      turanSecondLoss K M * (2 * eta) ^ j * ‖lowPart‖ ≤
        ((j - 1).factorial : ℝ) / 16 := by
    calc
      turanSecondLoss K M * (2 * eta) ^ j * ‖lowPart‖ ≤
          turanSecondLoss K M * (2 * eta) ^ j *
            (∑ n ∈ Finset.Icc 1
                (variableDetectorLowerCutoff E eta j),
              weightedVonMangoldtMajorant eta (j - 1) n) := by
        apply mul_le_mul_of_nonneg_left
        · exact norm_variable_detector_prefix_le_majorant
            chi eta (j - 1) (variableDetectorLowerLog E eta j) u
        · exact mul_nonneg (turanSecondLoss_pos (by omega : 0 < K)).le
            (by positivity)
      _ ≤ ((j - 1).factorial : ℝ) / 16 :=
        variable_detector_prefix_small hE hK hjTwo
          hKloss hMloss le_rfl heta
  have hdecomp := full_variable_detector_eq_prefix_add_band
    chi E eta j N u hcut
  have htriangle :
      ‖finiteZeroDetectorPolynomial chi eta (j - 1) N u‖ ≤
        ‖lowPart‖ +
          ‖variableBandZeroDetectorPolynomial chi E eta j N u‖ := by
    rw [hdecomp]
    simpa only [lowPart] using
      norm_add_le lowPart
        (variableBandZeroDetectorPolynomial chi E eta j N u)
  have hscale : 0 ≤ turanSecondLoss K M * (2 * eta) ^ j :=
    mul_nonneg (turanSecondLoss_pos (by omega : 0 < K)).le
      (by positivity)
  have hscaledTriangle := mul_le_mul_of_nonneg_left htriangle hscale
  nlinarith

end

end Erdos48
