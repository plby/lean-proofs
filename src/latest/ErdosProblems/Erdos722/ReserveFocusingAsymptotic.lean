/-
Copyright 2026 The Lean-Proofs Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0
-/
import ErdosProblems.Erdos722.RotationAbundance
import ErdosProblems.Erdos722.CoverAsymptotic
import Mathlib

set_option relaxedAutoImplicit true

/-!
# The separated reserve-focusing cover

The ordinary cover lemma is used later for the much sparser nibble leave.
Here the leave is the original reserve, whose codimension-one degree has
exponent `1 - 1 / rho`.  Rotation abundance supplies the stronger candidate
exponent `q-r-1/(3*rho)`.  The random-greedy spill cap is placed strictly
between these scales, at exponent `1-1/(2*rho)`.
-/

namespace Erdos722.ReserveFocusingAsymptotic

open Finset Filter
open scoped Topology Real
open Erdos722.Asymptotics
open Erdos722.Typicality
open Erdos722.Reserve
open Erdos722.RootedEmbedding
open Erdos722.RootSchedule
open Erdos722.CoverEmbedding
open Erdos722.CoverClique
open Erdos722.Cover

noncomputable section

def focusCandidateDen (rho : ℕ) : ℕ := 3 * rho
def focusCandidateNum (q r rho : ℕ) : ℕ :=
  focusCandidateDen rho * (q - r) - 1
def focusLeaveNum (rho : ℕ) : ℕ := rho - 1
def focusLoadDen (rho : ℕ) : ℕ := 2 * rho
def focusLoadNum (rho : ℕ) : ℕ := focusLoadDen rho - 1

def focusCandidateExp (q r rho : ℕ) : ℝ :=
  (focusCandidateNum q r rho : ℝ) / focusCandidateDen rho
def focusLeaveExp (rho : ℕ) : ℝ :=
  (focusLeaveNum rho : ℝ) / rho
def focusLoadExp (rho : ℕ) : ℝ :=
  (focusLoadNum rho : ℝ) / focusLoadDen rho

def focusCandidateLower (q r rho n : ℕ) : ℕ :=
  rationalPowerThreshold (focusCandidateNum q r rho)
    (focusCandidateDen rho) n

def focusLeaveCap (rho n : ℕ) : ℕ :=
  4 * rationalPowerThreshold (focusLeaveNum rho) rho n

def focusScheduleConstant (q r : ℕ) : ℕ :=
  4 * (2 ^ (r - 1) * (2 ^ q * r ^ r))

def focusLoadMultiplier (q r : ℕ) : ℕ :=
  64 * focusScheduleConstant q r

def focusSpentCap (q r rho n : ℕ) : ℕ :=
  focusLoadMultiplier q r *
    rationalPowerThreshold (focusLoadNum rho) (focusLoadDen rho) n

def focusDenominatorConstant (q r : ℕ) : ℕ :=
  coverMeetingConstant q r * 2 ^ q * focusLoadMultiplier q r

lemma focusCandidateDen_pos (hrho : 0 < rho) :
    0 < focusCandidateDen rho := by
  simp [focusCandidateDen, hrho]

lemma focusLoadDen_pos (hrho : 0 < rho) : 0 < focusLoadDen rho := by
  simp [focusLoadDen, hrho]

lemma focusCandidateNum_pos (hrq : r < q) (hrho : 0 < rho) :
    0 < focusCandidateNum q r rho := by
  dsimp [focusCandidateNum, focusCandidateDen]
  have hprod : 1 < 3 * rho * (q - r) := by
    calc
      1 < 3 * 1 * 1 := by norm_num
      _ ≤ 3 * rho * (q - r) := by gcongr <;> omega
  exact Nat.sub_pos_of_lt hprod

lemma focusLeaveNum_pos (hrho : 1 < rho) : 0 < focusLeaveNum rho := by
  simp [focusLeaveNum]
  omega

lemma focusLoadNum_pos (hrho : 0 < rho) : 0 < focusLoadNum rho := by
  simp [focusLoadNum, focusLoadDen]
  omega

/-- The three strict exponent gaps used by the focusing cover. -/
lemma focus_exponent_gaps (hrq : r < q) (hrho : 1 < rho) :
    let s : ℝ := ((q - r : ℕ) : ℝ)
    let a := focusCandidateExp q r rho
    let delta := focusLeaveExp rho
    let c := focusLoadExp rho
    (q - r - 1 : ℕ) + c < a ∧ s + delta - a < c := by
  dsimp [focusCandidateExp, focusCandidateNum, focusCandidateDen,
    focusLeaveExp, focusLeaveNum, focusLoadExp, focusLoadNum, focusLoadDen]
  have hs : 1 ≤ q - r := by omega
  have hcandSub : 1 ≤ 3 * rho * (q - r) := by
    calc
      1 ≤ 3 * 1 * 1 := by norm_num
      _ ≤ 3 * rho * (q - r) := by gcongr <;> omega
  have hloadSub : 1 ≤ 2 * rho := by omega
  have hrho0 : (0 : ℝ) < rho := by exact_mod_cast (by omega : 0 < rho)
  rw [Nat.cast_sub hcandSub,
    Nat.cast_sub (by omega : 1 ≤ rho),
    Nat.cast_sub hloadSub,
    Nat.cast_sub hs]
  push_cast
  field_simp
  constructor <;> nlinarith

lemma focusCandidateLower_le_of_power
    (hrq : r < q) (hrho : 0 < rho) {n x : ℕ}
    (h : n ^ focusCandidateNum q r rho ≤
      x ^ focusCandidateDen rho) :
    focusCandidateLower q r rho n ≤ x := by
  exact rationalPowerThreshold_le_of_power_lower _ _ _ _
    (focusCandidateDen_pos hrho) h

lemma eventually_focusLeave_degree_le
    (hrho : 1 < rho) :
    ∀ᶠ n : ℕ in atTop, ∀ x : ℕ,
      x ^ rho ≤ 2 ^ rho * n ^ focusLeaveNum rho →
      x ≤ focusLeaveCap rho n := by
  have hT := eventually_half_rpow_le_rationalPowerThreshold
    (focusLeaveNum_pos hrho) (by omega : 0 < rho)
  filter_upwards [hT, eventually_ge_atTop (1 : ℕ)] with n hT hn
  intro x hx
  let delta := focusLeaveExp rho
  let T := rationalPowerThreshold (focusLeaveNum rho) rho n
  have hnpos : (0 : ℝ) < n := by positivity
  have hrhoR : (0 : ℝ) < rho := by exact_mod_cast (by omega : 0 < rho)
  have hTlower : (n : ℝ) ^ delta / 2 ≤ T := by
    simpa [delta, focusLeaveExp] using hT
  have hbase : (2 : ℝ) * (n : ℝ) ^ delta ≤ 4 * T := by
    linarith
  have hpowBase := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤
      2 * (n : ℝ) ^ delta) hbase rho
  have hexp : delta * rho = (focusLeaveNum rho : ℝ) := by
    dsimp [delta, focusLeaveExp]
    field_simp
  have hidentity : ((2 : ℝ) * (n : ℝ) ^ delta) ^ rho =
      (2 ^ rho : ℕ) * (n ^ focusLeaveNum rho : ℕ) := by
    rw [mul_pow]
    push_cast
    have hnidentity : ((n : ℝ) ^ delta) ^ rho =
        (n : ℝ) ^ focusLeaveNum rho := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hnpos.le, hexp,
        Real.rpow_natCast]
    rw [hnidentity]
  have hxR : (x : ℝ) ^ rho ≤
      ((2 : ℝ) * (n : ℝ) ^ delta) ^ rho := by
    rw [hidentity]
    exact_mod_cast hx
  have hpow : x ^ rho ≤ (focusLeaveCap rho n) ^ rho := by
    have : (x : ℝ) ^ rho ≤ (4 * (T : ℝ)) ^ rho :=
      hxR.trans hpowBase
    exact_mod_cast this
  exact (Nat.pow_le_pow_iff_left (by omega : rho ≠ 0)).mp hpow

lemma eventually_half_focusCandidate_rpow_le
    (hrq : r < q) (hrho : 0 < rho) :
    ∀ᶠ n : ℕ in atTop,
      (n : ℝ) ^ focusCandidateExp q r rho / 2 ≤
        (focusCandidateLower q r rho n : ℝ) := by
  simpa [focusCandidateExp, focusCandidateLower] using
    eventually_half_rpow_le_rationalPowerThreshold
      (focusCandidateNum_pos hrq hrho) (focusCandidateDen_pos hrho)

lemma focusLeaveCap_cast_le (rho n : ℕ) :
    (focusLeaveCap rho n : ℝ) ≤
      4 * (n : ℝ) ^ focusLeaveExp rho := by
  rw [focusLeaveCap]
  push_cast
  exact mul_le_mul_of_nonneg_left
    (rationalPowerThreshold_cast_le _ _ _) (by norm_num)

lemma focusLeaveCap_pow_le (hrho : 0 < rho) (n : ℕ) :
    focusLeaveCap rho n ^ rho ≤
      4 ^ rho * n ^ focusLeaveNum rho := by
  rw [focusLeaveCap, mul_pow]
  exact Nat.mul_le_mul_left _
    (rationalPowerThreshold_pow_le _ _ _ hrho)

lemma focusSpentCap_cast_le (q r rho n : ℕ) :
    (focusSpentCap q r rho n : ℝ) ≤
      focusLoadMultiplier q r * (n : ℝ) ^ focusLoadExp rho := by
  rw [focusSpentCap]
  push_cast
  exact mul_le_mul_of_nonneg_left
    (rationalPowerThreshold_cast_le _ _ _) (Nat.cast_nonneg _)

lemma eventually_half_focusLoad_rpow_mul_le_spentCap
    (hrho : 0 < rho) :
    ∀ᶠ n : ℕ in atTop,
      (focusLoadMultiplier q r : ℝ) *
          ((n : ℝ) ^ focusLoadExp rho / 2) ≤
        (focusSpentCap q r rho n : ℝ) := by
  have h := eventually_half_rpow_le_rationalPowerThreshold
    (focusLoadNum_pos hrho) (focusLoadDen_pos hrho)
  filter_upwards [h] with n hn
  rw [focusSpentCap]
  push_cast
  exact mul_le_mul_of_nonneg_left hn (Nat.cast_nonneg _)

lemma focus_codim_cast_le
    (hr : 0 < r) (hrq : r < q) (rho n : ℕ) (hn : 1 ≤ n) :
    (codimOneMeetingBound (coverPattern q r) n
        ((coverPattern q r).freeEdges.card * focusSpentCap q r rho n) : ℝ) ≤
      focusDenominatorConstant q r *
        (n : ℝ) ^ ((q - r - 1 : ℕ) + focusLoadExp rho) := by
  let T := rationalPowerThreshold (focusLoadNum rho) (focusLoadDen rho) n
  have hnat := codimOneMeetingBound_coverPattern_le hr hrq n
    ((coverPattern q r).freeEdges.card * focusSpentCap q r rho n)
  have hfree := card_coverPattern_freeEdges_le (q := q) (r := r)
  have hupperNat :
      codimOneMeetingBound (coverPattern q r) n
          ((coverPattern q r).freeEdges.card * focusSpentCap q r rho n) ≤
        focusDenominatorConstant q r * T * n ^ (q - r - 1) := by
    calc
      codimOneMeetingBound (coverPattern q r) n
          ((coverPattern q r).freeEdges.card * focusSpentCap q r rho n) ≤
          coverMeetingConstant q r *
            ((coverPattern q r).freeEdges.card * focusSpentCap q r rho n) *
              n ^ (q - r - 1) := hnat
      _ ≤ coverMeetingConstant q r *
            ((2 ^ q) * focusSpentCap q r rho n) * n ^ (q - r - 1) := by
        exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _
          (Nat.mul_le_mul_right _ hfree))
      _ = focusDenominatorConstant q r * T * n ^ (q - r - 1) := by
        unfold focusSpentCap focusDenominatorConstant
        dsimp [T]
        ring
  have hupperReal :
      (codimOneMeetingBound (coverPattern q r) n
          ((coverPattern q r).freeEdges.card * focusSpentCap q r rho n) : ℝ) ≤
        (focusDenominatorConstant q r : ℝ) * T *
          (n : ℝ) ^ (q - r - 1) := by exact_mod_cast hupperNat
  calc
    _ ≤ (focusDenominatorConstant q r : ℝ) * T *
        (n : ℝ) ^ (q - r - 1) := hupperReal
    _ ≤ (focusDenominatorConstant q r : ℝ) *
        (n : ℝ) ^ focusLoadExp rho * (n : ℝ) ^ (q - r - 1) := by
      gcongr
      exact rationalPowerThreshold_cast_le _ _ _
    _ = focusDenominatorConstant q r *
        (n : ℝ) ^ ((q - r - 1 : ℕ) + focusLoadExp rho) := by
      have hnpos : (0 : ℝ) < n := by positivity
      rw [show (focusDenominatorConstant q r : ℝ) *
          (n : ℝ) ^ focusLoadExp rho * (n : ℝ) ^ (q - r - 1) =
        (focusDenominatorConstant q r : ℝ) *
          ((n : ℝ) ^ (q - r - 1 : ℕ) *
            (n : ℝ) ^ focusLoadExp rho) by ring]
      rw [← Real.rpow_natCast, ← Real.rpow_add hnpos]

theorem eventually_focus_legalLowerBound
    (hr : 0 < r) (hrq : r < q) (hrho : 1 < rho) :
    ∀ᶠ n : ℕ in atTop,
      0 < reserveLegalLowerBound (coverPattern q r) n
          (focusCandidateLower q r rho n) (focusSpentCap q r rho n) ∧
      (n : ℝ) ^ focusCandidateExp q r rho / 4 ≤
        (reserveLegalLowerBound (coverPattern q r) n
          (focusCandidateLower q r rho n)
          (focusSpentCap q r rho n) : ℝ) := by
  have hgap := (focus_exponent_gaps hrq hrho).1
  have hdom := eventually_const_mul_rpow_le_rpow
    (C := (4 * focusDenominatorConstant q r : ℕ)) hgap (by positivity)
  have hcand := eventually_half_focusCandidate_rpow_le
    (rho := rho) hrq (by omega)
  filter_upwards [hdom, hcand, eventually_ge_atTop (1 : ℕ)] with
      n hdom hcand hn
  let loss := codimOneMeetingBound (coverPattern q r) n
    ((coverPattern q r).freeEdges.card * focusSpentCap q r rho n)
  let A := focusCandidateLower q r rho n
  have hlossRaw := focus_codim_cast_le hr hrq rho n hn
  have hloss : (loss : ℝ) ≤
      (n : ℝ) ^ focusCandidateExp q r rho / 4 := by
    have hscaled : (4 : ℝ) *
        ((focusDenominatorConstant q r : ℝ) *
          (n : ℝ) ^ ((q - r - 1 : ℕ) + focusLoadExp rho)) ≤
        (n : ℝ) ^ focusCandidateExp q r rho := by
      convert hdom using 1 <;> push_cast <;> ring
    change (loss : ℝ) ≤ focusDenominatorConstant q r *
      (n : ℝ) ^ ((q - r - 1 : ℕ) + focusLoadExp rho) at hlossRaw
    linarith
  have hpowPos : 0 < (n : ℝ) ^ focusCandidateExp q r rho := by positivity
  have hlossAReal : (loss : ℝ) < A := by
    dsimp [A]
    linarith
  have hlossA : loss < A := by exact_mod_cast hlossAReal
  have hcastSub : ((A - loss : ℕ) : ℝ) = (A : ℝ) - loss := by
    rw [Nat.cast_sub hlossA.le]
  constructor
  · simpa [reserveLegalLowerBound, A, loss] using Nat.sub_pos_of_lt hlossA
  · rw [reserveLegalLowerBound]
    change (n : ℝ) ^ focusCandidateExp q r rho / 4 ≤
      ((A - loss : ℕ) : ℝ)
    rw [hcastSub]
    dsimp [A]
    linarith

theorem eventually_focus_quantitative_bound
    (hr : 0 < r) (hrq : r < q) (hrho : 1 < rho) :
    ∀ᶠ n : ℕ in atTop,
      (Real.exp 1 - 1) *
          ((faceScheduleNumeratorBound (coverPattern q r) n
              (focusLeaveCap rho n) : ℝ) /
            reserveLegalLowerBound (coverPattern q r) n
              (focusCandidateLower q r rho n)
              (focusSpentCap q r rho n)) ≤
        (focusSpentCap q r rho n : ℝ) / 2 := by
  have hlegal := eventually_focus_legalLowerBound hr hrq hrho
  have hcap := eventually_half_focusLoad_rpow_mul_le_spentCap
    (q := q) (r := r) (by omega : 0 < rho)
  let b : ℝ := (q - r : ℕ) + focusLeaveExp rho -
    focusCandidateExp q r rho
  have hbc : b < focusLoadExp rho := by
    simpa [b] using (focus_exponent_gaps hrq hrho).2
  have hdom := eventually_const_mul_rpow_le_rpow
    (C := (32 * focusScheduleConstant q r : ℕ)) hbc (by positivity)
  filter_upwards [hlegal, hcap, hdom, eventually_ge_atTop (1 : ℕ)] with
      n hlegal hcap hdom hn
  let L := reserveLegalLowerBound (coverPattern q r) n
    (focusCandidateLower q r rho n) (focusSpentCap q r rho n)
  let B := faceScheduleNumeratorBound (coverPattern q r) n
    (focusLeaveCap rho n)
  let a := focusCandidateExp q r rho
  let delta := focusLeaveExp rho
  let S := focusScheduleConstant q r
  have hD := focusLeaveCap_cast_le rho n
  have hnpos : (0 : ℝ) < n := by positivity
  have hB : (B : ℝ) ≤ (S : ℝ) * (n : ℝ) ^ ((q - r : ℕ) + delta) := by
    dsimp [B, S]
    rw [faceScheduleNumeratorBound_coverPattern hrq.le]
    push_cast
    calc
      (2 : ℝ) ^ (r - 1) * ((2 : ℝ) ^ q * (r : ℝ) ^ r) *
          (n : ℝ) ^ (q - r) * (focusLeaveCap rho n : ℝ) ≤
        (2 : ℝ) ^ (r - 1) * ((2 : ℝ) ^ q * (r : ℝ) ^ r) *
          (n : ℝ) ^ (q - r) * (4 * (n : ℝ) ^ delta) := by
            gcongr
      _ = (focusScheduleConstant q r : ℝ) *
          (n : ℝ) ^ ((q - r : ℕ) + delta) := by
            rw [Real.rpow_add hnpos, Real.rpow_natCast]
            dsimp [focusScheduleConstant]
            push_cast
            ring
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hlegal.1
  have hLlower : (n : ℝ) ^ a / 4 ≤ L := by simpa [L, a] using hlegal.2
  have hratio : (B : ℝ) / L ≤ (4 * S : ℕ) * (n : ℝ) ^ b := by
    apply (div_le_iff₀ hLpos).2
    have hpow : (n : ℝ) ^ ((q - r : ℕ) + delta) =
        (n : ℝ) ^ a * (n : ℝ) ^ b := by
      rw [← Real.rpow_add hnpos]
      congr 1
      dsimp [b]
      linarith
    calc
      (B : ℝ) ≤ (S : ℝ) * (n : ℝ) ^ ((q - r : ℕ) + delta) := hB
      _ = (S : ℝ) * ((n : ℝ) ^ a * (n : ℝ) ^ b) := by rw [hpow]
      _ ≤ (S : ℝ) * ((4 : ℝ) * L * (n : ℝ) ^ b) := by
        gcongr
        linarith
      _ = ((4 * S : ℕ) : ℝ) * (n : ℝ) ^ b * L := by push_cast; ring
  have hexpCoef : Real.exp 1 - 1 ≤ 2 := by
    linarith [Real.exp_one_lt_d9]
  have hleft : (Real.exp 1 - 1) * ((B : ℝ) / L) ≤
      (8 * S : ℕ) * (n : ℝ) ^ b := by
    calc
      _ ≤ 2 * (((4 * S : ℕ) : ℝ) * (n : ℝ) ^ b) := by
        exact mul_le_mul hexpCoef hratio (by positivity) (by norm_num)
      _ = ((8 * S : ℕ) : ℝ) * (n : ℝ) ^ b := by push_cast; ring
  have hsmall : ((8 * S : ℕ) : ℝ) * (n : ℝ) ^ b ≤
      (focusLoadMultiplier q r : ℝ) *
        ((n : ℝ) ^ focusLoadExp rho / 4) := by
    have hdom' : ((32 * S : ℕ) : ℝ) * (n : ℝ) ^ b ≤
        (n : ℝ) ^ focusLoadExp rho := by simpa [S] using hdom
    have hfirst : ((8 * S : ℕ) : ℝ) * (n : ℝ) ^ b ≤
        (n : ℝ) ^ focusLoadExp rho / 4 := by
      push_cast at hdom' ⊢
      linarith
    have hmult : (1 : ℝ) ≤ focusLoadMultiplier q r := by
      have hrr : 0 < r ^ r := by
        by_cases hz : r = 0
        · simp [hz]
        · positivity
      dsimp [focusLoadMultiplier, focusScheduleConstant]
      exact_mod_cast (by positivity : 0 < 64 *
        (4 * (2 ^ (r - 1) * (2 ^ q * r ^ r))))
    exact hfirst.trans (by
      calc
        (n : ℝ) ^ focusLoadExp rho / 4 =
            1 * ((n : ℝ) ^ focusLoadExp rho / 4) := by ring
        _ ≤ (focusLoadMultiplier q r : ℝ) *
            ((n : ℝ) ^ focusLoadExp rho / 4) := by
          exact mul_le_mul_of_nonneg_right hmult (by positivity))
  have hright : (focusLoadMultiplier q r : ℝ) *
      ((n : ℝ) ^ focusLoadExp rho / 4) ≤
        (focusSpentCap q r rho n : ℝ) / 2 := by
    linarith
  change (Real.exp 1 - 1) * ((B : ℝ) / L) ≤
    (focusSpentCap q r rho n : ℝ) / 2
  exact hleft.trans (hsmall.trans hright)

theorem eventually_focus_exponential_union_bound
    (hrho : 1 < rho) :
    ∀ᶠ n : ℕ in atTop,
      (Fintype.card (RelevantFaceLoadTarget (coverPattern q r) n) : ℝ) *
          Real.exp (-(focusSpentCap q r rho n : ℝ) / 2) < 1 := by
  let c := focusLoadExp rho
  let M := focusLoadMultiplier q r
  let C0 : ℝ := 2 ^ q
  have hc : 0 < c := by
    dsimp [c, focusLoadExp]
    exact div_pos (by exact_mod_cast focusLoadNum_pos (by omega : 0 < rho))
      (by exact_mod_cast focusLoadDen_pos (by omega : 0 < rho))
  have hM : 0 < (M : ℝ) := by
    have hrr : 0 < r ^ r := by
      by_cases hz : r = 0
      · simp [hz]
      · positivity
    exact_mod_cast (by
      dsimp [M, focusLoadMultiplier, focusScheduleConstant]
      positivity)
  have hdecay := tendsto_pow_mul_exp_neg_rpow_atTop (r - 1) hc
    (show (0 : ℝ) < (M : ℝ) / 4 by positivity)
  have hconst : Tendsto (fun x : ℝ ↦ C0 *
      (x ^ (r - 1) * Real.exp (-((M : ℝ) / 4) * x ^ c)))
      atTop (nhds 0) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds.mul hdecay : Tendsto (fun x : ℝ ↦ C0 *
        (x ^ (r - 1) * Real.exp (-((M : ℝ) / 4) * x ^ c)))
          atTop (nhds (C0 * 0)))
  have hsmall : ∀ᶠ n : ℕ in atTop,
      C0 * ((n : ℝ) ^ (r - 1) *
        Real.exp (-((M : ℝ) / 4) * (n : ℝ) ^ c)) < 1 :=
    (tendsto_order.1 (hconst.comp tendsto_natCast_atTop_atTop)).2 _ (by norm_num)
  have hcap := eventually_half_focusLoad_rpow_mul_le_spentCap
    (q := q) (r := r) (by omega : 0 < rho)
  filter_upwards [hsmall, hcap] with n hnsmall hcap
  have hcardNat :
      Fintype.card (RelevantFaceLoadTarget (coverPattern q r) n) ≤
        2 ^ q * n ^ (r - 1) := by
    calc
      _ ≤ (coverPattern q r).freeEdges.card * Nat.choose n (r - 1) :=
        card_relevantFaceLoadTarget_le _ _
      _ ≤ 2 ^ q * n ^ (r - 1) :=
        Nat.mul_le_mul card_coverPattern_freeEdges_le (Nat.choose_le_pow _ _)
  have hcardReal :
      (Fintype.card (RelevantFaceLoadTarget (coverPattern q r) n) : ℝ) ≤
        (2 ^ q : ℕ) * (n : ℝ) ^ (r - 1) := by exact_mod_cast hcardNat
  have hspent : (M : ℝ) / 4 * (n : ℝ) ^ c ≤
      (focusSpentCap q r rho n : ℝ) / 2 := by
    calc
      _ = ((M : ℝ) * ((n : ℝ) ^ c / 2)) / 2 := by ring
      _ ≤ _ := by
        simpa [M, c] using
          div_le_div_of_nonneg_right hcap (by norm_num : (0 : ℝ) ≤ 2)
  calc
    _ ≤ ((2 ^ q : ℕ) : ℝ) * (n : ℝ) ^ (r - 1) *
        Real.exp (-(focusSpentCap q r rho n : ℝ) / 2) := by gcongr
    _ ≤ ((2 ^ q : ℕ) : ℝ) * (n : ℝ) ^ (r - 1) *
        Real.exp (-((M : ℝ) / 4) * (n : ℝ) ^ c) := by
          gcongr
          convert neg_le_neg hspent using 1 <;> ring
    _ = C0 * ((n : ℝ) ^ (r - 1) *
        Real.exp (-((M : ℝ) / 4) * (n : ℝ) ^ c)) := by
          dsimp [C0]
          push_cast
          ring
    _ < 1 := hnsmall

/-- Power-cleared rotation abundance plus the original reserve degree bound
produces a pairwise spill-disjoint focusing clique for every reserve edge. -/
theorem eventually_exists_focusCoverAssignment_of_power_bounds
    (hr : 0 < r) (hrq : r < q) (hrho : 1 < rho) :
    ∀ᶠ n : ℕ in atTop, ∀ (leave host : Finset (Finset (Fin n))),
      (∀ e ∈ leave, e.card = r) →
      (∀ e ∈ host, e.card = r) →
      (∀ J : Finset (Fin n), J.card = r - 1 →
        (Reserve.localDegree leave J) ^ rho ≤
          2 ^ rho * n ^ focusLeaveNum rho) →
      (∀ e ∈ leave,
        n ^ focusCandidateNum q r rho ≤
          (reserveCandidates n q r host e).card ^ focusCandidateDen rho) →
      Nonempty (CoverAssignment n q r leave host) := by
  have hdegree := eventually_focusLeave_degree_le hrho
  have hlegal := eventually_focus_legalLowerBound hr hrq hrho
  have hquant := eventually_focus_quantitative_bound hr hrq hrho
  have hcard := eventually_focus_exponential_union_bound
    (q := q) (r := r) hrho
  filter_upwards [hdegree, hlegal, hquant, hcard] with
      n hdegree hlegal hquant hcard
  intro leave host hleaveUniform hhostUniform hleavePower hcandidates
  apply exists_coverAssignment_of_finite_bounds hr hrq leave host
    hleaveUniform hhostUniform (D := focusLeaveCap rho n)
    (A := focusCandidateLower q r rho n)
    (C := focusSpentCap q r rho n)
  · intro J hJ
    exact hdegree (Reserve.localDegree leave J) (hleavePower J hJ)
  · intro e he
    exact focusCandidateLower_le_of_power hrq (by omega : 0 < rho)
      (hcandidates e he)
  · exact hlegal.1
  · exact hquant
  · exact hcard

/-- Apply the preceding cover theorem to the abundant random-rotation
family produced by a fixed pruned generator sample. -/
theorem eventually_exists_prunedGenerator_focusCover
    (N q r d rho : ℕ) (hr : 1 < r) (hrq : r < q)
    (hqd : Nat.choose q r < d)
    (hmd : (coverPattern q r).freeEdges.card < d)
    (hcross : (3 * rho) * (coverPattern q r).freeEdges.card < d)
    (hrho : 1 < rho) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (hn : 0 < n)
        (omegaSample : {e // e ∈ uniformEdges n r} → Bool)
        (D : Erdos722.Rotations.TwoCapPrunedData N n q r
          (Erdos722.GeneratorAsymptotic.generatorFaceCap d n)
          (Erdos722.GeneratorAsymptotic.generatorEdgeCap d n)
          (Erdos722.GeneratorAsymptotic.generatorPruneThreshold q r d n)
          (Erdos722.GeneratorAsymptotic.generatorFaceCliqueCap q r d n)
          (Erdos722.GeneratorAsymptotic.generatorEdgeCliqueCap q r d n))
        (leave : Finset (Finset (Fin n))),
      (∀ roots, ∀ hroots : roots ∈ rootFamilies n r (Nat.choose q r),
        commonMean n roots (reserveProbabilityIcc n d hn) / 2 <
          Erdos722.Probability.finiteRandomSum
            (fun x ↦ commonNeighborIndicator n r roots (by omega)
              (root_card_of_mem_rootFamilies hroots) x) omegaSample ∧
        Erdos722.Probability.finiteRandomSum
            (fun x ↦ commonNeighborIndicator n r roots (by omega)
              (root_card_of_mem_rootFamilies hroots) x) omegaSample <
          2 * commonMean n roots (reserveProbabilityIcc n d hn)) →
      D.K = sampledEdges n r omegaSample →
      (uniformEdges n (r - 1)).card *
          Erdos722.GeneratorAsymptotic.generatorDegreeLower d n ≤
        2 * D.Kstar.card * Nat.choose r (r - 1) →
      (∀ e ∈ leave, e.card = r) →
      (∀ J : Finset (Fin n), J.card = r - 1 →
        (Reserve.localDegree leave J) ^ rho ≤
          2 ^ rho * n ^ focusLeaveNum rho) →
      ∃ choice : Fin (Erdos722.GeneratorAsymptotic.generatorEdgeCap d n) →
          Fin (coverPattern q r).freeEdges.card → Equiv.Perm (Fin n),
        Nonempty (CoverAssignment n q r leave
          (Erdos722.RotationAbundance.rotationUnionHost D.Kstar choice \
            leave)) := by
  let root := coverRoot q r
  let m := (coverPattern q r).freeEdges.card
  let edges : Fin m → Finset (Fin q) := fun i ↦
    (coverPattern q r).freeEdges.equivFin.symm i
  have hroot : root.card < q := by
    dsimp [root]
    rw [card_coverRoot hrq.le]
    exact hrq
  have hedges : ∀ i, (edges i).card = r := by
    intro i
    exact (mem_coverPattern_freeEdges_iff hrq.le).mp
      ((coverPattern q r).freeEdges.equivFin.symm i).2 |>.1
  have hproper : ∀ i, ((edges i) ∩ root).card < r := by
    intro i
    have hi := ((coverPattern q r).freeEdges.equivFin.symm i).2
    have hiData := (mem_coverPattern_freeEdges_iff hrq.le).mp hi
    have hinterLe : ((edges i) ∩ root).card ≤ r := by
      exact (Finset.card_le_card Finset.inter_subset_left).trans_eq hiData.1
    by_contra hnot
    have heq : ((edges i) ∩ root).card = r := by omega
    have hsub : edges i ⊆ root := by
      apply Finset.inter_eq_left.mp
      apply Finset.eq_of_subset_of_card_le Finset.inter_subset_left
      rw [heq]
      simpa [edges] using hiData.1.le
    exact hiData.2 (Finset.eq_of_subset_of_card_le hsub (by
      rw [card_coverRoot hrq.le, hiData.1]))
  have habundant :=
    Erdos722.RotationAbundance.eventually_exists_prunedGenerator_rootedRotationAbundantCover
      N q r d hr hrq hqd root hroot (by simpa [m] using hmd)
      edges hedges hproper
  have hclean :=
    Erdos722.RotationAbundance.eventually_clean_candidate_power_of_abundant_rotations
      (q := q) (r := r) (d := d) (m := m) (rho := rho)
      (Dloss := 3 * rho) (Kloss := 1) (Cdeg := 4)
      (by omega : 0 < r) hrq (by
        have hchoose : 0 < Nat.choose q r := Nat.choose_pos hrq.le
        omega) (by omega : 0 < rho)
      (by
        dsimp [m]
        exact (Nat.mul_le_mul_right (coverPattern q r).freeEdges.card
          (by omega : 2 * rho ≤ 3 * rho)).trans_lt hcross)
      (by simpa [m] using hcross)
      (by
        exact Nat.mul_pos (by positivity : 0 < 3 * rho) (by omega))
  have hfocus := eventually_exists_focusCoverAssignment_of_power_bounds
    (q := q) (r := r) (rho := rho) (by omega) hrq hrho
  have hdegree := eventually_focusLeave_degree_le hrho
  filter_upwards [habundant, hclean, hfocus, hdegree] with
      n habundant hclean hfocus hdegree
  intro hn omegaSample D leave htyp hDK hmass hleaveUniform hleavePower
  obtain ⟨choice, hchoice⟩ := habundant hn omegaSample D htyp hDK hmass
  refine ⟨choice, ?_⟩
  apply hfocus leave
    (Erdos722.RotationAbundance.rotationUnionHost D.Kstar choice \ leave)
    hleaveUniform
  · intro a ha
    have haUnion := (Finset.mem_sdiff.mp ha).1
    obtain ⟨t, _ht, haGroup⟩ := Finset.mem_biUnion.mp haUnion
    obtain ⟨i, _hi, hai⟩ := Finset.mem_biUnion.mp haGroup
    have hpre : Erdos722.Rotations.rotateEdge (choice t i).symm a ∈ D.Kstar :=
      Erdos722.Rotations.mem_rotateFamily.mp hai
    have hcard := D.uniform _ (D.Kstar_subset hpre)
    exact (Erdos722.Rotations.rotateEdge_card (choice t i).symm a).symm.trans hcard
  · exact hleavePower
  · intro e he
    have hecard := hleaveUniform e he
    have hene : e.Nonempty := Finset.card_pos.mp (by omega)
    let : Nonempty (Fin n) := ⟨hene.choose⟩
    obtain ⟨request, hrequest⟩ := exists_rootRequest_with_image root e (by
      dsimp [root]
      rw [card_coverRoot hrq.le, hecard])
    obtain ⟨t, ht⟩ := hchoice request
    apply hclean (Erdos722.GeneratorAsymptotic.generatorEdgeCap d n)
      D.Kstar leave choice request e t (focusLeaveCap rho n) (by
        simpa [uniformEdges] using hmass)
    · simpa [m, edges, Erdos722.RotationAbundance.card_successfulRootedEmbeddings]
        using ht
    · exact hleaveUniform
    · intro J hJ
      exact hdegree (Reserve.localDegree leave J) (hleavePower J hJ)
    · exact focusLeaveCap_pow_le (by omega : 0 < rho) n
    · simpa [root] using hrequest

end

end Erdos722.ReserveFocusingAsymptotic
