/-
Copyright 2026 The Lean-Proofs Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import ErdosProblems.Erdos722.Asymptotics
import ErdosProblems.Erdos722.CoverClique
import Mathlib

/-!
# Scalar parameters for the reserve cover

This file clears all fractional exponents with
`d = (6 * choose q r)^2`.  The three thresholds below correspond to the
reserve candidate count, the nibble leave degree, and the allowed spent-edge
load respectively.
-/

namespace Erdos722.CoverAsymptotic

open Finset Filter
open scoped Topology Real
open Erdos722.Asymptotics
open Erdos722.Reserve
open Erdos722.RootedEmbedding
open Erdos722.RootSchedule
open Erdos722.CoverEmbedding
open Erdos722.CoverClique
open Erdos722.Cover

noncomputable section

def coverK (q r : ℕ) : ℕ := Nat.choose q r
def coverDen (q r : ℕ) : ℕ := (6 * coverK q r) ^ 2
def coverCandidateNumerator (q r : ℕ) : ℕ :=
  coverDen q r * (q - r) - coverK q r
def coverLeaveNumerator (q r : ℕ) : ℕ :=
  coverDen q r - 3 * coverK q r
def coverLoadNumerator (q r : ℕ) : ℕ :=
  coverDen q r - 2 * coverK q r

def coverScheduleConstant (q r : ℕ) : ℕ :=
  2 ^ (r - 1) * (2 ^ q * r ^ r)

def coverLoadMultiplier (q r : ℕ) : ℕ :=
  32 * coverScheduleConstant q r

def coverDenominatorConstant (q r : ℕ) : ℕ :=
  coverMeetingConstant q r * 2 ^ q * coverLoadMultiplier q r

def coverCandidateLower (q r n : ℕ) : ℕ :=
  rationalPowerThreshold (coverCandidateNumerator q r) (coverDen q r) n

def coverLeaveCap (q r n : ℕ) : ℕ :=
  rationalPowerThreshold (coverLeaveNumerator q r) (coverDen q r) n

def coverSpentCap (q r n : ℕ) : ℕ :=
  coverLoadMultiplier q r *
    rationalPowerThreshold (coverLoadNumerator q r) (coverDen q r) n

def coverCandidateExponent (q r : ℕ) : ℝ :=
  (coverCandidateNumerator q r : ℝ) / coverDen q r

def coverLeaveExponent (q r : ℕ) : ℝ :=
  (coverLeaveNumerator q r : ℝ) / coverDen q r

def coverLoadExponent (q r : ℕ) : ℝ :=
  (coverLoadNumerator q r : ℝ) / coverDen q r

lemma coverK_pos (hrq : r ≤ q) : 0 < coverK q r := by
  exact Nat.choose_pos hrq

lemma coverDen_pos (hrq : r ≤ q) : 0 < coverDen q r := by
  have hK := coverK_pos hrq
  unfold coverDen
  exact pow_pos (mul_pos (by norm_num) hK) _

lemma three_mul_coverK_lt_coverDen (hr : 0 < r) (hrq : r < q) :
    3 * coverK q r < coverDen q r := by
  have hK := coverK_pos hrq.le
  dsimp [coverDen]
  nlinarith

lemma coverCandidateNumerator_pos (hr : 0 < r) (hrq : r < q) :
    0 < coverCandidateNumerator q r := by
  have hK := coverK_pos hrq.le
  have hD := three_mul_coverK_lt_coverDen hr hrq
  have hqr : 1 ≤ q - r := by omega
  apply Nat.sub_pos_of_lt
  exact (by omega : coverK q r < coverDen q r).trans_le
    (Nat.le_mul_of_pos_right (coverDen q r) hqr)

lemma coverLeaveNumerator_pos (hr : 0 < r) (hrq : r < q) :
    0 < coverLeaveNumerator q r := by
  dsimp [coverLeaveNumerator]
  exact Nat.sub_pos_of_lt (three_mul_coverK_lt_coverDen hr hrq)

lemma coverLoadNumerator_pos (hr : 0 < r) (hrq : r < q) :
    0 < coverLoadNumerator q r := by
  have h := three_mul_coverK_lt_coverDen hr hrq
  dsimp [coverLoadNumerator]
  omega

lemma cover_exponent_identities (hr : 0 < r) (hrq : r < q) :
    let d := coverDen q r
    let K := coverK q r
    let a := (coverCandidateNumerator q r : ℝ) / d
    let δ := (coverLeaveNumerator q r : ℝ) / d
    let c := (coverLoadNumerator q r : ℝ) / d
    a = (q - r : ℕ) - (K : ℝ) / d ∧
      δ = 1 - 3 * (K : ℝ) / d ∧
      c = 1 - 2 * (K : ℝ) / d ∧
      (q - r : ℕ) + δ - a = c ∧
      (q - r - 1 : ℕ) + c < a := by
  dsimp
  have hD := coverDen_pos hrq.le
  have h3 := three_mul_coverK_lt_coverDen hr hrq
  have hq : 1 ≤ q - r := by omega
  have hsubA : coverK q r ≤ coverDen q r * (q - r) :=
    (by omega : coverK q r ≤ coverDen q r).trans
      (Nat.le_mul_of_pos_right (coverDen q r) hq)
  have hsubD : 3 * coverK q r ≤ coverDen q r := by omega
  have hsubC : 2 * coverK q r ≤ coverDen q r := by omega
  have hdR : (coverDen q r : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  have hcastA : (coverCandidateNumerator q r : ℝ) =
      (coverDen q r : ℝ) * (q - r : ℕ) - coverK q r := by
    rw [coverCandidateNumerator, Nat.cast_sub hsubA]
    push_cast
    rfl
  have hcastD : (coverLeaveNumerator q r : ℝ) =
      (coverDen q r : ℝ) - 3 * coverK q r := by
    rw [coverLeaveNumerator, Nat.cast_sub hsubD]
    push_cast
    rfl
  have hcastC : (coverLoadNumerator q r : ℝ) =
      (coverDen q r : ℝ) - 2 * coverK q r := by
    rw [coverLoadNumerator, Nat.cast_sub hsubC]
    push_cast
    rfl
  have ha : (coverCandidateNumerator q r : ℝ) / coverDen q r =
      (q - r : ℕ) - (coverK q r : ℝ) / coverDen q r := by
    rw [hcastA]
    field_simp
  have hδ : (coverLeaveNumerator q r : ℝ) / coverDen q r =
      1 - 3 * (coverK q r : ℝ) / coverDen q r := by
    rw [hcastD]
    field_simp
  have hc : (coverLoadNumerator q r : ℝ) / coverDen q r =
      1 - 2 * (coverK q r : ℝ) / coverDen q r := by
    rw [hcastC]
    field_simp
  refine ⟨ha, hδ, hc, ?_, ?_⟩
  · rw [ha, hδ, hc]
    ring
  · rw [ha, hc]
    rw [Nat.cast_sub hq]
    have hKR : (0 : ℝ) < coverK q r := by
      exact_mod_cast coverK_pos hrq.le
    have hDR : (0 : ℝ) < coverDen q r := by exact_mod_cast hD
    have hKD : (0 : ℝ) < (coverK q r : ℝ) / coverDen q r :=
      div_pos hKR hDR
    norm_num
    have htwo : (2 : ℝ) * coverK q r / coverDen q r =
        2 * ((coverK q r : ℝ) / coverDen q r) := by ring
    rw [htwo]
    linarith

/-- The power-cleared reserve conclusion implies the natural candidate
lower bound chosen above. -/
lemma coverCandidateLower_le_of_power
    (hr : 0 < r) (hrq : r < q) {n x : ℕ}
    (h : n ^ coverCandidateNumerator q r ≤ x ^ coverDen q r) :
    coverCandidateLower q r n ≤ x := by
  exact rationalPowerThreshold_le_of_power_lower _ _ _ _
    (coverDen_pos hrq.le) h

/-- The power-cleared nibble conclusion implies the natural leave cap. -/
lemma le_coverLeaveCap_of_power
    (hr : 0 < r) (hrq : r < q) {n x : ℕ}
    (h : x ^ coverDen q r ≤ n ^ coverLeaveNumerator q r) :
    x ≤ coverLeaveCap q r n := by
  exact le_rationalPowerThreshold_of_pow_le _ _ _ _
    (coverDen_pos hrq.le) h

lemma eventually_half_candidate_rpow_le
    (hr : 0 < r) (hrq : r < q) :
    ∀ᶠ n : ℕ in atTop,
      (n : ℝ) ^ coverCandidateExponent q r / 2 ≤
        (coverCandidateLower q r n : ℝ) := by
  simpa [coverCandidateExponent, coverCandidateLower] using
    (eventually_half_rpow_le_rationalPowerThreshold
      (coverCandidateNumerator_pos hr hrq) (coverDen_pos hrq.le))

lemma coverCandidateLower_cast_le (q r n : ℕ) :
    (coverCandidateLower q r n : ℝ) ≤
      (n : ℝ) ^ coverCandidateExponent q r := by
  exact rationalPowerThreshold_cast_le _ _ _

lemma coverLeaveCap_cast_le (q r n : ℕ) :
    (coverLeaveCap q r n : ℝ) ≤
      (n : ℝ) ^ coverLeaveExponent q r := by
  exact rationalPowerThreshold_cast_le _ _ _

lemma coverSpentCap_cast_le (q r n : ℕ) :
    (coverSpentCap q r n : ℝ) ≤
      coverLoadMultiplier q r * (n : ℝ) ^ coverLoadExponent q r := by
  rw [coverSpentCap]
  push_cast
  exact mul_le_mul_of_nonneg_left
    (rationalPowerThreshold_cast_le _ _ _) (Nat.cast_nonneg _)

lemma eventually_half_load_rpow_mul_le_spentCap
    (hr : 0 < r) (hrq : r < q) :
    ∀ᶠ n : ℕ in atTop,
      (coverLoadMultiplier q r : ℝ) *
          ((n : ℝ) ^ coverLoadExponent q r / 2) ≤
        (coverSpentCap q r n : ℝ) := by
  have h := eventually_half_rpow_le_rationalPowerThreshold
    (coverLoadNumerator_pos hr hrq) (coverDen_pos hrq.le)
  filter_upwards [h] with n hn
  rw [coverSpentCap]
  push_cast
  exact mul_le_mul_of_nonneg_left hn (Nat.cast_nonneg _)

lemma codim_cover_cast_le
    (hr : 0 < r) (hrq : r < q) (n : ℕ) (hn : 1 ≤ n) :
    (codimOneMeetingBound (coverPattern q r) n
        ((coverPattern q r).freeEdges.card * coverSpentCap q r n) : ℝ) ≤
      coverDenominatorConstant q r *
        (n : ℝ) ^ ((q - r - 1 : ℕ) + coverLoadExponent q r) := by
  let T := rationalPowerThreshold (coverLoadNumerator q r) (coverDen q r) n
  have hnat := codimOneMeetingBound_coverPattern_le hr hrq n
    ((coverPattern q r).freeEdges.card * coverSpentCap q r n)
  have hfree := card_coverPattern_freeEdges_le (q := q) (r := r)
  have hupperNat :
      codimOneMeetingBound (coverPattern q r) n
          ((coverPattern q r).freeEdges.card * coverSpentCap q r n) ≤
        coverDenominatorConstant q r * T * n ^ (q - r - 1) := by
    calc
      codimOneMeetingBound (coverPattern q r) n
          ((coverPattern q r).freeEdges.card * coverSpentCap q r n) ≤
          coverMeetingConstant q r *
            ((coverPattern q r).freeEdges.card * coverSpentCap q r n) *
              n ^ (q - r - 1) := hnat
      _ ≤ coverMeetingConstant q r *
            ((2 ^ q) * coverSpentCap q r n) * n ^ (q - r - 1) := by
        exact Nat.mul_le_mul_right _
          (Nat.mul_le_mul_left _
            (Nat.mul_le_mul_right (coverSpentCap q r n) hfree))
      _ = coverDenominatorConstant q r * T * n ^ (q - r - 1) := by
        unfold coverSpentCap coverDenominatorConstant
        dsimp [T]
        ring
  have hupperReal :
      (codimOneMeetingBound (coverPattern q r) n
          ((coverPattern q r).freeEdges.card * coverSpentCap q r n) : ℝ) ≤
        (coverDenominatorConstant q r : ℝ) * (T : ℝ) *
          (n : ℝ) ^ (q - r - 1) := by
    exact_mod_cast hupperNat
  have hT : (T : ℝ) ≤ (n : ℝ) ^ coverLoadExponent q r := by
    exact rationalPowerThreshold_cast_le _ _ _
  calc
    (codimOneMeetingBound (coverPattern q r) n
        ((coverPattern q r).freeEdges.card * coverSpentCap q r n) : ℝ) ≤
        (coverDenominatorConstant q r : ℝ) * (T : ℝ) *
          (n : ℝ) ^ (q - r - 1) := hupperReal
    _ ≤ (coverDenominatorConstant q r : ℝ) *
          (n : ℝ) ^ coverLoadExponent q r *
            (n : ℝ) ^ (q - r - 1) := by gcongr
    _ = coverDenominatorConstant q r *
        (n : ℝ) ^ ((q - r - 1 : ℕ) + coverLoadExponent q r) := by
      have hnpos : (0 : ℝ) < n := by positivity
      calc
        (coverDenominatorConstant q r : ℝ) *
              (n : ℝ) ^ coverLoadExponent q r *
                (n : ℝ) ^ (q - r - 1) =
            (coverDenominatorConstant q r : ℝ) *
              ((n : ℝ) ^ coverLoadExponent q r *
                (n : ℝ) ^ (q - r - 1 : ℕ)) := by ring
        _ = (coverDenominatorConstant q r : ℝ) *
              (n : ℝ) ^ (coverLoadExponent q r +
                (q - r - 1 : ℕ)) := by
          rw [← Real.rpow_natCast]
          rw [Real.rpow_add hnpos]
        _ = (coverDenominatorConstant q r : ℝ) *
              (n : ℝ) ^ ((q - r - 1 : ℕ) +
                coverLoadExponent q r) := by
          congr 2
          ring

/-- Eventually the spent-edge overlap removes at most one quarter of the
reserve candidate scale, leaving a positive denominator of the same
polynomial order. -/
theorem eventually_cover_legalLowerBound
    (hr : 0 < r) (hrq : r < q) :
    ∀ᶠ n : ℕ in atTop,
      0 < reserveLegalLowerBound (coverPattern q r) n
          (coverCandidateLower q r n) (coverSpentCap q r n) ∧
      (n : ℝ) ^ coverCandidateExponent q r / 4 ≤
        (reserveLegalLowerBound (coverPattern q r) n
          (coverCandidateLower q r n) (coverSpentCap q r n) : ℝ) := by
  have hexp := cover_exponent_identities hr hrq
  have hgap : (q - r - 1 : ℕ) + coverLoadExponent q r <
      coverCandidateExponent q r := by
    simpa [coverCandidateExponent, coverLoadExponent] using hexp.2.2.2.2
  have hdom := eventually_const_mul_rpow_le_rpow
    (C := (4 * coverDenominatorConstant q r : ℕ)) hgap (by positivity)
  have hcand := eventually_half_candidate_rpow_le hr hrq
  filter_upwards [hdom, hcand, eventually_ge_atTop (1 : ℕ)] with
      n hdom hcand hn
  let loss := codimOneMeetingBound (coverPattern q r) n
    ((coverPattern q r).freeEdges.card * coverSpentCap q r n)
  let A := coverCandidateLower q r n
  have hlossRaw := codim_cover_cast_le hr hrq n hn
  have hloss : (loss : ℝ) ≤
      (n : ℝ) ^ coverCandidateExponent q r / 4 := by
    have hscaled : (4 : ℝ) *
          ((coverDenominatorConstant q r : ℝ) *
            (n : ℝ) ^ ((q - r - 1 : ℕ) + coverLoadExponent q r)) ≤
        (n : ℝ) ^ coverCandidateExponent q r := by
      calc
        (4 : ℝ) * ((coverDenominatorConstant q r : ℝ) *
            (n : ℝ) ^ ((q - r - 1 : ℕ) + coverLoadExponent q r)) =
          (4 * coverDenominatorConstant q r : ℕ) *
            (n : ℝ) ^ ((q - r - 1 : ℕ) + coverLoadExponent q r) := by
              push_cast
              ring
        _ ≤ _ := hdom
    change (loss : ℝ) ≤ coverDenominatorConstant q r *
      (n : ℝ) ^ ((q - r - 1 : ℕ) + coverLoadExponent q r) at hlossRaw
    linarith
  have hpowPos : 0 < (n : ℝ) ^ coverCandidateExponent q r := by positivity
  have hlossAReal : (loss : ℝ) < A := by
    dsimp [A]
    have hcand' : (n : ℝ) ^ coverCandidateExponent q r / 2 ≤
        (coverCandidateLower q r n : ℝ) := hcand
    linarith
  have hlossA : loss < A := by exact_mod_cast hlossAReal
  have hpos : 0 < A - loss := Nat.sub_pos_of_lt hlossA
  have hcastSub : ((A - loss : ℕ) : ℝ) = (A : ℝ) - loss := by
    rw [Nat.cast_sub hlossA.le]
  constructor
  · simpa [reserveLegalLowerBound, A, loss] using hpos
  · rw [reserveLegalLowerBound]
    change (n : ℝ) ^ coverCandidateExponent q r / 4 ≤
      ((A - loss : ℕ) : ℝ)
    rw [hcastSub]
    dsimp [A]
    linarith

/-- The scheduled face numerator divided by the legal denominator is small
enough for the Chernoff exponent at `t=1`. -/
theorem eventually_cover_quantitative_bound
    (hr : 0 < r) (hrq : r < q) :
    ∀ᶠ n : ℕ in atTop,
      (Real.exp 1 - 1) *
          ((faceScheduleNumeratorBound (coverPattern q r) n
              (coverLeaveCap q r n) : ℝ) /
            reserveLegalLowerBound (coverPattern q r) n
              (coverCandidateLower q r n) (coverSpentCap q r n)) ≤
        (coverSpentCap q r n : ℝ) / 2 := by
  have hlegal := eventually_cover_legalLowerBound hr hrq
  have hcap := eventually_half_load_rpow_mul_le_spentCap hr hrq
  filter_upwards [hlegal, hcap, eventually_ge_atTop (1 : ℕ)] with
      n hlegal hcap hn
  let L := reserveLegalLowerBound (coverPattern q r) n
    (coverCandidateLower q r n) (coverSpentCap q r n)
  let B := faceScheduleNumeratorBound (coverPattern q r) n
    (coverLeaveCap q r n)
  let a := coverCandidateExponent q r
  let δ := coverLeaveExponent q r
  let c := coverLoadExponent q r
  let S := coverScheduleConstant q r
  have hids := cover_exponent_identities hr hrq
  have hac : (q - r : ℕ) + δ = a + c := by
    have hid := hids.2.2.2.1
    change (q - r : ℕ) + δ - a = c at hid
    linarith
  have hD := coverLeaveCap_cast_le q r n
  have hnpos : (0 : ℝ) < n := by positivity
  have hB : (B : ℝ) ≤ (S : ℝ) * (n : ℝ) ^ (a + c) := by
    dsimp [B, S]
    rw [faceScheduleNumeratorBound_coverPattern hrq.le]
    push_cast
    calc
      (2 : ℝ) ^ (r - 1) * ((2 : ℝ) ^ q * (r : ℝ) ^ r) *
            (n : ℝ) ^ (q - r) * (coverLeaveCap q r n : ℝ) ≤
          (coverScheduleConstant q r : ℝ) *
            (n : ℝ) ^ (q - r) * (n : ℝ) ^ δ := by
        dsimp [coverScheduleConstant, δ]
        push_cast
        gcongr
      _ = (coverScheduleConstant q r : ℝ) *
            (n : ℝ) ^ ((q - r : ℕ) + δ) := by
        rw [← Real.rpow_natCast, Real.rpow_add hnpos]
        ring
      _ = (coverScheduleConstant q r : ℝ) *
            (n : ℝ) ^ (a + c) := by rw [hac]
  have hLposReal : (0 : ℝ) < L := by
    exact_mod_cast hlegal.1
  have hLlower : (n : ℝ) ^ a / 4 ≤ (L : ℝ) := by
    simpa [L, a] using hlegal.2
  have hpowApos : 0 < (n : ℝ) ^ a := by positivity
  have hratio : (B : ℝ) / L ≤
      (4 * S : ℕ) * (n : ℝ) ^ c := by
    apply (div_le_iff₀ hLposReal).2
    calc
      (B : ℝ) ≤ (S : ℝ) * (n : ℝ) ^ (a + c) := hB
      _ = (S : ℝ) * ((n : ℝ) ^ a * (n : ℝ) ^ c) := by
        rw [Real.rpow_add hnpos]
      _ ≤ (S : ℝ) * ((4 : ℝ) * L * (n : ℝ) ^ c) := by
        gcongr
        linarith
      _ = ((4 * S : ℕ) : ℝ) * (n : ℝ) ^ c * L := by
        push_cast
        ring
  have hexpCoef : Real.exp 1 - 1 ≤ 2 := by
    linarith [Real.exp_one_lt_d9]
  have hleft : (Real.exp 1 - 1) * ((B : ℝ) / L) ≤
      (8 * S : ℕ) * (n : ℝ) ^ c := by
    calc
      (Real.exp 1 - 1) * ((B : ℝ) / L) ≤
          2 * (((4 * S : ℕ) : ℝ) * (n : ℝ) ^ c) := by
        exact mul_le_mul hexpCoef hratio (by positivity) (by norm_num)
      _ = ((8 * S : ℕ) : ℝ) * (n : ℝ) ^ c := by
        push_cast
        ring
  have hright : ((8 * S : ℕ) : ℝ) * (n : ℝ) ^ c ≤
      (coverSpentCap q r n : ℝ) / 2 := by
    have hcap' : (coverLoadMultiplier q r : ℝ) *
          ((n : ℝ) ^ c / 2) ≤ (coverSpentCap q r n : ℝ) := by
      simpa [c] using hcap
    have hM : coverLoadMultiplier q r = 32 * S := by
      rfl
    rw [hM] at hcap'
    push_cast at hcap'
    calc
      ((8 * S : ℕ) : ℝ) * (n : ℝ) ^ c =
          (32 * (S : ℝ) * ((n : ℝ) ^ c / 2)) / 2 := by
            push_cast
            ring
      _ ≤ (coverSpentCap q r n : ℝ) / 2 := by gcongr
  change (Real.exp 1 - 1) * ((B : ℝ) / L) ≤
    (coverSpentCap q r n : ℝ) / 2
  exact hleft.trans hright

/-- The polynomially many face counters are dominated by the exponential
tail coming from the scheduled load cap. -/
theorem eventually_cover_exponential_union_bound
    (hr : 0 < r) (hrq : r < q) :
    ∀ᶠ n : ℕ in atTop,
      (Fintype.card (RelevantFaceLoadTarget (coverPattern q r) n) : ℝ) *
          Real.exp (-(coverSpentCap q r n : ℝ) / 2) < 1 := by
  let c := coverLoadExponent q r
  let M := coverLoadMultiplier q r
  let C₀ : ℝ := 2 ^ q
  have hc : 0 < c := by
    dsimp [c, coverLoadExponent]
    exact div_pos (by exact_mod_cast coverLoadNumerator_pos hr hrq)
      (by exact_mod_cast coverDen_pos hrq.le)
  have hM : 0 < (M : ℝ) := by
    dsimp [M, coverLoadMultiplier, coverScheduleConstant]
    positivity
  have hdecay := tendsto_pow_mul_exp_neg_rpow_atTop (r - 1) hc
    (show (0 : ℝ) < (M : ℝ) / 4 by positivity)
  have hconst : Tendsto
      (fun x : ℝ ↦ C₀ *
        (x ^ (r - 1) * Real.exp (-((M : ℝ) / 4) * x ^ c)))
      atTop (nhds 0) := by
    have hC₀ : Tendsto (fun _ : ℝ ↦ C₀) atTop (nhds C₀) :=
      tendsto_const_nhds
    simpa only [mul_zero] using hC₀.mul hdecay
  have hnat := hconst.comp tendsto_natCast_atTop_atTop
  have hsmall : ∀ᶠ n : ℕ in atTop,
      C₀ * ((n : ℝ) ^ (r - 1) *
        Real.exp (-((M : ℝ) / 4) * (n : ℝ) ^ c)) < 1 :=
    (tendsto_order.1 hnat).2 _ (by norm_num)
  have hcap := eventually_half_load_rpow_mul_le_spentCap hr hrq
  filter_upwards [hsmall, hcap] with n hnsmall hcap
  have hcardNat :
      Fintype.card (RelevantFaceLoadTarget (coverPattern q r) n) ≤
        2 ^ q * n ^ (r - 1) := by
    calc
      Fintype.card (RelevantFaceLoadTarget (coverPattern q r) n) ≤
          (coverPattern q r).freeEdges.card * Nat.choose n (r - 1) :=
        card_relevantFaceLoadTarget_le _ _
      _ ≤ 2 ^ q * n ^ (r - 1) :=
        Nat.mul_le_mul card_coverPattern_freeEdges_le (Nat.choose_le_pow _ _)
  have hcardReal :
      (Fintype.card (RelevantFaceLoadTarget (coverPattern q r) n) : ℝ) ≤
        (2 ^ q : ℕ) * (n : ℝ) ^ (r - 1) := by
    exact_mod_cast hcardNat
  have hspent : (M : ℝ) / 4 * (n : ℝ) ^ c ≤
      (coverSpentCap q r n : ℝ) / 2 := by
    calc
      (M : ℝ) / 4 * (n : ℝ) ^ c =
          ((M : ℝ) * ((n : ℝ) ^ c / 2)) / 2 := by ring
      _ ≤ (coverSpentCap q r n : ℝ) / 2 := by
        simpa [M, c] using div_le_div_of_nonneg_right hcap (by norm_num : (0 : ℝ) ≤ 2)
  calc
    (Fintype.card (RelevantFaceLoadTarget (coverPattern q r) n) : ℝ) *
          Real.exp (-(coverSpentCap q r n : ℝ) / 2) ≤
        ((2 ^ q : ℕ) : ℝ) * (n : ℝ) ^ (r - 1) *
          Real.exp (-(coverSpentCap q r n : ℝ) / 2) := by
      gcongr
    _ ≤ ((2 ^ q : ℕ) : ℝ) * (n : ℝ) ^ (r - 1) *
          Real.exp (-((M : ℝ) / 4) * (n : ℝ) ^ c) := by
      gcongr
      convert neg_le_neg hspent using 1 <;> ring
    _ = C₀ * ((n : ℝ) ^ (r - 1) *
          Real.exp (-((M : ℝ) / 4) * (n : ℝ) ^ c)) := by
      dsimp [C₀]
      push_cast
      ring
    _ < 1 := hnsmall

/-- For all sufficiently large `n`, the power-cleared candidate and leave
degree estimates imply the full reserve-cover conclusion.  This is the
asymptotic form consumed by the absorption assembly. -/
theorem eventually_exists_coverAssignment_of_power_bounds
    (hr : 0 < r) (hrq : r < q) :
    ∀ᶠ n : ℕ in atTop, ∀ (leave reserve : Finset (Finset (Fin n))),
      (∀ e ∈ leave, e.card = r) →
      (∀ e ∈ reserve, e.card = r) →
      (∀ J : Finset (Fin n), J.card = r - 1 →
        (Reserve.localDegree leave J) ^ coverDen q r ≤
          n ^ coverLeaveNumerator q r) →
      (∀ e ∈ leave,
        n ^ coverCandidateNumerator q r ≤
          (reserveCandidates n q r reserve e).card ^ coverDen q r) →
      Nonempty (CoverAssignment n q r leave reserve) := by
  have hlegal := eventually_cover_legalLowerBound hr hrq
  have hquant := eventually_cover_quantitative_bound hr hrq
  have hcard := eventually_cover_exponential_union_bound hr hrq
  filter_upwards [hlegal, hquant, hcard] with n hlegal hquant hcard
  intro leave reserve hleaveUniform hreserveUniform hdegree hcandidates
  apply exists_coverAssignment_of_finite_bounds hr hrq leave reserve
    hleaveUniform hreserveUniform
  · intro J hJ
    exact le_coverLeaveCap_of_power hr hrq (hdegree J hJ)
  · intro e he
    exact coverCandidateLower_le_of_power hr hrq (hcandidates e he)
  · exact hlegal.1
  · exact hquant
  · exact hcard

end

end Erdos722.CoverAsymptotic
