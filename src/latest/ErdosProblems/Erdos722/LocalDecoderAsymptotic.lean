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
import ErdosProblems.Erdos722.LocalDecoderEmbedding
import ErdosProblems.Erdos722.Asymptotics
import Mathlib

/-!
# Asymptotic simultaneous placement of local decoders

If the root/forbidden `r`-graph has codimension-one degree
`O(n^(1-1/d))`, the rooted random-greedy theorem places one fixed complete
rooted hypergraph at each edge while using only `O(n^(1-1/(2d)))` new
edges through any lower face.  This file clears those two rational powers
with natural thresholds.
-/

namespace Erdos722.LocalDecoderAsymptotic

open Finset Filter
open scoped Topology Real
open Erdos722.Typicality
open Erdos722.Reserve
open Erdos722.RootedEmbedding
open Erdos722.RootSchedule
open Erdos722.CoverClique
open Erdos722.Asymptotics
open Erdos722.LocalDecoderEmbedding

noncomputable section

/-- Input codimension-one degree threshold `n^(1-1/d)`. -/
def decoderInputCap (d n : ℕ) : ℕ :=
  rationalPowerThreshold (d - 1) d n

/-- Larger stopping cap `n^(1-1/(2d))` used for the newly placed edges. -/
def decoderPathScale (d n : ℕ) : ℕ :=
  rationalPowerThreshold (2 * d - 1) (2 * d) n

def decoderScheduleConstant (v r : ℕ) : ℕ :=
  2 ^ (r - 1) * (2 ^ v * r ^ r)

def decoderBaselineConstant (v r : ℕ) : ℕ :=
  2 ^ (v - r)

/-- A deliberately generous fixed multiplier, absorbing the schedule
numerator and the `e-1<2` Chernoff coefficient. -/
def decoderPathMultiplier (v r : ℕ) : ℕ :=
  16 * decoderBaselineConstant v r * decoderScheduleConstant v r

def decoderPathCap (v r d n : ℕ) : ℕ :=
  decoderPathMultiplier v r * decoderPathScale d n

def decoderInputExponent (d : ℕ) : ℝ :=
  ((d - 1 : ℕ) : ℝ) / d

def decoderPathExponent (d : ℕ) : ℝ :=
  ((2 * d - 1 : ℕ) : ℝ) / (2 * d : ℕ)

def decoderUsedConstant (v r : ℕ) : ℕ :=
  coverMeetingConstant v r * 2 ^ v * decoderPathMultiplier v r

lemma decoderInputCap_pow_le (d n : ℕ) (hd : 0 < d) :
    (decoderInputCap d n) ^ d ≤ n ^ (d - 1) := by
  exact rationalPowerThreshold_pow_le _ _ _ hd

lemma decoderPathScale_pow_le (d n : ℕ) (hd : 0 < d) :
    (decoderPathScale d n) ^ (2 * d) ≤ n ^ (2 * d - 1) := by
  exact rationalPowerThreshold_pow_le _ _ _ (Nat.mul_pos (by omega) hd)

lemma le_decoderInputCap_of_pow_le
    (d n x : ℕ) (hd : 0 < d) (h : x ^ d ≤ n ^ (d - 1)) :
    x ≤ decoderInputCap d n := by
  exact le_rationalPowerThreshold_of_pow_le _ _ _ _ hd h

lemma decoderInputCap_cast_le (d n : ℕ) :
    (decoderInputCap d n : ℝ) ≤
      (n : ℝ) ^ (((d - 1 : ℕ) : ℝ) / d) :=
  rationalPowerThreshold_cast_le _ _ _

lemma decoderPathScale_cast_le (d n : ℕ) :
    (decoderPathScale d n : ℝ) ≤
      (n : ℝ) ^ (((2 * d - 1 : ℕ) : ℝ) / (2 * d : ℕ)) :=
  rationalPowerThreshold_cast_le _ _ _

lemma decoder_exponent_identities (hd : 0 < d) :
    decoderInputExponent d = 1 - (1 : ℝ) / d ∧
      decoderPathExponent d = 1 - (1 : ℝ) / (2 * d) ∧
      decoderInputExponent d < decoderPathExponent d ∧
      0 < decoderPathExponent d := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have h2dR : (0 : ℝ) < 2 * d := by positivity
  have hdsub : (d - 1 : ℕ) = d - 1 := by omega
  have h2dsub : (2 * d - 1 : ℕ) = 2 * d - 1 := by omega
  constructor
  · rw [decoderInputExponent, Nat.cast_sub (by omega : 1 ≤ d)]
    push_cast
    field_simp
  constructor
  · rw [decoderPathExponent, Nat.cast_sub (by omega : 1 ≤ 2 * d)]
    push_cast
    field_simp
  constructor
  · rw [decoderInputExponent, decoderPathExponent,
      Nat.cast_sub (by omega : 1 ≤ d),
      Nat.cast_sub (by omega : 1 ≤ 2 * d)]
    push_cast
    rw [div_lt_div_iff₀ hdR h2dR]
    nlinarith
  · rw [decoderPathExponent]
    exact div_pos
      (by exact_mod_cast (Nat.sub_pos_of_lt (by omega : 1 < 2 * d)))
      (by exact_mod_cast (Nat.mul_pos (by omega : 0 < 2) hd))

/-- The input cap may use a different exponent denominator from the path
cap.  The latter dominates exactly when `dInput < 2 * dPath`. -/
lemma decoderInputExponent_lt_decoderPathExponent
    {dInput dPath : ℕ}
    (hdInput : 0 < dInput) (hdPath : 0 < dPath)
    (hgap : dInput < 2 * dPath) :
    decoderInputExponent dInput < decoderPathExponent dPath := by
  rw [(decoder_exponent_identities hdInput).1,
    (decoder_exponent_identities hdPath).2.1]
  have hdInputR : (0 : ℝ) < dInput := by exact_mod_cast hdInput
  have hdPathR : (0 : ℝ) < 2 * dPath := by
    exact_mod_cast (Nat.mul_pos (by omega : 0 < 2) hdPath)
  have hgapR : (dInput : ℝ) < 2 * dPath := by exact_mod_cast hgap
  have hinv : (1 : ℝ) / (2 * dPath) < 1 / dInput := by
    exact one_div_lt_one_div_of_lt hdInputR hgapR
  linarith

lemma decoderPathMultiplier_pos (v r : ℕ) (hr : 0 < r) :
    0 < decoderPathMultiplier v r := by
  simp [decoderPathMultiplier, decoderBaselineConstant,
    decoderScheduleConstant, hr]

lemma decoderPathCap_pos_of_scale
    {v r d n : ℕ} (hr : 0 < r) (hscale : 0 < decoderPathScale d n) :
    0 < decoderPathCap v r d n := by
  exact Nat.mul_pos (decoderPathMultiplier_pos v r hr) hscale

/-- A falling-factorial baseline retains a fixed fraction of `n^s` once
all `s` selected vertices and all `r` roots fit below `n/2`. -/
lemma descFactorial_sub_cast_lower
    {n r s : ℕ} (hn : 2 * (r + s) ≤ n) :
    (n : ℝ) ^ s / (2 : ℝ) ^ s ≤
      ((n - r).descFactorial s : ℕ) := by
  rw [Nat.descFactorial_eq_prod_range]
  push_cast
  calc
    (n : ℝ) ^ s / (2 : ℝ) ^ s =
        ((n : ℝ) / 2) ^ s := by
      exact (div_pow (n : ℝ) 2 s).symm
    _ = ∏ _i ∈ Finset.range s, ((n : ℝ) / 2) := by
      rw [Finset.prod_const, Finset.card_range]
    _ ≤ ∏ i ∈ Finset.range s, (((n - r - i : ℕ) : ℝ)) := by
      apply Finset.prod_le_prod
      · intro i hi
        positivity
      · intro i hi
        have his : i < s := Finset.mem_range.mp hi
        have hnat : n ≤ 2 * (n - r - i) := by omega
        have hreal : (n : ℝ) ≤ 2 * ((n - r - i : ℕ) : ℝ) := by
          exact_mod_cast hnat
        linarith

lemma decoderMeetingBound_cast_le
    {n v r D : ℕ} (hr : 0 < r) (hrv : r < v) :
    (codimOneMeetingBound (coverPattern v r) n D : ℝ) ≤
      (coverMeetingConstant v r : ℝ) * D *
        (n : ℝ) ^ (v - r - 1) := by
  exact_mod_cast codimOneMeetingBound_coverPattern_le hr hrv n D

lemma decoderScheduleNumerator_eq
    {n v r D : ℕ} (hrv : r ≤ v) :
    faceScheduleNumeratorBound (coverPattern v r) n D =
      decoderScheduleConstant v r * n ^ (v - r) * D := by
  simpa [decoderScheduleConstant] using
    faceScheduleNumeratorBound_coverPattern hrv n D

lemma decoderFixedMeeting_cast_le
    {n v r d : ℕ} (hr : 0 < r) (hrv : r < v) (hn : 1 ≤ n) :
    (codimOneMeetingBound (coverPattern v r) n
        (decoderInputCap d n) : ℝ) ≤
      (coverMeetingConstant v r : ℝ) *
        (n : ℝ) ^ ((v - r - 1 : ℕ) + decoderInputExponent d) := by
  have hraw := decoderMeetingBound_cast_le
    (n := n) (v := v) (r := r) (D := decoderInputCap d n) hr hrv
  have hD := decoderInputCap_cast_le d n
  have hnpos : (0 : ℝ) < n := by positivity
  calc
    (codimOneMeetingBound (coverPattern v r) n
        (decoderInputCap d n) : ℝ) ≤
        (coverMeetingConstant v r : ℝ) * (decoderInputCap d n : ℝ) *
          (n : ℝ) ^ (v - r - 1) := hraw
    _ ≤ (coverMeetingConstant v r : ℝ) *
          (n : ℝ) ^ decoderInputExponent d *
            (n : ℝ) ^ (v - r - 1) := by
      dsimp [decoderInputExponent]
      gcongr
    _ = (coverMeetingConstant v r : ℝ) *
        (n : ℝ) ^ ((v - r - 1 : ℕ) + decoderInputExponent d) := by
      rw [show (coverMeetingConstant v r : ℝ) *
          (n : ℝ) ^ decoderInputExponent d * (n : ℝ) ^ (v - r - 1) =
          (coverMeetingConstant v r : ℝ) *
            ((n : ℝ) ^ decoderInputExponent d *
              (n : ℝ) ^ (v - r - 1)) by ring]
      rw [← Real.rpow_natCast, ← Real.rpow_add hnpos]
      congr 2
      ring

lemma decoderUsedMeeting_cast_le
    {n v r d : ℕ} (hr : 0 < r) (hrv : r < v) (hn : 1 ≤ n) :
    (codimOneMeetingBound (coverPattern v r) n
        ((coverPattern v r).freeEdges.card * decoderPathCap v r d n) : ℝ) ≤
      (decoderUsedConstant v r : ℝ) *
        (n : ℝ) ^ ((v - r - 1 : ℕ) + decoderPathExponent d) := by
  let T := decoderPathScale d n
  have hnat := codimOneMeetingBound_coverPattern_le hr hrv n
    ((coverPattern v r).freeEdges.card * decoderPathCap v r d n)
  have hfree := card_coverPattern_freeEdges_le (q := v) (r := r)
  have hupperNat :
      codimOneMeetingBound (coverPattern v r) n
          ((coverPattern v r).freeEdges.card * decoderPathCap v r d n) ≤
        decoderUsedConstant v r * T * n ^ (v - r - 1) := by
    calc
      codimOneMeetingBound (coverPattern v r) n
          ((coverPattern v r).freeEdges.card * decoderPathCap v r d n) ≤
          coverMeetingConstant v r *
            ((coverPattern v r).freeEdges.card * decoderPathCap v r d n) *
              n ^ (v - r - 1) := hnat
      _ ≤ coverMeetingConstant v r *
            ((2 ^ v) * decoderPathCap v r d n) * n ^ (v - r - 1) := by
        exact Nat.mul_le_mul_right _
          (Nat.mul_le_mul_left _
            (Nat.mul_le_mul_right (decoderPathCap v r d n) hfree))
      _ = decoderUsedConstant v r * T * n ^ (v - r - 1) := by
        unfold decoderPathCap decoderUsedConstant
        dsimp [T]
        ring
  have hupperReal :
      (codimOneMeetingBound (coverPattern v r) n
          ((coverPattern v r).freeEdges.card * decoderPathCap v r d n) : ℝ) ≤
        (decoderUsedConstant v r : ℝ) * (T : ℝ) *
          (n : ℝ) ^ (v - r - 1) := by
    exact_mod_cast hupperNat
  have hT : (T : ℝ) ≤ (n : ℝ) ^ decoderPathExponent d := by
    exact decoderPathScale_cast_le d n
  have hnpos : (0 : ℝ) < n := by positivity
  calc
    (codimOneMeetingBound (coverPattern v r) n
        ((coverPattern v r).freeEdges.card * decoderPathCap v r d n) : ℝ) ≤
        (decoderUsedConstant v r : ℝ) * (T : ℝ) *
          (n : ℝ) ^ (v - r - 1) := hupperReal
    _ ≤ (decoderUsedConstant v r : ℝ) *
          (n : ℝ) ^ decoderPathExponent d *
            (n : ℝ) ^ (v - r - 1) := by gcongr
    _ = (decoderUsedConstant v r : ℝ) *
        (n : ℝ) ^ ((v - r - 1 : ℕ) + decoderPathExponent d) := by
      rw [show (decoderUsedConstant v r : ℝ) *
          (n : ℝ) ^ decoderPathExponent d * (n : ℝ) ^ (v - r - 1) =
          (decoderUsedConstant v r : ℝ) *
            ((n : ℝ) ^ decoderPathExponent d *
              (n : ℝ) ^ (v - r - 1)) by ring]
      rw [← Real.rpow_natCast, ← Real.rpow_add hnpos]
      congr 2
      ring

/-- Both forbidden-edge losses are eventually a small fixed fraction of
the falling-factorial baseline. -/
theorem eventually_decoder_legalLowerBound
    (hr : 0 < r) (hrv : r < v) (hd : 0 < d) :
    ∀ᶠ n : ℕ in atTop,
      0 < rootedFaceLegalLowerBound (coverPattern v r) n
          (decoderInputCap d n) (decoderPathCap v r d n) ∧
      (n : ℝ) ^ (v - r) /
          (2 * decoderBaselineConstant v r : ℕ) ≤
        (rootedFaceLegalLowerBound (coverPattern v r) n
          (decoderInputCap d n) (decoderPathCap v r d n) : ℝ) := by
  let s := v - r
  let a := decoderInputExponent d
  let c := decoderPathExponent d
  let B₀ := decoderBaselineConstant v r
  let Mfixed := coverMeetingConstant v r
  let Mused := decoderUsedConstant v r
  have hs : 0 < s := by omega
  have hB₀ : 0 < B₀ := by simp [B₀, decoderBaselineConstant]
  have hids := decoder_exponent_identities hd
  have hgapFixed : ((s - 1 : ℕ) : ℝ) + a < s := by
    have hsone : 1 ≤ s := by omega
    have hinv : (0 : ℝ) < 1 / d := by
      have hdR : (0 : ℝ) < d := by exact_mod_cast hd
      positivity
    rw [Nat.cast_sub hsone]
    norm_num
    rw [show a = 1 - (1 : ℝ) / d by simpa [a] using hids.1]
    linarith
  have hgapUsed : ((s - 1 : ℕ) : ℝ) + c < s := by
    have hsone : 1 ≤ s := by omega
    have h2dR : (0 : ℝ) < 2 * d := by
      exact_mod_cast (Nat.mul_pos (by omega : 0 < 2) hd)
    have hinv : (0 : ℝ) < 1 / (2 * d) := by positivity
    rw [Nat.cast_sub hsone]
    norm_num
    rw [show c = 1 - (1 : ℝ) / (2 * d) by
      simpa [c] using hids.2.1]
    linarith
  have hdomFixed := eventually_const_mul_rpow_le_rpow
    (C := (4 * B₀ * Mfixed : ℕ)) hgapFixed (by positivity)
  have hdomUsed := eventually_const_mul_rpow_le_rpow
    (C := (4 * B₀ * Mused : ℕ)) hgapUsed (by positivity)
  filter_upwards [hdomFixed, hdomUsed,
      eventually_ge_atTop (max (2 * v) 1)] with n hdomFixed hdomUsed hn
  have hn1 : 1 ≤ n := (le_max_right _ _).trans hn
  have hnv : 2 * v ≤ n := (le_max_left _ _).trans hn
  have hbaseline := descFactorial_sub_cast_lower
    (n := n) (r := r) (s := s) (by
      have : r + s = v := by dsimp [s]; omega
      simpa [this] using hnv)
  let base := (n - r).descFactorial s
  let lossFixed := codimOneMeetingBound (coverPattern v r) n
    (decoderInputCap d n)
  let lossUsed := codimOneMeetingBound (coverPattern v r) n
    ((coverPattern v r).freeEdges.card * decoderPathCap v r d n)
  have hfixedRaw : (lossFixed : ℝ) ≤
      (Mfixed : ℝ) * (n : ℝ) ^ (((s - 1 : ℕ) : ℝ) + a) := by
    simpa [lossFixed, Mfixed, s, a] using
      (decoderFixedMeeting_cast_le
        (n := n) (v := v) (r := r) (d := d) hr hrv hn1)
  have husedRaw : (lossUsed : ℝ) ≤
      (Mused : ℝ) * (n : ℝ) ^ (((s - 1 : ℕ) : ℝ) + c) := by
    simpa [lossUsed, Mused, s, c] using
      (decoderUsedMeeting_cast_le
        (n := n) (v := v) (r := r) (d := d) hr hrv hn1)
  have hfixed : (lossFixed : ℝ) ≤
      (n : ℝ) ^ s / (4 * B₀ : ℕ) := by
    have hscaled : (4 * B₀ : ℝ) *
          ((Mfixed : ℝ) *
            (n : ℝ) ^ (((s - 1 : ℕ) : ℝ) + a)) ≤
        (n : ℝ) ^ s := by
      calc
        (4 * B₀ : ℝ) * ((Mfixed : ℝ) *
            (n : ℝ) ^ (((s - 1 : ℕ) : ℝ) + a)) =
            ((4 * B₀ * Mfixed : ℕ) : ℝ) *
              (n : ℝ) ^ (((s - 1 : ℕ) : ℝ) + a) := by
          push_cast
          ring
        _ ≤ (n : ℝ) ^ (s : ℝ) := hdomFixed
        _ = (n : ℝ) ^ s := by rw [Real.rpow_natCast]
    have hden : (0 : ℝ) < (4 * B₀ : ℕ) := by positivity
    apply (le_div_iff₀ hden).2
    calc
      (lossFixed : ℝ) * (4 * B₀ : ℕ) ≤
          ((Mfixed : ℝ) *
            (n : ℝ) ^ (((s - 1 : ℕ) : ℝ) + a)) *
              (4 * B₀ : ℕ) := by gcongr
      _ ≤ (n : ℝ) ^ s := by
        rw [show (Mfixed : ℝ) *
              (n : ℝ) ^ (((s - 1 : ℕ) : ℝ) + a) *
                (4 * B₀ : ℕ) =
            (4 * B₀ : ℝ) * ((Mfixed : ℝ) *
              (n : ℝ) ^ (((s - 1 : ℕ) : ℝ) + a)) by
                push_cast
                ring]
        exact hscaled
  have hused : (lossUsed : ℝ) ≤
      (n : ℝ) ^ s / (4 * B₀ : ℕ) := by
    have hscaled : (4 * B₀ : ℝ) *
          ((Mused : ℝ) *
            (n : ℝ) ^ (((s - 1 : ℕ) : ℝ) + c)) ≤
        (n : ℝ) ^ s := by
      calc
        (4 * B₀ : ℝ) * ((Mused : ℝ) *
            (n : ℝ) ^ (((s - 1 : ℕ) : ℝ) + c)) =
            ((4 * B₀ * Mused : ℕ) : ℝ) *
              (n : ℝ) ^ (((s - 1 : ℕ) : ℝ) + c) := by
          push_cast
          ring
        _ ≤ (n : ℝ) ^ (s : ℝ) := hdomUsed
        _ = (n : ℝ) ^ s := by rw [Real.rpow_natCast]
    have hden : (0 : ℝ) < (4 * B₀ : ℕ) := by positivity
    apply (le_div_iff₀ hden).2
    calc
      (lossUsed : ℝ) * (4 * B₀ : ℕ) ≤
          ((Mused : ℝ) *
            (n : ℝ) ^ (((s - 1 : ℕ) : ℝ) + c)) *
              (4 * B₀ : ℕ) := by gcongr
      _ ≤ (n : ℝ) ^ s := by
        rw [show (Mused : ℝ) *
              (n : ℝ) ^ (((s - 1 : ℕ) : ℝ) + c) *
                (4 * B₀ : ℕ) =
            (4 * B₀ : ℝ) * ((Mused : ℝ) *
              (n : ℝ) ^ (((s - 1 : ℕ) : ℝ) + c)) by
                push_cast
                ring]
        exact hscaled
  have hpowPos : (0 : ℝ) < (n : ℝ) ^ s := by positivity
  have hbaseReal : (n : ℝ) ^ s / B₀ ≤ (base : ℝ) := by
    have hB₀eq : (B₀ : ℝ) = (2 : ℝ) ^ s := by
      simp [B₀, decoderBaselineConstant, s]
    rw [hB₀eq]
    simpa [base] using hbaseline
  have hratio4 : (n : ℝ) ^ s / (4 * B₀ : ℕ) =
      ((n : ℝ) ^ s / B₀) / 4 := by
    have hBne : (B₀ : ℝ) ≠ 0 := by exact_mod_cast hB₀.ne'
    push_cast
    field_simp
  have hratio2 : (n : ℝ) ^ s / (2 * B₀ : ℕ) =
      ((n : ℝ) ^ s / B₀) / 2 := by
    have hBne : (B₀ : ℝ) ≠ 0 := by exact_mod_cast hB₀.ne'
    push_cast
    field_simp
  rw [hratio4] at hfixed hused
  have hfixedBaseReal : (lossFixed : ℝ) ≤ (base : ℝ) := by
    have hscalePos : (0 : ℝ) < (n : ℝ) ^ s / B₀ := by positivity
    linarith
  have hfixedBase : lossFixed ≤ base := by exact_mod_cast hfixedBaseReal
  have hcastFirst : ((base - lossFixed : ℕ) : ℝ) =
      (base : ℝ) - lossFixed := by
    rw [Nat.cast_sub hfixedBase]
  have husedRemainReal : (lossUsed : ℝ) ≤
      ((base - lossFixed : ℕ) : ℝ) := by
    rw [hcastFirst]
    linarith
  have husedRemain : lossUsed ≤ base - lossFixed := by
    exact_mod_cast husedRemainReal
  have hcastSecond : (((base - lossFixed) - lossUsed : ℕ) : ℝ) =
      (base : ℝ) - lossFixed - lossUsed := by
    rw [Nat.cast_sub husedRemain, hcastFirst]
  have hlower : (n : ℝ) ^ s / (2 * B₀ : ℕ) ≤
      (((base - lossFixed) - lossUsed : ℕ) : ℝ) := by
    rw [hcastSecond, hratio2]
    linarith
  have hpositiveReal : (0 : ℝ) <
      (((base - lossFixed) - lossUsed : ℕ) : ℝ) := by
    have hden : (0 : ℝ) < (2 * B₀ : ℕ) := by positivity
    exact (div_pos hpowPos hden).trans_le hlower
  have hpositive : 0 < (base - lossFixed) - lossUsed := by exact_mod_cast hpositiveReal
  constructor
  · simpa [rootedFaceLegalLowerBound, base, lossFixed, lossUsed, s,
      CoverClique.card_coverRoot hrv.le] using hpositive
  · simpa [rootedFaceLegalLowerBound, base, lossFixed, lossUsed, s, B₀,
      CoverClique.card_coverRoot hrv.le] using hlower

lemma eventually_half_path_rpow_mul_le_cap
    (hr : 0 < r) (hd : 0 < d) :
    ∀ᶠ n : ℕ in atTop,
      (decoderPathMultiplier v r : ℝ) *
          ((n : ℝ) ^ decoderPathExponent d / 2) ≤
        (decoderPathCap v r d n : ℝ) := by
  have hnum : 0 < 2 * d - 1 := by omega
  have hden : 0 < 2 * d := Nat.mul_pos (by omega) hd
  have hfloor := eventually_half_rpow_le_rationalPowerThreshold hnum hden
  filter_upwards [hfloor] with n hn
  rw [decoderPathCap]
  push_cast
  exact mul_le_mul_of_nonneg_left hn (Nat.cast_nonneg _)

/-- The scheduled face numerator divided by the rooted legal denominator
fits below half of the path cap. -/
theorem eventually_decoder_quantitative_bound
    (hr : 0 < r) (hrv : r < v) (hd : 0 < d) :
    ∀ᶠ n : ℕ in atTop,
      (Real.exp 1 - 1) *
          ((faceScheduleNumeratorBound (coverPattern v r) n
              (decoderInputCap d n) : ℝ) /
            rootedFaceLegalLowerBound (coverPattern v r) n
              (decoderInputCap d n) (decoderPathCap v r d n)) ≤
        (decoderPathCap v r d n : ℝ) / 2 := by
  have hlegal := eventually_decoder_legalLowerBound hr hrv hd
  have hcap := eventually_half_path_rpow_mul_le_cap
    (v := v) hr hd
  filter_upwards [hlegal, hcap, eventually_ge_atTop (1 : ℕ)] with
      n hlegal hcap hn
  let s := v - r
  let a := decoderInputExponent d
  let c := decoderPathExponent d
  let S := decoderScheduleConstant v r
  let B₀ := decoderBaselineConstant v r
  let L := rootedFaceLegalLowerBound (coverPattern v r) n
    (decoderInputCap d n) (decoderPathCap v r d n)
  let B := faceScheduleNumeratorBound (coverPattern v r) n
    (decoderInputCap d n)
  have hnpos : (0 : ℝ) < n := by positivity
  have hD := decoderInputCap_cast_le d n
  have hB : (B : ℝ) ≤ (S : ℝ) * (n : ℝ) ^ (s + a) := by
    dsimp [B, S]
    rw [decoderScheduleNumerator_eq hrv.le]
    push_cast
    calc
      (decoderScheduleConstant v r : ℝ) * (n : ℝ) ^ (v - r) *
            (decoderInputCap d n : ℝ) ≤
          (decoderScheduleConstant v r : ℝ) *
            (n : ℝ) ^ s * (n : ℝ) ^ a := by
        gcongr
        simpa [a, decoderInputExponent] using hD
      _ = (decoderScheduleConstant v r : ℝ) *
            (n : ℝ) ^ (s + a) := by
        rw [show (decoderScheduleConstant v r : ℝ) *
            (n : ℝ) ^ s * (n : ℝ) ^ a =
            (decoderScheduleConstant v r : ℝ) *
              ((n : ℝ) ^ s * (n : ℝ) ^ a) by ring]
        rw [← Real.rpow_natCast, ← Real.rpow_add hnpos]
  have hLposReal : (0 : ℝ) < L := by
    exact_mod_cast hlegal.1
  have hLlower : (n : ℝ) ^ s / (2 * B₀ : ℕ) ≤ (L : ℝ) := by
    simpa [L, s, B₀] using hlegal.2
  have hB₀pos : (0 : ℝ) < B₀ := by
    dsimp [B₀, decoderBaselineConstant]
    positivity
  have hpowSpos : (0 : ℝ) < (n : ℝ) ^ s := by positivity
  have hB₀nat : 0 < B₀ := by exact_mod_cast hB₀pos
  have hratio : (B : ℝ) / L ≤
      ((2 * B₀ * S : ℕ) : ℝ) * (n : ℝ) ^ a := by
    apply (div_le_iff₀ hLposReal).2
    calc
      (B : ℝ) ≤ (S : ℝ) * (n : ℝ) ^ (s + a) := hB
      _ = (S : ℝ) * ((n : ℝ) ^ s * (n : ℝ) ^ a) := by
        rw [Real.rpow_add hnpos]
        rw [Real.rpow_natCast]
      _ ≤ (S : ℝ) * (((2 * B₀ : ℕ) : ℝ) * L *
            (n : ℝ) ^ a) := by
        gcongr
        have hden : (0 : ℝ) < (2 * B₀ : ℕ) := by
          exact_mod_cast (Nat.mul_pos (by omega : 0 < 2) hB₀nat)
        simpa [mul_comm] using (div_le_iff₀ hden).mp hLlower
      _ = ((2 * B₀ * S : ℕ) : ℝ) * (n : ℝ) ^ a * L := by
        push_cast
        ring
  have hexpCoef : Real.exp 1 - 1 ≤ 2 := by
    linarith [Real.exp_one_lt_d9]
  have hleft : (Real.exp 1 - 1) * ((B : ℝ) / L) ≤
      ((4 * B₀ * S : ℕ) : ℝ) * (n : ℝ) ^ a := by
    calc
      (Real.exp 1 - 1) * ((B : ℝ) / L) ≤
          2 * (((2 * B₀ * S : ℕ) : ℝ) * (n : ℝ) ^ a) := by
        exact mul_le_mul hexpCoef hratio (by positivity) (by norm_num)
      _ = ((4 * B₀ * S : ℕ) : ℝ) * (n : ℝ) ^ a := by
        push_cast
        ring
  have hac : a ≤ c := (decoder_exponent_identities hd).2.2.1.le
  have hpowac : (n : ℝ) ^ a ≤ (n : ℝ) ^ c :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) hac
  have hright : ((4 * B₀ * S : ℕ) : ℝ) * (n : ℝ) ^ a ≤
      (decoderPathCap v r d n : ℝ) / 2 := by
    have hcap' : (decoderPathMultiplier v r : ℝ) *
          ((n : ℝ) ^ c / 2) ≤ (decoderPathCap v r d n : ℝ) := by
      simpa [c] using hcap
    have hM : decoderPathMultiplier v r = 16 * B₀ * S := by
      rfl
    rw [hM] at hcap'
    push_cast at hcap'
    calc
      ((4 * B₀ * S : ℕ) : ℝ) * (n : ℝ) ^ a ≤
          ((4 * B₀ * S : ℕ) : ℝ) * (n : ℝ) ^ c := by gcongr
      _ = (16 * (B₀ : ℝ) * (S : ℝ) *
            ((n : ℝ) ^ c / 2)) / 2 := by
        push_cast
        ring
      _ ≤ (decoderPathCap v r d n : ℝ) / 2 := by gcongr
  change (Real.exp 1 - 1) * ((B : ℝ) / L) ≤
    (decoderPathCap v r d n : ℝ) / 2
  exact hleft.trans hright

/-- The polynomially many face counters are dominated by the exponential
tail supplied by the growing decoder path cap. -/
theorem eventually_decoder_exponential_union_bound
    (hr : 0 < r) (hd : 0 < d) :
    ∀ᶠ n : ℕ in atTop,
      (Fintype.card (RelevantFaceLoadTarget (coverPattern v r) n) : ℝ) *
          Real.exp (-(decoderPathCap v r d n : ℝ) / 2) < 1 := by
  let c := decoderPathExponent d
  let M := decoderPathMultiplier v r
  let C₀ : ℝ := 2 ^ v
  have hc : 0 < c := by
    simpa [c] using (decoder_exponent_identities hd).2.2.2
  have hMnat : 0 < M := by
    exact decoderPathMultiplier_pos v r hr
  have hM : 0 < (M : ℝ) := by exact_mod_cast hMnat
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
  have hcap := eventually_half_path_rpow_mul_le_cap
    (v := v) hr hd
  filter_upwards [hsmall, hcap] with n hnsmall hcap
  have hcardNat :
      Fintype.card (RelevantFaceLoadTarget (coverPattern v r) n) ≤
        2 ^ v * n ^ (r - 1) := by
    calc
      Fintype.card (RelevantFaceLoadTarget (coverPattern v r) n) ≤
          (coverPattern v r).freeEdges.card * Nat.choose n (r - 1) :=
        card_relevantFaceLoadTarget_le _ _
      _ ≤ 2 ^ v * n ^ (r - 1) :=
        Nat.mul_le_mul card_coverPattern_freeEdges_le (Nat.choose_le_pow _ _)
  have hcardReal :
      (Fintype.card (RelevantFaceLoadTarget (coverPattern v r) n) : ℝ) ≤
        (2 ^ v : ℕ) * (n : ℝ) ^ (r - 1) := by
    exact_mod_cast hcardNat
  have hspent : (M : ℝ) / 4 * (n : ℝ) ^ c ≤
      (decoderPathCap v r d n : ℝ) / 2 := by
    calc
      (M : ℝ) / 4 * (n : ℝ) ^ c =
          ((M : ℝ) * ((n : ℝ) ^ c / 2)) / 2 := by ring
      _ ≤ (decoderPathCap v r d n : ℝ) / 2 := by
        simpa [M, c] using
          div_le_div_of_nonneg_right hcap (by norm_num : (0 : ℝ) ≤ 2)
  calc
    (Fintype.card (RelevantFaceLoadTarget (coverPattern v r) n) : ℝ) *
          Real.exp (-(decoderPathCap v r d n : ℝ) / 2) ≤
        ((2 ^ v : ℕ) : ℝ) * (n : ℝ) ^ (r - 1) *
          Real.exp (-(decoderPathCap v r d n : ℝ) / 2) := by
      gcongr
    _ ≤ ((2 ^ v : ℕ) : ℝ) * (n : ℝ) ^ (r - 1) *
          Real.exp (-((M : ℝ) / 4) * (n : ℝ) ^ c) := by
      gcongr
      convert neg_le_neg hspent using 1 <;> ring
    _ = C₀ * ((n : ℝ) ^ (r - 1) *
          Real.exp (-((M : ℝ) / 4) * (n : ℝ) ^ c)) := by
      dsimp [C₀]
      push_cast
      ring
    _ < 1 := hnsmall

/-- For all sufficiently large ambient orders, every uniform root family
with the power-cleared codimension-one degree bound has simultaneous,
pairwise-separated complete rooted-clique extensions. -/
theorem eventually_exists_separatedCliqueExtensions_of_power_bound
    (hr : 0 < r) (hrv : r < v) (hd : 0 < d) :
    ∀ᶠ n : ℕ in atTop, ∀ roots : Finset (Finset (Fin n)),
      (∀ e ∈ roots, e.card = r) →
      (∀ J : Finset (Fin n), J.card = r - 1 →
        (Reserve.localDegree roots J) ^ d ≤ n ^ (d - 1)) →
      Nonempty (BoundedSeparatedCliqueExtensions n v r
        (decoderPathCap v r d n) roots roots) := by
  have hlegal := eventually_decoder_legalLowerBound hr hrv hd
  have hquant := eventually_decoder_quantitative_bound hr hrv hd
  have hcard := eventually_decoder_exponential_union_bound
    (v := v) hr hd
  filter_upwards [hlegal, hquant, hcard, eventually_ge_atTop v] with
      n hlegal hquant hcard hvn
  intro roots huniform hdegree
  by_cases hroots : roots = ∅
  · subst roots
    refine ⟨{
      toSeparatedCliqueExtensions := {
        embedding := fun e he ↦ False.elim (show False by simpa using he)
        root_image := ?_
        free_eq := ?_
        free_disjoint_forbidden := ?_
        free_pairwise := ?_ }
      free_degree_le := ?_ }⟩
    · intro e he
      simp at he
    · intro e he
      simp at he
    · intro e he
      simp at he
    · intro e he
      simp at he
    · intro J hJ
      simp [separatedFreeEdges, Reserve.localDegree]
  · let : Nonempty (Fin v ↪ Fin n) := ⟨Fin.castLEEmb hvn⟩
    obtain ⟨e₀, he₀⟩ := Finset.nonempty_iff_ne_empty.mpr hroots
    apply exists_separatedCliqueExtensions_of_finite_bounds
      hr hrv roots roots huniform huniform e₀ he₀
    · intro J hJ
      exact le_decoderInputCap_of_pow_le d n _ hd (hdegree J hJ)
    · intro J hJ
      exact le_decoderInputCap_of_pow_le d n _ hd (hdegree J hJ)
    · exact hlegal.1
    · exact hquant
    · exact hcard

/-- Two-host form of the separated rooted-clique theorem.  The roots and
the forbidden edge host may be different, provided both obey the same
power-cleared codimension-one bound. -/
theorem eventually_exists_separatedCliqueExtensions_of_two_power_bounds
    (hr : 0 < r) (hrv : r < v) (hd : 0 < d) :
    ∀ᶠ n : ℕ in atTop,
      ∀ roots forbidden : Finset (Finset (Fin n)),
      (∀ e ∈ roots, e.card = r) →
      (∀ e ∈ forbidden, e.card = r) →
      (∀ J : Finset (Fin n), J.card = r - 1 →
        (Reserve.localDegree roots J) ^ d ≤ n ^ (d - 1)) →
      (∀ J : Finset (Fin n), J.card = r - 1 →
        (Reserve.localDegree forbidden J) ^ d ≤ n ^ (d - 1)) →
      Nonempty (BoundedSeparatedCliqueExtensions n v r
        (decoderPathCap v r d n) roots forbidden) := by
  have hlegal := eventually_decoder_legalLowerBound hr hrv hd
  have hquant := eventually_decoder_quantitative_bound hr hrv hd
  have hcard := eventually_decoder_exponential_union_bound
    (v := v) hr hd
  filter_upwards [hlegal, hquant, hcard, eventually_ge_atTop v] with
      n hlegal hquant hcard hvn
  intro roots forbidden hrootsUniform hforbiddenUniform
    hrootsDegree hforbiddenDegree
  by_cases hroots : roots = ∅
  · subst roots
    refine ⟨{
      toSeparatedCliqueExtensions := {
        embedding := fun e he ↦ False.elim (show False by simpa using he)
        root_image := ?_
        free_eq := ?_
        free_disjoint_forbidden := ?_
        free_pairwise := ?_ }
      free_degree_le := ?_ }⟩
    · intro e he
      simp at he
    · intro e he
      simp at he
    · intro e he
      simp at he
    · intro e he
      simp at he
    · intro J hJ
      simp [separatedFreeEdges, Reserve.localDegree]
  · let : Nonempty (Fin v ↪ Fin n) := ⟨Fin.castLEEmb hvn⟩
    obtain ⟨e₀, he₀⟩ := Finset.nonempty_iff_ne_empty.mpr hroots
    apply exists_separatedCliqueExtensions_of_finite_bounds
      hr hrv roots forbidden hrootsUniform hforbiddenUniform e₀ he₀
    · intro J hJ
      exact le_decoderInputCap_of_pow_le d n _ hd (hrootsDegree J hJ)
    · intro J hJ
      exact le_decoderInputCap_of_pow_le d n _ hd (hforbiddenDegree J hJ)
    · exact hlegal.1
    · exact hquant
    · exact hcard

end

end Erdos722.LocalDecoderAsymptotic
