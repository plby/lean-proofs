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
import ErdosProblems.Erdos722.RootedFamilyEmbedding
import ErdosProblems.Erdos722.RootedFamilyMultiEmbedding
import ErdosProblems.Erdos722.LocalDecoderAsymptotic
import Mathlib

/-!
# Asymptotic placement of a fixed rooted family

This is the cardinality-generic counterpart of the local-decoder placement
theorem.  The distinguished root may be a whole `k`-set.  If the family of
root images has codimension-one degree `O(n^(1-1/d))`, one copy of the fixed
pattern can be placed at every root while the union of all free edges has
degree `O(n^(1-1/(2d)))`.
-/

namespace Erdos722.RootedFamilyAsymptotic

open Finset Filter
open scoped Topology Real
open Erdos722.Reserve
open Erdos722.RootedEmbedding
open Erdos722.RootSchedule
open Erdos722.Asymptotics
open Erdos722.LocalDecoderAsymptotic
open Erdos722.RootedFamilyEmbedding
open Erdos722.RootedFamilyMultiEmbedding

noncomputable section

def rootedMeetingConstant (P : RootedPattern v r) : ℕ :=
  P.freeEdges.card * (2 ^ r * r ^ r)

def rootedUsedConstant (P : RootedPattern v r) : ℕ :=
  rootedMeetingConstant P * P.freeEdges.card * decoderPathMultiplier v r

def scaledDecoderPathCap (scale v r d n : ℕ) : ℕ :=
  scale * decoderPathCap v r d n

/-- For an arbitrary fixed rooted pattern, every term in the labelled
meeting loss has the essential exponent `v - |root| - 1`. -/
theorem codimOneMeetingBound_le
    (P : RootedPattern v r) (hr : 0 < r)
    (hroot : P.root.card < v) (n D : ℕ) :
    codimOneMeetingBound P n D ≤
      rootedMeetingConstant P * D * n ^ (v - P.root.card - 1) := by
  classical
  let M := (2 ^ r * r ^ r) * D * n ^ (v - P.root.card - 1)
  have hterm : ∀ e ∈ P.freeEdges,
      (n ^ (r - 1 - (e ∩ P.root).card) * D) *
          (2 ^ r *
            (r ^ (e \ P.root).card *
              n ^ (v - (P.root.card + (e \ P.root).card)))) ≤ M := by
    intro e he
    have heData := Finset.mem_filter.mp he
    have hecard : e.card = r := P.uniform e heData.1
    have hfree : ¬e ⊆ P.root := heData.2
    have houtsidePos : 0 < (e \ P.root).card := by
      rw [Finset.card_pos]
      exact Finset.sdiff_nonempty.mpr hfree
    have houtsideLeR : (e \ P.root).card ≤ r := by
      exact (Finset.card_le_card Finset.sdiff_subset).trans_eq hecard
    have houtsideLeComplement : (e \ P.root).card ≤ v - P.root.card := by
      have hsub : e \ P.root ⊆
          (Finset.univ : Finset (Fin v)) \ P.root := by
        intro x hx
        exact Finset.mem_sdiff.mpr
          ⟨Finset.mem_univ x, (Finset.mem_sdiff.mp hx).2⟩
      have hc := Finset.card_le_card hsub
      simpa [Finset.card_sdiff_of_subset (Finset.subset_univ _)] using hc
    have hsplit := Finset.card_inter_add_card_sdiff e P.root
    have hexp :
        (r - 1 - (e ∩ P.root).card) +
            (v - (P.root.card + (e \ P.root).card)) =
          v - P.root.card - 1 := by
      omega
    have hrpow : r ^ (e \ P.root).card ≤ r ^ r :=
      Nat.pow_le_pow_right hr houtsideLeR
    dsimp [M]
    calc
      (n ^ (r - 1 - (e ∩ P.root).card) * D) *
          (2 ^ r *
            (r ^ (e \ P.root).card *
              n ^ (v - (P.root.card + (e \ P.root).card)))) =
          (2 ^ r * r ^ (e \ P.root).card * D) *
            (n ^ (r - 1 - (e ∩ P.root).card) *
              n ^ (v - (P.root.card + (e \ P.root).card))) := by ring
      _ = (2 ^ r * r ^ (e \ P.root).card * D) *
            n ^ ((r - 1 - (e ∩ P.root).card) +
              (v - (P.root.card + (e \ P.root).card))) := by
        rw [Nat.pow_add]
      _ = (2 ^ r * r ^ (e \ P.root).card * D) *
            n ^ (v - P.root.card - 1) := by rw [hexp]
      _ ≤ (2 ^ r * r ^ r * D) * n ^ (v - P.root.card - 1) := by
        exact Nat.mul_le_mul_right _
          (Nat.mul_le_mul_right D (Nat.mul_le_mul_left (2 ^ r) hrpow))
  unfold codimOneMeetingBound
  calc
    (∑ e ∈ P.freeEdges,
      (n ^ (r - 1 - (e ∩ P.root).card) * D) *
        (2 ^ r *
          (r ^ (e \ P.root).card *
            n ^ (v - (P.root.card + (e \ P.root).card))))) ≤
        ∑ _e ∈ P.freeEdges, M := by
      apply Finset.sum_le_sum
      intro e he
      exact hterm e he
    _ = P.freeEdges.card * M := by simp
    _ = rootedMeetingConstant P * D *
        n ^ (v - P.root.card - 1) := by
      simp [M, rootedMeetingConstant]
      ring

lemma rootedFixedMeeting_cast_le
    (P : RootedPattern v r) (hr : 0 < r)
    (hroot : P.root.card < v) (hd : 0 < d) (hn : 1 ≤ n) :
    (codimOneMeetingBound P n (decoderInputCap d n) : ℝ) ≤
      (rootedMeetingConstant P : ℝ) *
        (n : ℝ) ^ ((v - P.root.card - 1 : ℕ) +
          decoderInputExponent d) := by
  have hrawNat := codimOneMeetingBound_le P hr hroot n
    (decoderInputCap d n)
  have hraw :
      (codimOneMeetingBound P n (decoderInputCap d n) : ℝ) ≤
        (rootedMeetingConstant P : ℝ) *
          (decoderInputCap d n : ℝ) *
            (n : ℝ) ^ (v - P.root.card - 1) := by
    exact_mod_cast hrawNat
  have hD := decoderInputCap_cast_le d n
  have hnpos : (0 : ℝ) < n := by positivity
  calc
    (codimOneMeetingBound P n (decoderInputCap d n) : ℝ) ≤
        (rootedMeetingConstant P : ℝ) *
          (decoderInputCap d n : ℝ) *
            (n : ℝ) ^ (v - P.root.card - 1) := hraw
    _ ≤ (rootedMeetingConstant P : ℝ) *
          (n : ℝ) ^ decoderInputExponent d *
            (n : ℝ) ^ (v - P.root.card - 1) := by
      dsimp [decoderInputExponent]
      gcongr
    _ = (rootedMeetingConstant P : ℝ) *
        (n : ℝ) ^ ((v - P.root.card - 1 : ℕ) +
          decoderInputExponent d) := by
      rw [show (rootedMeetingConstant P : ℝ) *
          (n : ℝ) ^ decoderInputExponent d *
            (n : ℝ) ^ (v - P.root.card - 1) =
          (rootedMeetingConstant P : ℝ) *
            ((n : ℝ) ^ decoderInputExponent d *
              (n : ℝ) ^ (v - P.root.card - 1)) by ring]
      rw [← Real.rpow_natCast, ← Real.rpow_add hnpos]
      congr 2
      ring

lemma rootedUsedMeeting_cast_le
    (P : RootedPattern v r) (hr : 0 < r)
    (hroot : P.root.card < v) (hd : 0 < d) (hn : 1 ≤ n) :
    (codimOneMeetingBound P n
        (P.freeEdges.card * decoderPathCap v r d n) : ℝ) ≤
      (rootedUsedConstant P : ℝ) *
        (n : ℝ) ^ ((v - P.root.card - 1 : ℕ) +
          decoderPathExponent d) := by
  let T := decoderPathScale d n
  have hrawNat := codimOneMeetingBound_le P hr hroot n
    (P.freeEdges.card * decoderPathCap v r d n)
  have hupperNat :
      codimOneMeetingBound P n
          (P.freeEdges.card * decoderPathCap v r d n) ≤
        rootedUsedConstant P * T * n ^ (v - P.root.card - 1) := by
    calc
      codimOneMeetingBound P n
          (P.freeEdges.card * decoderPathCap v r d n) ≤
          rootedMeetingConstant P *
            (P.freeEdges.card * decoderPathCap v r d n) *
              n ^ (v - P.root.card - 1) := hrawNat
      _ = rootedUsedConstant P * T *
            n ^ (v - P.root.card - 1) := by
        unfold decoderPathCap rootedUsedConstant
        dsimp [T]
        ring
  have hupperReal :
      (codimOneMeetingBound P n
          (P.freeEdges.card * decoderPathCap v r d n) : ℝ) ≤
        (rootedUsedConstant P : ℝ) * (T : ℝ) *
          (n : ℝ) ^ (v - P.root.card - 1) := by
    exact_mod_cast hupperNat
  have hT : (T : ℝ) ≤ (n : ℝ) ^ decoderPathExponent d := by
    exact decoderPathScale_cast_le d n
  have hnpos : (0 : ℝ) < n := by positivity
  calc
    (codimOneMeetingBound P n
        (P.freeEdges.card * decoderPathCap v r d n) : ℝ) ≤
        (rootedUsedConstant P : ℝ) * (T : ℝ) *
          (n : ℝ) ^ (v - P.root.card - 1) := hupperReal
    _ ≤ (rootedUsedConstant P : ℝ) *
          (n : ℝ) ^ decoderPathExponent d *
            (n : ℝ) ^ (v - P.root.card - 1) := by gcongr
    _ = (rootedUsedConstant P : ℝ) *
        (n : ℝ) ^ ((v - P.root.card - 1 : ℕ) +
          decoderPathExponent d) := by
      rw [show (rootedUsedConstant P : ℝ) *
          (n : ℝ) ^ decoderPathExponent d *
            (n : ℝ) ^ (v - P.root.card - 1) =
          (rootedUsedConstant P : ℝ) *
            ((n : ℝ) ^ decoderPathExponent d *
              (n : ℝ) ^ (v - P.root.card - 1)) by ring]
      rw [← Real.rpow_natCast, ← Real.rpow_add hnpos]
      congr 2
      ring

lemma rootedScaledUsedMeeting_cast_le
    (P : RootedPattern v r) (hr : 0 < r)
    (hroot : P.root.card < v) (hd : 0 < d) (hn : 1 ≤ n)
    (scale : ℕ) :
    (codimOneMeetingBound P n
        (P.freeEdges.card * scaledDecoderPathCap scale v r d n) : ℝ) ≤
      (scale * rootedUsedConstant P : ℕ) *
        (n : ℝ) ^ ((v - P.root.card - 1 : ℕ) +
          decoderPathExponent d) := by
  let T := decoderPathScale d n
  have hrawNat := codimOneMeetingBound_le P hr hroot n
    (P.freeEdges.card * scaledDecoderPathCap scale v r d n)
  have hupperNat :
      codimOneMeetingBound P n
          (P.freeEdges.card * scaledDecoderPathCap scale v r d n) ≤
        (scale * rootedUsedConstant P) * T *
          n ^ (v - P.root.card - 1) := by
    calc
      codimOneMeetingBound P n
          (P.freeEdges.card * scaledDecoderPathCap scale v r d n) ≤
          rootedMeetingConstant P *
            (P.freeEdges.card * scaledDecoderPathCap scale v r d n) *
              n ^ (v - P.root.card - 1) := hrawNat
      _ = (scale * rootedUsedConstant P) * T *
            n ^ (v - P.root.card - 1) := by
        unfold scaledDecoderPathCap decoderPathCap rootedUsedConstant
        dsimp [T]
        ring
  have hupperReal :
      (codimOneMeetingBound P n
          (P.freeEdges.card * scaledDecoderPathCap scale v r d n) : ℝ) ≤
        ((scale * rootedUsedConstant P : ℕ) : ℝ) * (T : ℝ) *
          (n : ℝ) ^ (v - P.root.card - 1) := by
    exact_mod_cast hupperNat
  have hT : (T : ℝ) ≤ (n : ℝ) ^ decoderPathExponent d :=
    decoderPathScale_cast_le d n
  have hnpos : (0 : ℝ) < n := by positivity
  calc
    (codimOneMeetingBound P n
        (P.freeEdges.card * scaledDecoderPathCap scale v r d n) : ℝ) ≤
        ((scale * rootedUsedConstant P : ℕ) : ℝ) * (T : ℝ) *
          (n : ℝ) ^ (v - P.root.card - 1) := hupperReal
    _ ≤ ((scale * rootedUsedConstant P : ℕ) : ℝ) *
          (n : ℝ) ^ decoderPathExponent d *
            (n : ℝ) ^ (v - P.root.card - 1) := by gcongr
    _ = ((scale * rootedUsedConstant P : ℕ) : ℝ) *
        (n : ℝ) ^ ((v - P.root.card - 1 : ℕ) +
          decoderPathExponent d) := by
      rw [show ((scale * rootedUsedConstant P : ℕ) : ℝ) *
          (n : ℝ) ^ decoderPathExponent d *
            (n : ℝ) ^ (v - P.root.card - 1) =
          ((scale * rootedUsedConstant P : ℕ) : ℝ) *
            ((n : ℝ) ^ decoderPathExponent d *
              (n : ℝ) ^ (v - P.root.card - 1)) by ring]
      rw [← Real.rpow_natCast, ← Real.rpow_add hnpos]
      congr 2
      ring

/-- Both meeting losses for a fixed rooted pattern are eventually a small
fraction of the falling-factorial baseline. -/
theorem eventually_rooted_legalLowerBound
    (P : RootedPattern v r) (hr : 0 < r)
    (hroot : P.root.card < v) (hd : 0 < d) :
    ∀ᶠ n : ℕ in atTop,
      0 < rootedFaceLegalLowerBound P n
          (decoderInputCap d n) (decoderPathCap v r d n) ∧
      (n : ℝ) ^ (v - P.root.card) /
          (2 * 2 ^ (v - P.root.card) : ℕ) ≤
        (rootedFaceLegalLowerBound P n
          (decoderInputCap d n) (decoderPathCap v r d n) : ℝ) := by
  let s := v - P.root.card
  let a := decoderInputExponent d
  let c := decoderPathExponent d
  let B₀ := 2 ^ s
  let Mfixed := rootedMeetingConstant P
  let Mused := rootedUsedConstant P
  have hs : 0 < s := by omega
  have hB₀ : 0 < B₀ := by simp [B₀]
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
    (n := n) (r := P.root.card) (s := s) (by
      have : P.root.card + s = v := by dsimp [s]; omega
      simpa [this] using hnv)
  let base := (n - P.root.card).descFactorial s
  let lossFixed := codimOneMeetingBound P n (decoderInputCap d n)
  let lossUsed := codimOneMeetingBound P n
    (P.freeEdges.card * decoderPathCap v r d n)
  have hfixedRaw : (lossFixed : ℝ) ≤
      (Mfixed : ℝ) * (n : ℝ) ^ (((s - 1 : ℕ) : ℝ) + a) := by
    simpa [lossFixed, Mfixed, s, a] using
      (rootedFixedMeeting_cast_le P hr hroot hd hn1)
  have husedRaw : (lossUsed : ℝ) ≤
      (Mused : ℝ) * (n : ℝ) ^ (((s - 1 : ℕ) : ℝ) + c) := by
    simpa [lossUsed, Mused, s, c] using
      (rootedUsedMeeting_cast_le P hr hroot hd hn1)
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
    have hB₀eq : (B₀ : ℝ) = (2 : ℝ) ^ s := by simp [B₀]
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
  have hpositive : 0 < (base - lossFixed) - lossUsed := by
    exact_mod_cast hpositiveReal
  constructor
  · simpa [rootedFaceLegalLowerBound, base, lossFixed, lossUsed, s]
      using hpositive
  · simpa [rootedFaceLegalLowerBound, base, lossFixed, lossUsed, s, B₀]
      using hlower

theorem eventually_rooted_scaled_legalLowerBound
    (P : RootedPattern v r) (hr : 0 < r)
    (hroot : P.root.card < v) (hd : 0 < d)
    (scale : ℕ) (hscale : 0 < scale) :
    ∀ᶠ n : ℕ in atTop,
      0 < rootedFaceLegalLowerBound P n
          (decoderInputCap d n) (scaledDecoderPathCap scale v r d n) ∧
      (n : ℝ) ^ (v - P.root.card) /
          (2 * 2 ^ (v - P.root.card) : ℕ) ≤
        (rootedFaceLegalLowerBound P n
          (decoderInputCap d n) (scaledDecoderPathCap scale v r d n) : ℝ) := by
  let s := v - P.root.card
  let a := decoderInputExponent d
  let c := decoderPathExponent d
  let B₀ := 2 ^ s
  let Mfixed := rootedMeetingConstant P
  let Mused := scale * rootedUsedConstant P
  have hs : 0 < s := by omega
  have hB₀ : 0 < B₀ := by simp [B₀]
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
    (C := (4 * B₀ * Mused : ℕ)) hgapUsed (by
      dsimp [Mused]
      positivity)
  filter_upwards [hdomFixed, hdomUsed,
      eventually_ge_atTop (max (2 * v) 1)] with n hdomFixed hdomUsed hn
  have hn1 : 1 ≤ n := (le_max_right _ _).trans hn
  have hnv : 2 * v ≤ n := (le_max_left _ _).trans hn
  have hbaseline := descFactorial_sub_cast_lower
    (n := n) (r := P.root.card) (s := s) (by
      have : P.root.card + s = v := by dsimp [s]; omega
      simpa [this] using hnv)
  let base := (n - P.root.card).descFactorial s
  let lossFixed := codimOneMeetingBound P n (decoderInputCap d n)
  let lossUsed := codimOneMeetingBound P n
    (P.freeEdges.card * scaledDecoderPathCap scale v r d n)
  have hfixedRaw : (lossFixed : ℝ) ≤
      (Mfixed : ℝ) * (n : ℝ) ^ (((s - 1 : ℕ) : ℝ) + a) := by
    simpa [lossFixed, Mfixed, s, a] using
      (rootedFixedMeeting_cast_le P hr hroot hd hn1)
  have husedRaw : (lossUsed : ℝ) ≤
      (Mused : ℝ) * (n : ℝ) ^ (((s - 1 : ℕ) : ℝ) + c) := by
    simpa [lossUsed, Mused, s, c] using
      (rootedScaledUsedMeeting_cast_le P hr hroot hd hn1 scale)
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
    have hB₀eq : (B₀ : ℝ) = (2 : ℝ) ^ s := by simp [B₀]
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
  have hpositive : 0 < (base - lossFixed) - lossUsed := by
    exact_mod_cast hpositiveReal
  constructor
  · simpa [rootedFaceLegalLowerBound, base, lossFixed, lossUsed, s]
      using hpositive
  · simpa [rootedFaceLegalLowerBound, base, lossFixed, lossUsed, s, B₀]
      using hlower

/-- Two-scale form of the legal-extension estimate.  The prescribed root
and forbidden hosts use `dInput`, while the random-greedy stopping cap uses
the independent denominator `dPath`. -/
theorem eventually_rooted_twoScale_scaled_legalLowerBound
    {dInput dPath : ℕ}
    (P : RootedPattern v r) (hr : 0 < r)
    (hroot : P.root.card < v)
    (hdInput : 0 < dInput) (hdPath : 0 < dPath)
    (scale : ℕ) (hscale : 0 < scale) :
    ∀ᶠ n : ℕ in atTop,
      0 < rootedFaceLegalLowerBound P n
          (decoderInputCap dInput n)
          (scaledDecoderPathCap scale v r dPath n) ∧
      (n : ℝ) ^ (v - P.root.card) /
          (2 * 2 ^ (v - P.root.card) : ℕ) ≤
        (rootedFaceLegalLowerBound P n
          (decoderInputCap dInput n)
          (scaledDecoderPathCap scale v r dPath n) : ℝ) := by
  let s := v - P.root.card
  let a := decoderInputExponent dInput
  let c := decoderPathExponent dPath
  let B₀ := 2 ^ s
  let Mfixed := rootedMeetingConstant P
  let Mused := scale * rootedUsedConstant P
  have hs : 0 < s := by omega
  have hB₀ : 0 < B₀ := by simp [B₀]
  have hgapFixed : ((s - 1 : ℕ) : ℝ) + a < s := by
    have hsone : 1 ≤ s := by omega
    have hinv : (0 : ℝ) < 1 / dInput := by
      have hdR : (0 : ℝ) < dInput := by exact_mod_cast hdInput
      positivity
    rw [Nat.cast_sub hsone]
    norm_num
    rw [show a = 1 - (1 : ℝ) / dInput by
      simpa [a] using (decoder_exponent_identities hdInput).1]
    linarith
  have hgapUsed : ((s - 1 : ℕ) : ℝ) + c < s := by
    have hsone : 1 ≤ s := by omega
    have h2dR : (0 : ℝ) < 2 * dPath := by
      exact_mod_cast (Nat.mul_pos (by omega : 0 < 2) hdPath)
    have hinv : (0 : ℝ) < 1 / (2 * dPath) := by positivity
    rw [Nat.cast_sub hsone]
    norm_num
    rw [show c = 1 - (1 : ℝ) / (2 * dPath) by
      simpa [c] using (decoder_exponent_identities hdPath).2.1]
    linarith
  have hdomFixed := eventually_const_mul_rpow_le_rpow
    (C := (4 * B₀ * Mfixed : ℕ)) hgapFixed (by positivity)
  have hdomUsed := eventually_const_mul_rpow_le_rpow
    (C := (4 * B₀ * Mused : ℕ)) hgapUsed (by
      dsimp [Mused]
      positivity)
  filter_upwards [hdomFixed, hdomUsed,
      eventually_ge_atTop (max (2 * v) 1)] with n hdomFixed hdomUsed hn
  have hn1 : 1 ≤ n := (le_max_right _ _).trans hn
  have hnv : 2 * v ≤ n := (le_max_left _ _).trans hn
  have hbaseline := descFactorial_sub_cast_lower
    (n := n) (r := P.root.card) (s := s) (by
      have : P.root.card + s = v := by dsimp [s]; omega
      simpa [this] using hnv)
  let base := (n - P.root.card).descFactorial s
  let lossFixed := codimOneMeetingBound P n (decoderInputCap dInput n)
  let lossUsed := codimOneMeetingBound P n
    (P.freeEdges.card * scaledDecoderPathCap scale v r dPath n)
  have hfixedRaw : (lossFixed : ℝ) ≤
      (Mfixed : ℝ) * (n : ℝ) ^ (((s - 1 : ℕ) : ℝ) + a) := by
    simpa [lossFixed, Mfixed, s, a] using
      (rootedFixedMeeting_cast_le P hr hroot hdInput hn1)
  have husedRaw : (lossUsed : ℝ) ≤
      (Mused : ℝ) * (n : ℝ) ^ (((s - 1 : ℕ) : ℝ) + c) := by
    simpa [lossUsed, Mused, s, c] using
      (rootedScaledUsedMeeting_cast_le P hr hroot hdPath hn1 scale)
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
    have hB₀eq : (B₀ : ℝ) = (2 : ℝ) ^ s := by simp [B₀]
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
  have hpositive : 0 < (base - lossFixed) - lossUsed := by
    exact_mod_cast hpositiveReal
  constructor
  · simpa [rootedFaceLegalLowerBound, base, lossFixed, lossUsed, s]
      using hpositive
  · simpa [rootedFaceLegalLowerBound, base, lossFixed, lossUsed, s, B₀]
      using hlower

/-- The scheduled-face numerator divided by the legal denominator fits
below half of the generic path cap. -/
theorem eventually_rooted_quantitative_bound
    (P : RootedPattern v r) (hr : 0 < r)
    (hroot : P.root.card < v) (hrootLarge : r ≤ P.root.card)
    (hd : 0 < d) :
    ∀ᶠ n : ℕ in atTop,
      (Real.exp 1 - 1) *
          ((faceScheduleNumeratorBound P n (decoderInputCap d n) : ℝ) /
            rootedFaceLegalLowerBound P n
              (decoderInputCap d n) (decoderPathCap v r d n)) ≤
        (decoderPathCap v r d n : ℝ) / 2 := by
  have hlegal := eventually_rooted_legalLowerBound P hr hroot hd
  have hcap := eventually_half_path_rpow_mul_le_cap
    (v := v) hr hd
  filter_upwards [hlegal, hcap, eventually_ge_atTop (1 : ℕ)] with
      n hlegal hcap hn
  let s := v - P.root.card
  let a := decoderInputExponent d
  let c := decoderPathExponent d
  let S := decoderScheduleConstant v r
  let B₀ := 2 ^ s
  let L := rootedFaceLegalLowerBound P n
    (decoderInputCap d n) (decoderPathCap v r d n)
  let B := faceScheduleNumeratorBound P n (decoderInputCap d n)
  have hnpos : (0 : ℝ) < n := by positivity
  have hD := decoderInputCap_cast_le d n
  have hpowEq : (n : ℝ) ^ s * (n : ℝ) ^ a =
      (n : ℝ) ^ ((s : ℝ) + a) := by
    rw [← Real.rpow_natCast (n : ℝ) s]
    exact (Real.rpow_add hnpos _ _).symm
  have hB : (B : ℝ) ≤ (S : ℝ) * (n : ℝ) ^ (s + a) := by
    dsimp [B, S]
    unfold faceScheduleNumeratorBound decoderScheduleConstant
    push_cast
    calc
      ((2 : ℝ) ^ (r - 1) * ((2 : ℝ) ^ v * (r : ℝ) ^ r) *
          (n : ℝ) ^ (v - P.root.card)) *
            (decoderInputCap d n : ℝ) ≤
        ((2 : ℝ) ^ (r - 1) * ((2 : ℝ) ^ v * (r : ℝ) ^ r)) *
          (n : ℝ) ^ s * (n : ℝ) ^ a := by
        gcongr
        simpa [a, decoderInputExponent] using hD
      _ = ((2 : ℝ) ^ (r - 1) * ((2 : ℝ) ^ v * (r : ℝ) ^ r)) *
          (n : ℝ) ^ (s + a) := by
        rw [show ((2 : ℝ) ^ (r - 1) * ((2 : ℝ) ^ v * (r : ℝ) ^ r)) *
            (n : ℝ) ^ s * (n : ℝ) ^ a =
          ((2 : ℝ) ^ (r - 1) * ((2 : ℝ) ^ v * (r : ℝ) ^ r)) *
            ((n : ℝ) ^ s * (n : ℝ) ^ a) by ring]
        rw [hpowEq]
  have hLposReal : (0 : ℝ) < L := by
    exact_mod_cast hlegal.1
  have hLlower : (n : ℝ) ^ s / (2 * B₀ : ℕ) ≤ (L : ℝ) := by
    simpa [L, s, B₀] using hlegal.2
  have hB₀pos : (0 : ℝ) < B₀ := by
    dsimp [B₀]
    positivity
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
  have hB₀le : B₀ ≤ decoderBaselineConstant v r := by
    dsimp [B₀, s, decoderBaselineConstant]
    exact Nat.pow_le_pow_right (by omega : 0 < 2) (by omega)
  have hright : ((4 * B₀ * S : ℕ) : ℝ) * (n : ℝ) ^ a ≤
      (decoderPathCap v r d n : ℝ) / 2 := by
    have hcap' : (decoderPathMultiplier v r : ℝ) *
          ((n : ℝ) ^ c / 2) ≤ (decoderPathCap v r d n : ℝ) := by
      simpa [c] using hcap
    have hcoef : 4 * B₀ * S ≤
        4 * decoderBaselineConstant v r * S := by gcongr
    have hM : decoderPathMultiplier v r =
        16 * decoderBaselineConstant v r * S := by rfl
    rw [hM] at hcap'
    push_cast at hcap'
    calc
      ((4 * B₀ * S : ℕ) : ℝ) * (n : ℝ) ^ a ≤
          ((4 * decoderBaselineConstant v r * S : ℕ) : ℝ) *
            (n : ℝ) ^ c := by
        push_cast
        gcongr
      _ = (16 * (decoderBaselineConstant v r : ℝ) * (S : ℝ) *
            ((n : ℝ) ^ c / 2)) / 2 := by
        push_cast
        ring
      _ ≤ (decoderPathCap v r d n : ℝ) / 2 := by gcongr
  change (Real.exp 1 - 1) * ((B : ℝ) / L) ≤
    (decoderPathCap v r d n : ℝ) / 2
  exact hleft.trans hright

/-- Repeating every prescribed root a fixed positive number of times scales
both the schedule numerator and the available path cap by that number. -/
theorem eventually_rooted_scaled_quantitative_bound
    (P : RootedPattern v r) (hr : 0 < r)
    (hroot : P.root.card < v) (hrootLarge : r ≤ P.root.card)
    (hd : 0 < d) (scale : ℕ) (hscale : 0 < scale) :
    ∀ᶠ n : ℕ in atTop,
      (Real.exp 1 - 1) *
          ((faceScheduleNumeratorBound P n
              (scale * decoderInputCap d n) : ℝ) /
            rootedFaceLegalLowerBound P n
              (decoderInputCap d n)
              (scaledDecoderPathCap scale v r d n)) ≤
        (scaledDecoderPathCap scale v r d n : ℝ) / 2 := by
  have hlegal := eventually_rooted_scaled_legalLowerBound
    P hr hroot hd scale hscale
  have hcap := eventually_half_path_rpow_mul_le_cap
    (v := v) hr hd
  filter_upwards [hlegal, hcap, eventually_ge_atTop (1 : ℕ)] with
      n hlegal hcap hn
  let s := v - P.root.card
  let a := decoderInputExponent d
  let c := decoderPathExponent d
  let S := decoderScheduleConstant v r
  let B₀ := 2 ^ s
  let L := rootedFaceLegalLowerBound P n
    (decoderInputCap d n) (scaledDecoderPathCap scale v r d n)
  let B := faceScheduleNumeratorBound P n
    (scale * decoderInputCap d n)
  have hnpos : (0 : ℝ) < n := by positivity
  have hD := decoderInputCap_cast_le d n
  have hpowEq : (n : ℝ) ^ s * (n : ℝ) ^ a =
      (n : ℝ) ^ ((s : ℝ) + a) := by
    rw [← Real.rpow_natCast (n : ℝ) s]
    exact (Real.rpow_add hnpos _ _).symm
  have hB : (B : ℝ) ≤
      ((scale * S : ℕ) : ℝ) * (n : ℝ) ^ (s + a) := by
    dsimp [B, S]
    unfold faceScheduleNumeratorBound decoderScheduleConstant
    push_cast
    calc
      ((2 : ℝ) ^ (r - 1) * ((2 : ℝ) ^ v * (r : ℝ) ^ r) *
          (n : ℝ) ^ (v - P.root.card)) *
            ((scale : ℝ) * (decoderInputCap d n : ℝ)) =
        (scale : ℝ) *
          ((2 : ℝ) ^ (r - 1) * ((2 : ℝ) ^ v * (r : ℝ) ^ r)) *
            (n : ℝ) ^ s * (decoderInputCap d n : ℝ) := by
        dsimp [s]
        ring
      _ ≤ (scale : ℝ) *
          ((2 : ℝ) ^ (r - 1) * ((2 : ℝ) ^ v * (r : ℝ) ^ r)) *
            (n : ℝ) ^ s * (n : ℝ) ^ a := by
        gcongr
        simpa [a, decoderInputExponent] using hD
      _ = (scale : ℝ) *
          ((2 : ℝ) ^ (r - 1) * ((2 : ℝ) ^ v * (r : ℝ) ^ r)) *
            (n : ℝ) ^ (s + a) := by
        rw [show (scale : ℝ) *
              ((2 : ℝ) ^ (r - 1) * ((2 : ℝ) ^ v * (r : ℝ) ^ r)) *
                (n : ℝ) ^ s * (n : ℝ) ^ a =
            (scale : ℝ) *
              ((2 : ℝ) ^ (r - 1) * ((2 : ℝ) ^ v * (r : ℝ) ^ r)) *
                ((n : ℝ) ^ s * (n : ℝ) ^ a) by ring]
        rw [hpowEq]
  have hLposReal : (0 : ℝ) < L := by
    exact_mod_cast hlegal.1
  have hLlower : (n : ℝ) ^ s / (2 * B₀ : ℕ) ≤ (L : ℝ) := by
    simpa [L, s, B₀] using hlegal.2
  have hB₀nat : 0 < B₀ := by
    dsimp [B₀]
    positivity
  have hratio : (B : ℝ) / L ≤
      ((2 * B₀ * (scale * S) : ℕ) : ℝ) * (n : ℝ) ^ a := by
    apply (div_le_iff₀ hLposReal).2
    calc
      (B : ℝ) ≤ ((scale * S : ℕ) : ℝ) *
          (n : ℝ) ^ (s + a) := hB
      _ = ((scale * S : ℕ) : ℝ) *
          ((n : ℝ) ^ s * (n : ℝ) ^ a) := by
        rw [Real.rpow_add hnpos]
        rw [Real.rpow_natCast]
      _ ≤ ((scale * S : ℕ) : ℝ) *
          (((2 * B₀ : ℕ) : ℝ) * L * (n : ℝ) ^ a) := by
        gcongr
        have hden : (0 : ℝ) < (2 * B₀ : ℕ) := by
          exact_mod_cast (Nat.mul_pos (by omega : 0 < 2) hB₀nat)
        simpa [mul_comm] using (div_le_iff₀ hden).mp hLlower
      _ = ((2 * B₀ * (scale * S) : ℕ) : ℝ) *
          (n : ℝ) ^ a * L := by
        push_cast
        ring
  have hexpCoef : Real.exp 1 - 1 ≤ 2 := by
    linarith [Real.exp_one_lt_d9]
  have hleft : (Real.exp 1 - 1) * ((B : ℝ) / L) ≤
      ((4 * B₀ * (scale * S) : ℕ) : ℝ) * (n : ℝ) ^ a := by
    calc
      (Real.exp 1 - 1) * ((B : ℝ) / L) ≤
          2 * (((2 * B₀ * (scale * S) : ℕ) : ℝ) *
            (n : ℝ) ^ a) := by
        exact mul_le_mul hexpCoef hratio (by positivity) (by norm_num)
      _ = ((4 * B₀ * (scale * S) : ℕ) : ℝ) *
          (n : ℝ) ^ a := by
        push_cast
        ring
  have hac : a ≤ c := (decoder_exponent_identities hd).2.2.1.le
  have hpowac : (n : ℝ) ^ a ≤ (n : ℝ) ^ c :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) hac
  have hB₀le : B₀ ≤ decoderBaselineConstant v r := by
    dsimp [B₀, s, decoderBaselineConstant]
    exact Nat.pow_le_pow_right (by omega : 0 < 2) (by omega)
  have hright : ((4 * B₀ * (scale * S) : ℕ) : ℝ) *
        (n : ℝ) ^ a ≤
      (scaledDecoderPathCap scale v r d n : ℝ) / 2 := by
    have hcap' : (decoderPathMultiplier v r : ℝ) *
          ((n : ℝ) ^ c / 2) ≤ (decoderPathCap v r d n : ℝ) := by
      simpa [c] using hcap
    have hcoef : 4 * B₀ * S ≤
        4 * decoderBaselineConstant v r * S := by gcongr
    have hM : decoderPathMultiplier v r =
        16 * decoderBaselineConstant v r * S := by rfl
    rw [hM] at hcap'
    push_cast at hcap'
    have hbase :
        ((4 * B₀ * S : ℕ) : ℝ) * (n : ℝ) ^ a ≤
          ((4 * decoderBaselineConstant v r * S : ℕ) : ℝ) *
            (n : ℝ) ^ c := by
      push_cast
      exact mul_le_mul (by exact_mod_cast hcoef) hpowac
        (by positivity) (by positivity)
    calc
      ((4 * B₀ * (scale * S) : ℕ) : ℝ) * (n : ℝ) ^ a =
          (scale : ℝ) *
            (((4 * B₀ * S : ℕ) : ℝ) * (n : ℝ) ^ a) := by
        push_cast
        ring
      _ ≤
          (scale : ℝ) *
            (((4 * decoderBaselineConstant v r * S : ℕ) : ℝ) *
              (n : ℝ) ^ c) := by
        exact mul_le_mul_of_nonneg_left hbase (by positivity)
      _ = (scale : ℝ) *
          ((16 * (decoderBaselineConstant v r : ℝ) * (S : ℝ) *
            ((n : ℝ) ^ c / 2)) / 2) := by
        push_cast
        ring
      _ ≤ (scale : ℝ) *
          ((decoderPathCap v r d n : ℝ) / 2) := by gcongr
      _ = (scaledDecoderPathCap scale v r d n : ℝ) / 2 := by
        simp [scaledDecoderPathCap]
        ring
  change (Real.exp 1 - 1) * ((B : ℝ) / L) ≤
    (scaledDecoderPathCap scale v r d n : ℝ) / 2
  exact hleft.trans hright

/-- Two-scale form of the quantitative scheduling estimate.  The input
families may obey a stronger power bound than the cap demanded of the
random-greedy output; the strict denominator gap is exactly what makes the
input scheduling term asymptotically smaller than the output cap. -/
theorem eventually_rooted_twoScale_scaled_quantitative_bound
    {dInput dPath : ℕ}
    (P : RootedPattern v r) (hr : 0 < r)
    (hroot : P.root.card < v) (hrootLarge : r ≤ P.root.card)
    (hdInput : 0 < dInput) (hdPath : 0 < dPath)
    (hgap : dInput < 2 * dPath)
    (scale : ℕ) (hscale : 0 < scale) :
    ∀ᶠ n : ℕ in atTop,
      (Real.exp 1 - 1) *
          ((faceScheduleNumeratorBound P n
              (scale * decoderInputCap dInput n) : ℝ) /
            rootedFaceLegalLowerBound P n
              (decoderInputCap dInput n)
              (scaledDecoderPathCap scale v r dPath n)) ≤
        (scaledDecoderPathCap scale v r dPath n : ℝ) / 2 := by
  have hlegal := eventually_rooted_twoScale_scaled_legalLowerBound
    P hr hroot hdInput hdPath scale hscale
  have hcap := eventually_half_path_rpow_mul_le_cap
    (v := v) hr hdPath
  filter_upwards [hlegal, hcap, eventually_ge_atTop (1 : ℕ)] with
      n hlegal hcap hn
  let s := v - P.root.card
  let a := decoderInputExponent dInput
  let c := decoderPathExponent dPath
  let S := decoderScheduleConstant v r
  let B₀ := 2 ^ s
  let L := rootedFaceLegalLowerBound P n
    (decoderInputCap dInput n) (scaledDecoderPathCap scale v r dPath n)
  let B := faceScheduleNumeratorBound P n
    (scale * decoderInputCap dInput n)
  have hnpos : (0 : ℝ) < n := by positivity
  have hD := decoderInputCap_cast_le dInput n
  have hpowEq : (n : ℝ) ^ s * (n : ℝ) ^ a =
      (n : ℝ) ^ ((s : ℝ) + a) := by
    rw [← Real.rpow_natCast (n : ℝ) s]
    exact (Real.rpow_add hnpos _ _).symm
  have hB : (B : ℝ) ≤
      ((scale * S : ℕ) : ℝ) * (n : ℝ) ^ (s + a) := by
    dsimp [B, S]
    unfold faceScheduleNumeratorBound decoderScheduleConstant
    push_cast
    calc
      ((2 : ℝ) ^ (r - 1) * ((2 : ℝ) ^ v * (r : ℝ) ^ r) *
          (n : ℝ) ^ (v - P.root.card)) *
            ((scale : ℝ) * (decoderInputCap dInput n : ℝ)) =
        (scale : ℝ) *
          ((2 : ℝ) ^ (r - 1) * ((2 : ℝ) ^ v * (r : ℝ) ^ r)) *
            (n : ℝ) ^ s * (decoderInputCap dInput n : ℝ) := by
        dsimp [s]
        ring
      _ ≤ (scale : ℝ) *
          ((2 : ℝ) ^ (r - 1) * ((2 : ℝ) ^ v * (r : ℝ) ^ r)) *
            (n : ℝ) ^ s * (n : ℝ) ^ a := by
        gcongr
        simpa [a, decoderInputExponent] using hD
      _ = (scale : ℝ) *
          ((2 : ℝ) ^ (r - 1) * ((2 : ℝ) ^ v * (r : ℝ) ^ r)) *
            (n : ℝ) ^ (s + a) := by
        rw [show (scale : ℝ) *
              ((2 : ℝ) ^ (r - 1) * ((2 : ℝ) ^ v * (r : ℝ) ^ r)) *
                (n : ℝ) ^ s * (n : ℝ) ^ a =
            (scale : ℝ) *
              ((2 : ℝ) ^ (r - 1) * ((2 : ℝ) ^ v * (r : ℝ) ^ r)) *
                ((n : ℝ) ^ s * (n : ℝ) ^ a) by ring]
        rw [hpowEq]
  have hLposReal : (0 : ℝ) < L := by
    exact_mod_cast hlegal.1
  have hLlower : (n : ℝ) ^ s / (2 * B₀ : ℕ) ≤ (L : ℝ) := by
    simpa [L, s, B₀] using hlegal.2
  have hB₀nat : 0 < B₀ := by
    dsimp [B₀]
    positivity
  have hratio : (B : ℝ) / L ≤
      ((2 * B₀ * (scale * S) : ℕ) : ℝ) * (n : ℝ) ^ a := by
    apply (div_le_iff₀ hLposReal).2
    calc
      (B : ℝ) ≤ ((scale * S : ℕ) : ℝ) *
          (n : ℝ) ^ (s + a) := hB
      _ = ((scale * S : ℕ) : ℝ) *
          ((n : ℝ) ^ s * (n : ℝ) ^ a) := by
        rw [Real.rpow_add hnpos]
        rw [Real.rpow_natCast]
      _ ≤ ((scale * S : ℕ) : ℝ) *
          (((2 * B₀ : ℕ) : ℝ) * L * (n : ℝ) ^ a) := by
        gcongr
        have hden : (0 : ℝ) < (2 * B₀ : ℕ) := by
          exact_mod_cast (Nat.mul_pos (by omega : 0 < 2) hB₀nat)
        simpa [mul_comm] using (div_le_iff₀ hden).mp hLlower
      _ = ((2 * B₀ * (scale * S) : ℕ) : ℝ) *
          (n : ℝ) ^ a * L := by
        push_cast
        ring
  have hexpCoef : Real.exp 1 - 1 ≤ 2 := by
    linarith [Real.exp_one_lt_d9]
  have hleft : (Real.exp 1 - 1) * ((B : ℝ) / L) ≤
      ((4 * B₀ * (scale * S) : ℕ) : ℝ) * (n : ℝ) ^ a := by
    calc
      (Real.exp 1 - 1) * ((B : ℝ) / L) ≤
          2 * (((2 * B₀ * (scale * S) : ℕ) : ℝ) *
            (n : ℝ) ^ a) := by
        exact mul_le_mul hexpCoef hratio (by positivity) (by norm_num)
      _ = ((4 * B₀ * (scale * S) : ℕ) : ℝ) *
          (n : ℝ) ^ a := by
        push_cast
        ring
  have hac : a ≤ c := by
    exact (decoderInputExponent_lt_decoderPathExponent
      hdInput hdPath hgap).le
  have hpowac : (n : ℝ) ^ a ≤ (n : ℝ) ^ c :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) hac
  have hB₀le : B₀ ≤ decoderBaselineConstant v r := by
    dsimp [B₀, s, decoderBaselineConstant]
    exact Nat.pow_le_pow_right (by omega : 0 < 2) (by omega)
  have hright : ((4 * B₀ * (scale * S) : ℕ) : ℝ) *
        (n : ℝ) ^ a ≤
      (scaledDecoderPathCap scale v r dPath n : ℝ) / 2 := by
    have hcap' : (decoderPathMultiplier v r : ℝ) *
          ((n : ℝ) ^ c / 2) ≤ (decoderPathCap v r dPath n : ℝ) := by
      simpa [c] using hcap
    have hcoef : 4 * B₀ * S ≤
        4 * decoderBaselineConstant v r * S := by gcongr
    have hM : decoderPathMultiplier v r =
        16 * decoderBaselineConstant v r * S := by rfl
    rw [hM] at hcap'
    push_cast at hcap'
    have hbase :
        ((4 * B₀ * S : ℕ) : ℝ) * (n : ℝ) ^ a ≤
          ((4 * decoderBaselineConstant v r * S : ℕ) : ℝ) *
            (n : ℝ) ^ c := by
      push_cast
      exact mul_le_mul (by exact_mod_cast hcoef) hpowac
        (by positivity) (by positivity)
    calc
      ((4 * B₀ * (scale * S) : ℕ) : ℝ) * (n : ℝ) ^ a =
          (scale : ℝ) *
            (((4 * B₀ * S : ℕ) : ℝ) * (n : ℝ) ^ a) := by
        push_cast
        ring
      _ ≤
          (scale : ℝ) *
            (((4 * decoderBaselineConstant v r * S : ℕ) : ℝ) *
              (n : ℝ) ^ c) := by
        exact mul_le_mul_of_nonneg_left hbase (by positivity)
      _ = (scale : ℝ) *
          ((16 * (decoderBaselineConstant v r : ℝ) * (S : ℝ) *
            ((n : ℝ) ^ c / 2)) / 2) := by
        push_cast
        ring
      _ ≤ (scale : ℝ) *
          ((decoderPathCap v r dPath n : ℝ) / 2) := by gcongr
      _ = (scaledDecoderPathCap scale v r dPath n : ℝ) / 2 := by
        simp [scaledDecoderPathCap]
        ring
  change (Real.exp 1 - 1) * ((B : ℝ) / L) ≤
    (scaledDecoderPathCap scale v r dPath n : ℝ) / 2
  exact hleft.trans hright

/-- The polynomial family of face counters is dominated by the exponential
tail from the growing generic path cap. -/
theorem eventually_rooted_exponential_union_bound
    (P : RootedPattern v r) (hr : 0 < r) (hd : 0 < d) :
    ∀ᶠ n : ℕ in atTop,
      (Fintype.card (RelevantFaceLoadTarget P n) : ℝ) *
          Real.exp (-(decoderPathCap v r d n : ℝ) / 2) < 1 := by
  let c := decoderPathExponent d
  let M := decoderPathMultiplier v r
  let C₀ : ℝ := P.freeEdges.card
  have hc : 0 < c := by
    simpa [c] using (decoder_exponent_identities hd).2.2.2
  have hMnat : 0 < M := decoderPathMultiplier_pos v r hr
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
  have hcardNat : Fintype.card (RelevantFaceLoadTarget P n) ≤
      P.freeEdges.card * n ^ (r - 1) :=
    (card_relevantFaceLoadTarget_le P n).trans
      (Nat.mul_le_mul_left _ (Nat.choose_le_pow n (r - 1)))
  have hcardReal :
      (Fintype.card (RelevantFaceLoadTarget P n) : ℝ) ≤
        (P.freeEdges.card : ℝ) * (n : ℝ) ^ (r - 1) := by
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
    (Fintype.card (RelevantFaceLoadTarget P n) : ℝ) *
          Real.exp (-(decoderPathCap v r d n : ℝ) / 2) ≤
        (P.freeEdges.card : ℝ) * (n : ℝ) ^ (r - 1) *
          Real.exp (-(decoderPathCap v r d n : ℝ) / 2) := by
      gcongr
    _ ≤ (P.freeEdges.card : ℝ) * (n : ℝ) ^ (r - 1) *
          Real.exp (-((M : ℝ) / 4) * (n : ℝ) ^ c) := by
      gcongr
      convert neg_le_neg hspent using 1 <;> ring
    _ = C₀ * ((n : ℝ) ^ (r - 1) *
          Real.exp (-((M : ℝ) / 4) * (n : ℝ) ^ c)) := by
      dsimp [C₀]
      ring
    _ < 1 := hnsmall

/-- A positive fixed scaling of the path cap can only strengthen the
exponential union bound. -/
theorem eventually_rooted_scaled_exponential_union_bound
    (P : RootedPattern v r) (hr : 0 < r) (hd : 0 < d)
    (scale : ℕ) (hscale : 0 < scale) :
    ∀ᶠ n : ℕ in atTop,
      (Fintype.card (RelevantFaceLoadTarget P n) : ℝ) *
          Real.exp (-(scaledDecoderPathCap scale v r d n : ℝ) / 2) < 1 := by
  have hbase := eventually_rooted_exponential_union_bound P hr hd
  filter_upwards [hbase] with n hn
  have hcapNat : decoderPathCap v r d n ≤
      scaledDecoderPathCap scale v r d n := by
    unfold scaledDecoderPathCap
    calc
      decoderPathCap v r d n = 1 * decoderPathCap v r d n := by simp
      _ ≤ scale * decoderPathCap v r d n :=
        Nat.mul_le_mul_right _ hscale
  have hcapReal : (decoderPathCap v r d n : ℝ) ≤
      (scaledDecoderPathCap scale v r d n : ℝ) := by
    exact_mod_cast hcapNat
  calc
    (Fintype.card (RelevantFaceLoadTarget P n) : ℝ) *
          Real.exp (-(scaledDecoderPathCap scale v r d n : ℝ) / 2) ≤
        (Fintype.card (RelevantFaceLoadTarget P n) : ℝ) *
          Real.exp (-(decoderPathCap v r d n : ℝ) / 2) := by
      gcongr
    _ < 1 := hn

/-- Eventual simultaneous placement for any fixed rooted pattern whose root
contains at least `r` vertices and is not the whole pattern. -/
theorem eventually_exists_boundedRootedFamilyEmbeddings_of_power_bound
    (P : RootedPattern v r) (hr : 0 < r)
    (hrootNonempty : P.root.Nonempty)
    (hroot : P.root.card < v) (hrootLarge : r ≤ P.root.card)
    (hd : 0 < d) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (roots forbidden : Finset (Finset (Fin n))),
      (∀ Q ∈ roots, Q.card = P.root.card) →
      (∀ e ∈ forbidden, e.card = r) →
      (∀ J : Finset (Fin n), J.card = r - 1 →
        (Reserve.localDegree roots J) ^ d ≤ n ^ (d - 1)) →
      (∀ J : Finset (Fin n), J.card = r - 1 →
        (Reserve.localDegree forbidden J) ^ d ≤ n ^ (d - 1)) →
      Nonempty (BoundedRootedFamilyEmbeddings P roots forbidden
        (decoderPathCap v r d n)) := by
  have hlegal := eventually_rooted_legalLowerBound P hr hroot hd
  have hquant := eventually_rooted_quantitative_bound
    P hr hroot hrootLarge hd
  have hcard := eventually_rooted_exponential_union_bound P hr hd
  filter_upwards [hlegal, hquant, hcard, eventually_ge_atTop v] with
      n hlegal hquant hcard hvn
  intro roots forbidden hrootsUniform hforbiddenUniform hrootDegree
    hforbiddenDegree
  by_cases hroots : roots = ∅
  · subst roots
    refine ⟨{
      embedding := fun Q hQ ↦ False.elim (show False by simpa using hQ)
      root_image := ?_
      free_disjoint_forbidden := ?_
      free_pairwise := ?_
      freeUnion := ∅
      image_subset_freeUnion := ?_
      free_degree_le := ?_ }⟩
    · intro Q hQ
      simp at hQ
    · intro Q hQ
      simp at hQ
    · intro Q hQ
      simp at hQ
    · intro Q hQ
      simp at hQ
    · intro J hJ
      simp [Reserve.localDegree]
  · let : Nonempty (Fin v ↪ Fin n) := ⟨Fin.castLEEmb hvn⟩
    obtain ⟨Q₀, hQ₀⟩ := Finset.nonempty_iff_ne_empty.mpr hroots
    apply exists_boundedRootedFamilyEmbeddings_of_finite_bounds
      P roots forbidden hrootsUniform hrootNonempty (by omega)
      hforbiddenUniform Q₀ hQ₀
    · intro J hJ
      exact le_decoderInputCap_of_pow_le d n _ hd (hrootDegree J hJ)
    · intro J hJ
      exact le_decoderInputCap_of_pow_le d n _ hd
        (hforbiddenDegree J hJ)
    · exact hr
    · exact hlegal.1
    · exact hquant
    · exact hcard

/-- Eventual simultaneous placement of a fixed positive number of copies at
every root.  The root and forbidden families obey the same codimension-one
power bound as in the single-copy theorem. -/
theorem eventually_exists_boundedMultiRootedFamilyEmbeddings_of_power_bound
    (P : RootedPattern v r) (hr : 0 < r)
    (hrootNonempty : P.root.Nonempty)
    (hroot : P.root.card < v) (hrootLarge : r ≤ P.root.card)
    (hd : 0 < d) (multiplicity : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (roots forbidden : Finset (Finset (Fin n))),
      (∀ Q ∈ roots, Q.card = P.root.card) →
      (∀ e ∈ forbidden, e.card = r) →
      (∀ J : Finset (Fin n), J.card = r - 1 →
        (Reserve.localDegree roots J) ^ d ≤ n ^ (d - 1)) →
      (∀ J : Finset (Fin n), J.card = r - 1 →
        (Reserve.localDegree forbidden J) ^ d ≤ n ^ (d - 1)) →
      Nonempty (BoundedMultiRootedFamilyEmbeddings P roots forbidden
        multiplicity (scaledDecoderPathCap multiplicity v r d n)) := by
  by_cases hm : multiplicity = 0
  · subst multiplicity
    filter_upwards [] with n
    intro roots forbidden hrootsUniform hforbiddenUniform hrootDegree
      hforbiddenDegree
    refine ⟨{
      embedding := fun Q hQ t ↦ Fin.elim0 t
      root_image := ?_
      free_disjoint_forbidden := ?_
      free_pairwise := ?_
      freeUnion := ∅
      image_subset_freeUnion := ?_
      free_uniform := ?_
      freeUnion_disjoint_forbidden := ?_
      free_degree_le := ?_ }⟩
    · intro Q hQ t
      exact Fin.elim0 t
    · intro Q hQ t
      exact Fin.elim0 t
    · intro Q hQ t
      exact Fin.elim0 t
    · intro Q hQ t
      exact Fin.elim0 t
    · intro g hg
      simp at hg
    · simp
    · intro J hJ
      simp [Reserve.localDegree]
  · have hmpos : 0 < multiplicity := Nat.pos_of_ne_zero hm
    have hlegal := eventually_rooted_scaled_legalLowerBound
      P hr hroot hd multiplicity hmpos
    have hquant := eventually_rooted_scaled_quantitative_bound
      P hr hroot hrootLarge hd multiplicity hmpos
    have hcard := eventually_rooted_scaled_exponential_union_bound
      P hr hd multiplicity hmpos
    filter_upwards [hlegal, hquant, hcard, eventually_ge_atTop v] with
        n hlegal hquant hcard hvn
    intro roots forbidden hrootsUniform hforbiddenUniform hrootDegree
      hforbiddenDegree
    by_cases hroots : roots = ∅
    · subst roots
      refine ⟨{
        embedding := fun Q hQ t ↦ False.elim (show False by simpa using hQ)
        root_image := ?_
        free_disjoint_forbidden := ?_
        free_pairwise := ?_
        freeUnion := ∅
        image_subset_freeUnion := ?_
        free_uniform := ?_
        freeUnion_disjoint_forbidden := ?_
        free_degree_le := ?_ }⟩
      · intro Q hQ t
        simp at hQ
      · intro Q hQ t
        simp at hQ
      · intro Q hQ t
        simp at hQ
      · intro Q hQ t
        simp at hQ
      · intro g hg
        simp at hg
      · simp
      · intro J hJ
        simp [Reserve.localDegree]
    · let : Nonempty (Fin v ↪ Fin n) := ⟨Fin.castLEEmb hvn⟩
      obtain ⟨Q₀, hQ₀⟩ := Finset.nonempty_iff_ne_empty.mpr hroots
      apply exists_boundedMultiRootedFamilyEmbeddings_of_finite_bounds
        P roots forbidden hrootsUniform hrootNonempty (by omega)
        hforbiddenUniform Q₀ hQ₀
      · intro J hJ
        exact le_decoderInputCap_of_pow_le d n _ hd (hrootDegree J hJ)
      · intro J hJ
        exact le_decoderInputCap_of_pow_le d n _ hd
          (hforbiddenDegree J hJ)
      · exact hr
      · exact hlegal.1
      · exact hquant
      · exact hcard

/-- Graded-exponent simultaneous placement.  The prescribed root and
forbidden families satisfy the `dInput` power bound, while the output free
union is only required to satisfy the weaker `dPath` path cap. -/
theorem eventually_exists_boundedMultiRootedFamilyEmbeddings_of_two_power_bounds
    {dInput dPath : ℕ}
    (P : RootedPattern v r) (hr : 0 < r)
    (hrootNonempty : P.root.Nonempty)
    (hroot : P.root.card < v) (hrootLarge : r ≤ P.root.card)
    (hdInput : 0 < dInput) (hdPath : 0 < dPath)
    (hgap : dInput < 2 * dPath) (multiplicity : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (roots forbidden : Finset (Finset (Fin n))),
      (∀ Q ∈ roots, Q.card = P.root.card) →
      (∀ e ∈ forbidden, e.card = r) →
      (∀ J : Finset (Fin n), J.card = r - 1 →
        (Reserve.localDegree roots J) ^ dInput ≤ n ^ (dInput - 1)) →
      (∀ J : Finset (Fin n), J.card = r - 1 →
        (Reserve.localDegree forbidden J) ^ dInput ≤ n ^ (dInput - 1)) →
      Nonempty (BoundedMultiRootedFamilyEmbeddings P roots forbidden
        multiplicity (scaledDecoderPathCap multiplicity v r dPath n)) := by
  by_cases hm : multiplicity = 0
  · subst multiplicity
    filter_upwards [] with n
    intro roots forbidden hrootsUniform hforbiddenUniform hrootDegree
      hforbiddenDegree
    refine ⟨{
      embedding := fun Q hQ t ↦ Fin.elim0 t
      root_image := ?_
      free_disjoint_forbidden := ?_
      free_pairwise := ?_
      freeUnion := ∅
      image_subset_freeUnion := ?_
      free_uniform := ?_
      freeUnion_disjoint_forbidden := ?_
      free_degree_le := ?_ }⟩
    · intro Q hQ t
      exact Fin.elim0 t
    · intro Q hQ t
      exact Fin.elim0 t
    · intro Q hQ t
      exact Fin.elim0 t
    · intro Q hQ t
      exact Fin.elim0 t
    · intro g hg
      simp at hg
    · simp
    · intro J hJ
      simp [Reserve.localDegree]
  · have hmpos : 0 < multiplicity := Nat.pos_of_ne_zero hm
    have hlegal := eventually_rooted_twoScale_scaled_legalLowerBound
      P hr hroot hdInput hdPath multiplicity hmpos
    have hquant := eventually_rooted_twoScale_scaled_quantitative_bound
      P hr hroot hrootLarge hdInput hdPath hgap multiplicity hmpos
    have hcard := eventually_rooted_scaled_exponential_union_bound
      P hr hdPath multiplicity hmpos
    filter_upwards [hlegal, hquant, hcard, eventually_ge_atTop v] with
        n hlegal hquant hcard hvn
    intro roots forbidden hrootsUniform hforbiddenUniform hrootDegree
      hforbiddenDegree
    by_cases hroots : roots = ∅
    · subst roots
      refine ⟨{
        embedding := fun Q hQ t ↦ False.elim (show False by simpa using hQ)
        root_image := ?_
        free_disjoint_forbidden := ?_
        free_pairwise := ?_
        freeUnion := ∅
        image_subset_freeUnion := ?_
        free_uniform := ?_
        freeUnion_disjoint_forbidden := ?_
        free_degree_le := ?_ }⟩
      · intro Q hQ t
        simp at hQ
      · intro Q hQ t
        simp at hQ
      · intro Q hQ t
        simp at hQ
      · intro Q hQ t
        simp at hQ
      · intro g hg
        simp at hg
      · simp
      · intro J hJ
        simp [Reserve.localDegree]
    · let : Nonempty (Fin v ↪ Fin n) := ⟨Fin.castLEEmb hvn⟩
      obtain ⟨Q₀, hQ₀⟩ := Finset.nonempty_iff_ne_empty.mpr hroots
      apply exists_boundedMultiRootedFamilyEmbeddings_of_finite_bounds
        P roots forbidden hrootsUniform hrootNonempty (by omega)
        hforbiddenUniform Q₀ hQ₀
      · intro J hJ
        exact le_decoderInputCap_of_pow_le dInput n _ hdInput
          (hrootDegree J hJ)
      · intro J hJ
        exact le_decoderInputCap_of_pow_le dInput n _ hdInput
          (hforbiddenDegree J hJ)
      · exact hr
      · exact hlegal.1
      · exact hquant
      · exact hcard

end

end Erdos722.RootedFamilyAsymptotic
