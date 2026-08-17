/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

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

import ErdosProblems.Erdos636.CandidateFamily

/-!
# Eventual candidate-family arithmetic for Erdős Problem 636

The exact finite losses grow as `n^(63 + 1/5)` and
`n^(64 * (19/20) + 3) = n^(63 + 4/5)`, whereas the reservoir contains
order `n^64` many `64`-sets.  This file packages that strict exponent gap.
-/

namespace Erdos636.CandidateThresholds

noncomputable section

def reservoirSize (cR : ℝ) (n : ℕ) : ℕ :=
  ⌊(cR / 4) * (n : ℝ)⌋₊

def sunflowerSize (n : ℕ) : ℕ :=
  ⌊(n : ℝ) ^ (19 / 20 : ℝ)⌋₊

def exceptionalSize (m : ℕ) : ℕ :=
  ⌈(m : ℝ) ^ (1 / 5 : ℝ)⌉₊

def candidateTarget (n m : ℕ) : ℕ :=
  (64 : ℕ).factorial * (sunflowerSize n - 1) ^ 64 * (64 * m + 1) ^ 3

lemma reservoirSize_upper (cR : ℝ) (n : ℕ) (hcR : 0 ≤ cR) :
    (reservoirSize cR n : ℝ) ≤ cR / 4 * n := by
  exact Nat.floor_le
    (mul_nonneg (div_nonneg hcR (by norm_num)) (Nat.cast_nonneg n))

lemma reservoirSize_lower {cR : ℝ} {n : ℕ}
    (hn : 2 ≤ cR / 4 * n) :
    cR / 8 * n ≤ (reservoirSize cR n : ℝ) := by
  have hfloor := Nat.lt_floor_add_one (cR / 4 * (n : ℝ))
  dsimp [reservoirSize]
  linarith

private lemma cast_sunflowerSize_le (n : ℕ) :
    (sunflowerSize n : ℝ) ≤ (n : ℝ) ^ (19 / 20 : ℝ) := by
  exact Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg n) _)

private lemma rpow_lt_sunflowerSize_add_one (n : ℕ) :
    (n : ℝ) ^ (19 / 20 : ℝ) < sunflowerSize n + 1 := by
  exact Nat.lt_floor_add_one _

private lemma cast_exceptionalSize_lt_add_one (m : ℕ) :
    (exceptionalSize m : ℝ) < (m : ℝ) ^ (1 / 5 : ℝ) + 1 := by
  exact Nat.ceil_lt_add_one (Real.rpow_nonneg (Nat.cast_nonneg m) _)

/-- Multiplying a power by the missing positive power gives the larger
power.  This small adapter keeps the main proof's exponent arithmetic
readable. -/
private lemma mul_rpow_gap {n C D p q : ℝ} (hn : 0 < n)
    (hC : C ≤ D * n ^ (q - p)) :
    C * n ^ p ≤ D * n ^ q := by
  have h := mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hn.le p)
  calc
    C * n ^ p ≤ D * n ^ (q - p) * n ^ p := by simpa [mul_assoc] using h
    _ = D * n ^ q := by
      rw [mul_assoc, ← Real.rpow_add hn]
      ring_nf

private lemma matching_numeric {y z e r : ℝ}
    (hy : 1 ≤ y) (hz : 4 ≤ z) (he : e ≤ z + 2)
    (hr : y * z - 1 < r) :
    (1 / 4 : ℝ) * y * e ≤ r := by
  have hy0 : 0 ≤ y := zero_le_one.trans hy
  have hz0 : 0 ≤ z := by linarith
  have hlt : (1 / 4 : ℝ) * y * e < y * z - 1 := by
    nlinarith [mul_nonneg hy0 hz0]
  exact (hlt.trans hr).le

/-- Simultaneous eventual arithmetic package consumed by the fixed-ambient
structural assembly. -/
theorem exists_candidateThreshold (cR : ℝ) (hcR : 0 < cR) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ m : ℕ,
      cR * n ≤ (m : ℝ) → m ≤ n →
        2 ≤ sunflowerSize n ∧
        64 * m ^ (64 - 1) * exceptionalSize m + candidateTarget n m <
          (reservoirSize cR n).choose 64 ∧
        (1 / 4 : ℝ) * (n : ℝ) ^ (3 / 4 : ℝ) *
            (exceptionalSize m + 1) ≤ sunflowerSize n ∧
        (reservoirSize cR n : ℝ) ≤ cR / 4 * n ∧
        cR / 8 * n ≤ (reservoirSize cR n : ℝ) := by
  let a : ℝ := cR / 8
  let L : ℝ := (a / 2) ^ 64 / ((64 : ℕ).factorial : ℝ)
  let T : ℝ := (((64 : ℕ).factorial : ℕ) : ℝ) * 65 ^ 3
  have ha : 0 < a := by dsimp [a]; positivity
  have hL : 0 < L := by dsimp [L]; positivity
  have hT : 0 < T := by dsimp [T]; positivity
  obtain ⟨Nlin, hNlin⟩ := Erdos88.exists_nat_rpow_ge 1
    (max (8 / cR) (128 / a)) (by norm_num)
  obtain ⟨Nsun, hNsun⟩ := Erdos88.exists_nat_rpow_ge
    (19 / 20 : ℝ) 3 (by norm_num)
  obtain ⟨N02, hN02⟩ := Erdos88.exists_nat_rpow_ge
    (1 / 5 : ℝ) (max 4 (4 * T / L)) (by norm_num)
  obtain ⟨N08, hN08⟩ := Erdos88.exists_nat_rpow_ge
    (4 / 5 : ℝ) (512 / L) (by norm_num)
  let N := max 1 (max Nlin (max Nsun (max N02 N08)))
  refine ⟨N, ?_⟩
  intro n hn m _hmLower hmn
  have hn1 : 1 ≤ n := (le_max_left 1 _).trans hn
  have hnpos : 0 < n := by omega
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hnreal1 : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have htail : max Nlin (max Nsun (max N02 N08)) ≤ n :=
    (le_max_right 1 _).trans hn
  have hNlin' : Nlin ≤ n := (le_max_left _ _).trans htail
  have htail2 : max Nsun (max N02 N08) ≤ n :=
    (le_max_right Nlin _).trans htail
  have hNsun' : Nsun ≤ n := (le_max_left _ _).trans htail2
  have htail3 : max N02 N08 ≤ n := (le_max_right Nsun _).trans htail2
  have hN02' : N02 ≤ n := (le_max_left _ _).trans htail3
  have hN08' : N08 ≤ n := (le_max_right _ _).trans htail3
  have hlin := hNlin n hNlin'
  have hlin' : max (8 / cR) (128 / a) ≤ (n : ℝ) := by
    simpa using hlin
  have hsunpow := hNsun n hNsun'
  have hpow02 := hN02 n hN02'
  have hpow08 := hN08 n hN08'
  have hcRn : 2 ≤ cR / 4 * (n : ℝ) := by
    have h8 : 8 / cR ≤ (n : ℝ) := (le_max_left _ _).trans hlin'
    rw [div_le_iff₀ hcR] at h8
    nlinarith
  have hsLower : a * n ≤ (reservoirSize cR n : ℝ) := by
    simpa [a] using reservoirSize_lower hcRn
  have han128 : (128 : ℝ) ≤ a * n := by
    have h128 : 128 / a ≤ (n : ℝ) := (le_max_right _ _).trans hlin'
    rw [div_le_iff₀ ha] at h128
    simpa [mul_comm] using h128
  have hr2 : 2 ≤ sunflowerSize n := by
    rw [sunflowerSize, Nat.le_floor_iff' (by decide : (2 : ℕ) ≠ 0)]
    exact (by norm_num : (2 : ℝ) ≤ 3).trans hsunpow
  have hmreal : (m : ℝ) ≤ n := by exact_mod_cast hmn
  have hmPow : (m : ℝ) ^ (1 / 5 : ℝ) ≤
      (n : ℝ) ^ (1 / 5 : ℝ) :=
    Real.rpow_le_rpow (Nat.cast_nonneg m) hmreal (by norm_num)
  have hexc : (exceptionalSize m : ℝ) ≤
      (n : ℝ) ^ (1 / 5 : ℝ) + 1 :=
    (cast_exceptionalSize_lt_add_one m).le.trans (by linarith)
  have hpow02four : (4 : ℝ) ≤ (n : ℝ) ^ (1 / 5 : ℝ) :=
    (le_max_left _ _).trans hpow02
  have hpow08large : 512 / L ≤ (n : ℝ) ^ (4 / 5 : ℝ) := hpow08
  have hTlarge : 4 * T / L ≤ (n : ℝ) ^ (1 / 5 : ℝ) :=
    (le_max_right _ _).trans hpow02
  have herr :
      ((64 * m ^ (64 - 1) * exceptionalSize m : ℕ) : ℝ) ≤
        128 * (n : ℝ) ^ (316 / 5 : ℝ) := by
    push_cast
    norm_num
    calc
      64 * (m : ℝ) ^ 63 * exceptionalSize m ≤
          64 * (n : ℝ) ^ 63 *
            ((n : ℝ) ^ (1 / 5 : ℝ) + 1) := by gcongr
      _ ≤ 128 * (n : ℝ) ^ 63 *
            (n : ℝ) ^ (1 / 5 : ℝ) := by
          have honepow : (1 : ℝ) ≤ (n : ℝ) ^ (1 / 5 : ℝ) :=
            Real.one_le_rpow hnreal1 (by norm_num)
          have hp63 : 0 ≤ (n : ℝ) ^ 63 := by positivity
          nlinarith
      _ = 128 * (n : ℝ) ^ (316 / 5 : ℝ) := by
          rw [mul_assoc, ← Real.rpow_natCast, ← Real.rpow_add hnreal]
          norm_num
  have hrUpper : (sunflowerSize n : ℝ) ≤
      (n : ℝ) ^ (19 / 20 : ℝ) := cast_sunflowerSize_le n
  have hbaseUpper : 64 * m + 1 ≤ 65 * n := by omega
  have htarget : (candidateTarget n m : ℝ) ≤
      T * (n : ℝ) ^ (319 / 5 : ℝ) := by
    rw [candidateTarget]
    push_cast
    calc
      (((64 : ℕ).factorial : ℕ) : ℝ) *
          ((sunflowerSize n - 1 : ℕ) : ℝ) ^ 64 *
          (64 * (m : ℝ) + 1) ^ 3 ≤
        (((64 : ℕ).factorial : ℕ) : ℝ) *
          ((n : ℝ) ^ (19 / 20 : ℝ)) ^ 64 *
          (((65 : ℕ) : ℝ) * n) ^ 3 := by
            gcongr
            · exact (Nat.cast_le.mpr (Nat.sub_le _ _)).trans hrUpper
            · exact_mod_cast hbaseUpper
      _ = T * (n : ℝ) ^ (319 / 5 : ℝ) := by
        rw [← Real.rpow_mul_natCast hnreal.le, mul_pow]
        calc
          (((64 : ℕ).factorial : ℕ) : ℝ) *
              (n : ℝ) ^ (19 / 20 * (64 : ℝ)) *
              ((65 : ℝ) ^ 3 * (n : ℝ) ^ 3) =
            ((((64 : ℕ).factorial : ℕ) : ℝ) * 65 ^ 3) *
              ((n : ℝ) ^ (19 / 20 * (64 : ℝ)) *
                (n : ℝ) ^ 3) := by ring
          _ = T * (n : ℝ) ^ (319 / 5 : ℝ) := by
            have hn3 : (n : ℝ) ^ 3 = (n : ℝ) ^ (3 : ℝ) :=
              (Real.rpow_natCast (n : ℝ) 3).symm
            rw [hn3, ← Real.rpow_add hnreal]
            norm_num [T]
  have h128coefficient :
      (128 : ℝ) ≤ L / 4 * (n : ℝ) ^ (4 / 5 : ℝ) := by
    have hscaled := mul_le_mul_of_nonneg_left hpow08large hL.le
    rw [mul_div_cancel₀ 512 hL.ne'] at hscaled
    nlinarith
  have hTcoefficient :
      T ≤ L / 4 * (n : ℝ) ^ (1 / 5 : ℝ) := by
    have hscaled := mul_le_mul_of_nonneg_left hTlarge hL.le
    rw [mul_div_cancel₀ (4 * T) hL.ne'] at hscaled
    nlinarith
  have herrQuarter :
      128 * (n : ℝ) ^ (316 / 5 : ℝ) ≤
        L / 4 * (n : ℝ) ^ (64 : ℝ) := by
    have hc : (128 : ℝ) ≤
        L / 4 * (n : ℝ) ^ ((64 : ℝ) - 316 / 5) := by
      norm_num
      exact h128coefficient
    have hgap := mul_rpow_gap (n := (n : ℝ)) (C := 128) (D := L / 4)
      (p := 316 / 5) (q := 64) hnreal hc
    exact hgap
  have htargetQuarter :
      T * (n : ℝ) ^ (319 / 5 : ℝ) ≤
        L / 4 * (n : ℝ) ^ (64 : ℝ) := by
    have hc : T ≤ L / 4 * (n : ℝ) ^ ((64 : ℝ) - 319 / 5) := by
      rw [show (64 : ℝ) - 319 / 5 = 1 / 5 by norm_num]
      exact hTcoefficient
    have hgap := mul_rpow_gap (n := (n : ℝ)) (C := T) (D := L / 4)
      (p := 319 / 5) (q := 64) hnreal hc
    exact hgap
  have hsBig : (128 : ℝ) ≤ (reservoirSize cR n : ℝ) :=
    han128.trans hsLower
  have hsSub : 64 ≤ reservoirSize cR n + 1 := by
    exact_mod_cast (show (64 : ℝ) ≤ reservoirSize cR n + 1 by linarith)
  have hchooseBase : a / 2 * n ≤
      ((reservoirSize cR n + 1 - 64 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hsSub]
    push_cast
    nlinarith
  have hchoose : L * (n : ℝ) ^ (64 : ℝ) ≤
      ((reservoirSize cR n).choose 64 : ℝ) := by
    calc
      L * (n : ℝ) ^ (64 : ℝ) = L * (n : ℝ) ^ 64 := by
        congr 1
        exact Real.rpow_natCast (n : ℝ) 64
      _ =
          (a / 2 * n) ^ 64 / (((64 : ℕ).factorial : ℕ) : ℝ) := by
            dsimp [L]
            ring
      _ ≤ (((reservoirSize cR n + 1 - 64 : ℕ) : ℝ) ^ 64) /
          (((64 : ℕ).factorial : ℕ) : ℝ) := by gcongr
      _ ≤ ((reservoirSize cR n).choose 64 : ℝ) :=
        Nat.pow_le_choose 64 (reservoirSize cR n)
  have hcandidate :
      64 * m ^ (64 - 1) * exceptionalSize m + candidateTarget n m <
        (reservoirSize cR n).choose 64 := by
    exact_mod_cast (calc
      ((64 * m ^ (64 - 1) * exceptionalSize m +
          candidateTarget n m : ℕ) : ℝ)
          ≤ L / 4 * (n : ℝ) ^ (64 : ℝ) +
              L / 4 * (n : ℝ) ^ (64 : ℝ) := by
            rw [Nat.cast_add]
            exact add_le_add (herr.trans herrQuarter)
              (htarget.trans htargetQuarter)
      _ = L / 2 * (n : ℝ) ^ (64 : ℝ) := by ring
      _ < L * (n : ℝ) ^ (64 : ℝ) := by
        have hn64 : 0 < (n : ℝ) ^ (64 : ℝ) :=
          Real.rpow_pos_of_pos hnreal _
        exact mul_lt_mul_of_pos_right (half_lt_self hL) hn64
      _ ≤ ((reservoirSize cR n).choose 64 : ℝ) := hchoose)
  have hpow75one : (1 : ℝ) ≤ (n : ℝ) ^ (3 / 4 : ℝ) :=
    Real.one_le_rpow hnreal1 (by norm_num)
  have hrLower : (n : ℝ) ^ (19 / 20 : ℝ) - 1 < sunflowerSize n := by
    linarith [rpow_lt_sunflowerSize_add_one n]
  have hmatching :
      (1 / 4 : ℝ) * (n : ℝ) ^ (3 / 4 : ℝ) *
          (exceptionalSize m + 1) ≤ sunflowerSize n := by
    have hdecomp :
        (n : ℝ) ^ (19 / 20 : ℝ) =
          (n : ℝ) ^ (3 / 4 : ℝ) *
            (n : ℝ) ^ (1 / 5 : ℝ) := by
      rw [← Real.rpow_add hnreal]
      norm_num
    have hexcOne : ((exceptionalSize m + 1 : ℕ) : ℝ) ≤
        (n : ℝ) ^ (1 / 5 : ℝ) + 2 := by
      push_cast
      linarith
    change (1 / 4 : ℝ) * (n : ℝ) ^ (3 / 4 : ℝ) *
        ((exceptionalSize m : ℝ) + 1) ≤ (sunflowerSize n : ℝ)
    apply matching_numeric hpow75one hpow02four (by linarith) ?_
    rw [← hdecomp]
    exact hrLower
  exact ⟨hr2, hcandidate, hmatching,
    reservoirSize_upper cR n hcR.le, hsLower⟩

end

end Erdos636.CandidateThresholds
