/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.UpperSquarefreePrefix
import ErdosProblems.Erdos446.UpperPowerfulReduction

/-!
# Erdős Problem 446: numerical cutoffs for removal of powerful parts

This file records one simultaneous eventual choice of the numerical cutoffs
used in Ford's squarefree reduction.  The shell start is rounded upward only
after the real power has been formed; the additional integral factors make
the two division estimates exact.
-/

namespace Erdos446

open Finset Set Filter Real
open scoped BigOperators Topology

noncomputable section

/-- Ford's cutoff for the powerful part. -/
noncomputable def fordPowerfulCutoff (Y : ℕ) : ℕ :=
  Nat.floor ((Y : ℝ) ^ (1 / 8 : ℝ))

/-- A division-friendly upward rounding of Ford's squarefree shell start.
It lies between `8 v Y^(2/3)` and `16 v Y^(2/3)` once `Y ≥ 1`. -/
noncomputable def fordSquarefreeShellStart (Y v : ℕ) : ℕ :=
  8 * v * ⌈(Y : ℝ) ^ (2 / 3 : ℝ)⌉₊

private theorem eventually_log_sq_le_rpow_mul (c a : ℝ)
    (hc : 0 < c) (ha : 0 < a) :
    ∀ᶠ Y : ℕ in atTop,
      Real.log (Y : ℝ) ^ 2 ≤ c * (Y : ℝ) ^ a := by
  have h := (isLittleO_log_rpow_rpow_atTop (2 : ℝ) ha).natCast_atTop
  have hb := h.bound hc
  filter_upwards [hb, eventually_gt_atTop (0 : ℕ)] with Y hY hYpos
  have hlog : 0 ≤ Real.log (Y : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hYpos)
  have hpow : 0 ≤ (Y : ℝ) ^ a :=
    Real.rpow_nonneg (Nat.cast_nonneg Y) a
  simpa [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hlog 2),
    abs_of_nonneg hpow] using hY

private theorem endpoint_one_of_shell_lower
    (c S : ℝ) (v M : ℕ) (hv : 1 ≤ v) (hc : 2 ≤ c * S)
    (hc0 : 0 ≤ c) (hM : (8 : ℝ) * (v : ℝ) * S ≤ (M : ℝ)) :
    ((2 * v + 1 : ℕ) : ℝ) ≤ c * (M : ℝ) := by
  have hvR : (1 : ℝ) ≤ (v : ℝ) := by exact_mod_cast hv
  have h8v0 : 0 ≤ (8 : ℝ) * (v : ℝ) := by positivity
  calc
    ((2 * v + 1 : ℕ) : ℝ) ≤ 3 * (v : ℝ) := by
      push_cast
      linarith
    _ ≤ 16 * (v : ℝ) := by nlinarith
    _ = 2 * ((8 : ℝ) * (v : ℝ)) := by ring
    _ ≤ (c * S) * ((8 : ℝ) * (v : ℝ)) :=
      mul_le_mul_of_nonneg_right hc h8v0
    _ = c * ((8 : ℝ) * (v : ℝ) * S) := by ring
    _ ≤ c * (M : ℝ) := mul_le_mul_of_nonneg_left hM hc0

private theorem shell_cast_upper
    {v C : ℕ} {y S : ℝ}
    (hv : (v : ℝ) ≤ y) (hC : (C : ℝ) ≤ 2 * S) :
    ((8 * v * C : ℕ) : ℝ) ≤ 16 * y * S := by
  have hy0 : 0 ≤ y := (Nat.cast_nonneg v).trans hv
  push_cast
  calc
    8 * (v : ℝ) * (C : ℝ) ≤ 8 * y * (2 * S) := by gcongr
    _ = 16 * y * S := by ring

private theorem natCast_le_natCast {a b : ℕ} (h : a ≤ b) :
    (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast h

private theorem rpow_fifteen_eighth_mul_one_eighth {y : ℝ} (hy : 0 < y) :
    y ^ (15 / 8 : ℝ) * y ^ (1 / 8 : ℝ) = y ^ 2 := by
  rw [← Real.rpow_add hy]
  norm_num

private theorem rpow_one_mul_two_thirds_mul_one_twelfth {y : ℝ} (hy : 0 < y) :
    y * y ^ (2 / 3 : ℝ) * y ^ (1 / 12 : ℝ) = y ^ (7 / 4 : ℝ) := by
  have hone : y ^ (1 : ℝ) = y := Real.rpow_one y
  nth_rewrite 1 [← hone]
  rw [← Real.rpow_add hy, ← Real.rpow_add hy]
  norm_num

private theorem coefficient_gap
    {K L p d : ℝ} (hL : 0 < L) (hd : 0 < d)
    (h : L ≤ (K * Real.log 2 / d) * p) :
    d ≤ K * (Real.log 2 / L) * p := by
  rw [show K * (Real.log 2 / L) * p = (K * Real.log 2 * p) / L by
    field_simp]
  apply (le_div_iff₀ hL).2
  have hd0 : 0 ≤ d := hd.le
  have := mul_le_mul_of_nonneg_left h hd0
  calc
    d * L ≤ d * ((K * Real.log 2 / d) * p) := this
    _ = K * Real.log 2 * p := by field_simp

private theorem endpoint_two_of_gap
    {c p y S T : ℝ} {M N : ℕ}
    (hc : 0 ≤ c) (hyS : 0 ≤ y * S)
    (hM : (M : ℝ) ≤ 16 * y * S) (hgap : 32 ≤ c * p)
    (hidentity : y * S * p = T) (hTN : T ≤ (N : ℝ)) :
    2 * (M : ℝ) ≤ c * (N : ℝ) := by
  calc
    2 * (M : ℝ) ≤ 2 * (16 * y * S) :=
      mul_le_mul_of_nonneg_left hM (by norm_num)
    _ = 32 * (y * S) := by ring
    _ ≤ (c * p) * (y * S) := mul_le_mul_of_nonneg_right hgap hyS
    _ = c * T := by rw [← hidentity]; ring
    _ ≤ c * (N : ℝ) := mul_le_mul_of_nonneg_left hTN hc

private theorem endpoint_three_of_scale
    {c S : ℝ} {v N : ℕ}
    (hS : 0 < S) (hv : 0 < v) (hSv : S ≤ (v : ℝ))
    (hvN : (v : ℝ) ≤ (N : ℝ)) (hc : 2 ≤ c * S) :
    (((N / (2 * v + 1) : ℕ) + 1 : ℕ) : ℝ) ≤ c * (N : ℝ) := by
  have hvreal : (0 : ℝ) < (v : ℝ) := by exact_mod_cast hv
  have hden : (v : ℝ) ≤ ((2 * v + 1 : ℕ) : ℝ) := by
    push_cast
    linarith
  have hcastdiv : ((N / (2 * v + 1) : ℕ) : ℝ) ≤
      (N : ℝ) / ((2 * v + 1 : ℕ) : ℝ) := Nat.cast_div_le
  have hdivmono : (N : ℝ) / ((2 * v + 1 : ℕ) : ℝ) ≤
      (N : ℝ) / (v : ℝ) :=
    div_le_div_of_nonneg_left (Nat.cast_nonneg N) hvreal hden
  have hone : (1 : ℝ) ≤ (N : ℝ) / (v : ℝ) :=
    (le_div_iff₀ hvreal).2 (by simpa using hvN)
  have hquotient : (((N / (2 * v + 1) : ℕ) + 1 : ℕ) : ℝ) ≤
      2 * (N : ℝ) / (v : ℝ) := by
    rw [Nat.cast_add, Nat.cast_one]
    calc
      ((N / (2 * v + 1) : ℕ) : ℝ) + 1 ≤
          (N : ℝ) / (v : ℝ) + 1 := by
        linarith [hcastdiv.trans hdivmono]
      _ ≤ (N : ℝ) / (v : ℝ) + (N : ℝ) / (v : ℝ) :=
        by linarith
      _ = 2 * (N : ℝ) / (v : ℝ) := by ring
  have htwoDiv : 2 * (N : ℝ) / (v : ℝ) ≤
      2 * (N : ℝ) / S :=
    div_le_div_of_nonneg_left (by positivity) hS hSv
  have hdivCoef : 2 * (N : ℝ) / S ≤ c * (N : ℝ) := by
    apply (div_le_iff₀ hS).2
    have hN0 : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
    nlinarith [mul_le_mul_of_nonneg_right hc hN0]
  exact hquotient.trans (htwoDiv.trans hdivCoef)

private theorem rpow_seven_fourths_le_div_add_one
    {Y X q : ℕ} (hY : 0 < Y) (hq : 0 < q) (hYX : Y * Y ≤ X)
    (hqR : (q : ℝ) ≤ (Y : ℝ) ^ (1 / 8 : ℝ))
    (hRtwo : 2 ≤ (Y : ℝ) ^ (1 / 8 : ℝ)) :
    (Y : ℝ) ^ (7 / 4 : ℝ) ≤ ((X / q + 1 : ℕ) : ℝ) := by
  let y : ℝ := (Y : ℝ)
  let R : ℝ := y ^ (1 / 8 : ℝ)
  let T : ℝ := y ^ (7 / 4 : ℝ)
  let D : ℕ := ⌈T⌉₊
  have hypos : 0 < y := by
    change (0 : ℝ) < (Y : ℝ)
    exact_mod_cast hY
  have hTone : 1 ≤ T :=
    Real.one_le_rpow (by exact_mod_cast hY : (1 : ℝ) ≤ (Y : ℝ)) (by norm_num)
  have hTD : T ≤ (D : ℝ) := by
    change T ≤ (Nat.ceil T : ℝ)
    exact Nat.le_ceil T
  have hDtwo : (D : ℝ) ≤ 2 * T := by
    have h := (Nat.ceil_lt_add_one (zero_le_one.trans hTone)).le
    change (D : ℝ) ≤ T + 1 at h
    linarith
  have hRT : R * T = y ^ (15 / 8 : ℝ) := by
    dsimp [R, T]
    rw [← Real.rpow_add hypos]
    norm_num
  have hRTfull : y ^ (15 / 8 : ℝ) * R = y ^ 2 := by
    dsimp [R]
    exact rpow_fifteen_eighth_mul_one_eighth hypos
  have hqR' : (q : ℝ) ≤ R := by simpa [R, y] using hqR
  have hRtwo' : 2 ≤ R := by simpa [R, y] using hRtwo
  have hqDX : q * D ≤ X := by
    have hRT0 : 0 ≤ R * T := by positivity
    have hqDy : (q : ℝ) * (D : ℝ) ≤ y ^ 2 := by
      calc
        (q : ℝ) * (D : ℝ) ≤ R * (2 * T) := by gcongr
        _ = 2 * (R * T) := by ring
        _ ≤ R * (R * T) := mul_le_mul_of_nonneg_right hRtwo' hRT0
        _ = (R * T) * R := by ring
        _ = y ^ 2 := by rw [hRT, hRTfull]
    have hqDYY : q * D ≤ Y * Y := by
      exact_mod_cast (show (q : ℝ) * (D : ℝ) ≤
        (Y : ℝ) * (Y : ℝ) by simpa [y, pow_two] using hqDy)
    exact hqDYY.trans hYX
  have hDdiv : D ≤ X / q :=
    (Nat.le_div_iff_mul_le hq).2 (by simpa [Nat.mul_comm] using hqDX)
  calc
    (Y : ℝ) ^ (7 / 4 : ℝ) = T := rfl
    _ ≤ (D : ℝ) := hTD
    _ ≤ ((X / q : ℕ) : ℝ) := natCast_le_natCast hDdiv
    _ ≤ ((X / q + 1 : ℕ) : ℝ) :=
      natCast_le_natCast (by omega)

/-- All numerical side conditions needed to apply the squarefree prefix
estimate, simultaneously for every powerful part and all its divisors. -/
theorem exists_fordPowerfulCutoff_numerics (K : ℝ) (hK : 0 < K) :
    ∃ Y₀ : ℕ, ∀ Y ≥ Y₀, ∀ X, Y * Y ≤ X →
      let Q := fordPowerfulCutoff Y
      1 ≤ Q ∧ Q ≤ Y ∧
      (Q : ℝ) ^ (-(7 / 16 : ℝ)) *
          Erdos469.powerfulNineSixteenthsMass ≤
        Real.log 2 / Real.log (Y : ℝ) ^ 2 ∧
      ∀ q ∈ Finset.Icc 1 Q, ∀ f ∈ q.divisors,
        let v := Y / f
        let N := X / q + 1
        let M := fordSquarefreeShellStart Y v
        1 ≤ v ∧ v ≤ Y ∧
        (Y : ℝ) ^ (2 / 3 : ℝ) ≤ (v : ℝ) ∧
        4 * v ≤ M ∧
        (Y : ℝ) ^ (2 / 3 : ℝ) ≤ (M / (4 * v) : ℕ) ∧
        ((2 * v + 1 : ℕ) : ℝ) ≤
          K * (Real.log 2 / Real.log (Y : ℝ) ^ 2) * (M : ℝ) ∧
        2 * (M : ℝ) ≤
          K * (Real.log 2 / Real.log (Y : ℝ) ^ 2) * (N : ℝ) ∧
        (((N / (2 * v + 1) : ℕ) + 1 : ℕ) : ℝ) ≤
          K * (Real.log 2 / Real.log (Y : ℝ) ^ 2) * (N : ℝ) := by
  let A : ℝ := Erdos469.powerfulNineSixteenthsMass + 1
  have hA : 0 < A := by
    dsimp [A]
    linarith [Erdos469.powerfulNineSixteenthsMass_nonneg]
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hcTail : 0 < Real.log 2 / A := div_pos hlog2 hA
  have hcShell : 0 < K * Real.log 2 / 2 := by positivity
  have hcPrefix : 0 < K * Real.log 2 / 32 := by positivity
  have hpowTendsto :
      Tendsto (fun Y : ℕ ↦ (Y : ℝ) ^ (1 / 24 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  have heventually : ∀ᶠ Y : ℕ in atTop,
      2 ≤ Y ∧
      2 ≤ (Y : ℝ) ^ (1 / 24 : ℝ) ∧
      Real.log (Y : ℝ) ^ 2 ≤
        (Real.log 2 / A) * (Y : ℝ) ^ (7 / 384 : ℝ) ∧
      Real.log (Y : ℝ) ^ 2 ≤
        (K * Real.log 2 / 2) * (Y : ℝ) ^ (2 / 3 : ℝ) ∧
      Real.log (Y : ℝ) ^ 2 ≤
        (K * Real.log 2 / 32) * (Y : ℝ) ^ (1 / 12 : ℝ) := by
    filter_upwards
      [eventually_ge_atTop (2 : ℕ), hpowTendsto.eventually_ge_atTop 2,
        eventually_log_sq_le_rpow_mul (Real.log 2 / A) (7 / 384) hcTail (by norm_num),
        eventually_log_sq_le_rpow_mul (K * Real.log 2 / 2) (2 / 3) hcShell
          (by norm_num),
        eventually_log_sq_le_rpow_mul (K * Real.log 2 / 32) (1 / 12) hcPrefix
          (by norm_num)] with Y hY hroot htail hshell hprefix
    exact ⟨hY, hroot, htail, hshell, hprefix⟩
  rw [eventually_atTop] at heventually
  obtain ⟨Y₀, hY₀⟩ := heventually
  refine ⟨Y₀, fun Y hYY₀ X hYX ↦ ?_⟩
  have hYdata := hY₀ Y hYY₀
  rcases hYdata with ⟨hY, hroot, htail, hshell, hprefix⟩
  let y : ℝ := (Y : ℝ)
  let U : ℝ := y ^ (1 / 24 : ℝ)
  let R : ℝ := y ^ (1 / 8 : ℝ)
  let S : ℝ := y ^ (2 / 3 : ℝ)
  let T : ℝ := y ^ (7 / 4 : ℝ)
  let L : ℝ := Real.log y ^ 2
  let Q : ℕ := fordPowerfulCutoff Y
  have hypos : 0 < y := by
    simpa [y] using (show (0 : ℝ) < (Y : ℝ) by positivity)
  have hyone : 1 ≤ y := by
    have hYone : 1 ≤ Y := by omega
    simpa [y] using (show (1 : ℝ) ≤ (Y : ℝ) by exact_mod_cast hYone)
  have hU : 2 ≤ U := by simpa [U, y] using hroot
  have hUpos : 0 < U := lt_of_lt_of_le (by norm_num) hU
  have hSpos : 0 < S := Real.rpow_pos_of_pos hypos _
  have hSone : 1 ≤ S := Real.one_le_rpow hyone (by norm_num)
  have hRpos : 0 < R := Real.rpow_pos_of_pos hypos _
  have hTone : 1 ≤ T := Real.one_le_rpow hyone (by norm_num)
  have hLpos : 0 < L := by
    dsimp [L, y]
    exact sq_pos_of_pos (Real.log_pos (by exact_mod_cast (show 1 < Y by omega)))
  have hQlowerReal : U ≤ (Q : ℝ) := by
    have hUR : 2 * U ≤ R := by
      have hmono : U ≤ y ^ (1 / 12 : ℝ) := by
        dsimp [U]
        exact Real.rpow_le_rpow_of_exponent_le hyone (by norm_num)
      have hmul : U * U ≤ U * y ^ (1 / 12 : ℝ) :=
        mul_le_mul_of_nonneg_left hmono hUpos.le
      have hid : U * y ^ (1 / 12 : ℝ) = R := by
        dsimp [U, R]
        rw [← Real.rpow_add hypos]
        norm_num
      calc
        2 * U ≤ U * U := by nlinarith
        _ ≤ U * y ^ (1 / 12 : ℝ) := hmul
        _ = R := hid
    have hfloor : R < (Q : ℝ) + 1 := by
      simpa [Q, fordPowerfulCutoff, R, y] using
        (Nat.lt_floor_add_one R)
    linarith
  have hQone : 1 ≤ Q := by
    have : 2 ≤ Q := by exact_mod_cast (hU.trans hQlowerReal)
    omega
  have hQR : (Q : ℝ) ≤ R := by
    simpa [Q, fordPowerfulCutoff, R, y] using Nat.floor_le hRpos.le
  have hRY : R ≤ y := by
    dsimp [R]
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hyone (by norm_num : (1 / 8 : ℝ) ≤ 1)
  have hQY : Q ≤ Y := by
    have : (Q : ℝ) ≤ (Y : ℝ) := by simpa [y] using hQR.trans hRY
    exact_mod_cast this
  refine ⟨hQone, hQY, ?_, ?_⟩
  · have hneg : (-(7 / 16 : ℝ)) ≤ 0 := by norm_num
    have hpowerMono :
        (Q : ℝ) ^ (-(7 / 16 : ℝ)) ≤
          U ^ (-(7 / 16 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hUpos hQlowerReal hneg
    have hUpower :
        U ^ (-(7 / 16 : ℝ)) = y ^ (-(7 / 384 : ℝ)) := by
      dsimp [U]
      rw [← Real.rpow_mul hypos.le]
      norm_num
    have htail' :
        L ≤ (Real.log 2 / A) * y ^ (7 / 384 : ℝ) := by
      simpa [L, y] using htail
    have hmassA : Erdos469.powerfulNineSixteenthsMass ≤ A := by
      dsimp [A]
      linarith
    have hmass0 : 0 ≤ Erdos469.powerfulNineSixteenthsMass :=
      Erdos469.powerfulNineSixteenthsMass_nonneg
    apply (le_div_iff₀ hLpos).2
    calc
      (Q : ℝ) ^ (-(7 / 16 : ℝ)) *
            Erdos469.powerfulNineSixteenthsMass * L ≤
          U ^ (-(7 / 16 : ℝ)) *
            Erdos469.powerfulNineSixteenthsMass * L := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hpowerMono hmass0) hLpos.le
      _ ≤ U ^ (-(7 / 16 : ℝ)) * A * L := by
        gcongr
      _ ≤ U ^ (-(7 / 16 : ℝ)) * A *
          ((Real.log 2 / A) * y ^ (7 / 384 : ℝ)) := by
        gcongr
      _ = Real.log 2 := by
        rw [hUpower]
        have hcancel :
            y ^ (-(7 / 384 : ℝ)) * y ^ (7 / 384 : ℝ) = 1 := by
          rw [← Real.rpow_add hypos]
          norm_num
        field_simp
        nlinarith
  · intro q hq f hf
    have hqIcc := Finset.mem_Icc.mp hq
    have hqpos : 0 < q := by omega
    have hqQ : q ≤ Q := hqIcc.2
    have hqR : (q : ℝ) ≤ R :=
      (by exact_mod_cast hqQ : (q : ℝ) ≤ (Q : ℝ)).trans hQR
    have hfdvd : f ∣ q := (Nat.mem_divisors.mp hf).1
    have hfpos : 0 < f := Nat.pos_of_dvd_of_pos hfdvd hqpos
    have hfq : f ≤ q := Nat.le_of_dvd hqpos hfdvd
    have hfR : (f : ℝ) ≤ R :=
      (by exact_mod_cast hfq : (f : ℝ) ≤ (q : ℝ)).trans hqR
    let C : ℕ := ⌈S⌉₊
    let v : ℕ := Y / f
    let N : ℕ := X / q + 1
    let M : ℕ := 8 * v * C
    have hSC : S ≤ (C : ℝ) := by
      simpa [C] using Nat.le_ceil S
    have hCupper : (C : ℝ) ≤ S + 1 := by
      exact (Nat.ceil_lt_add_one hSpos.le).le
    have hCtwo : (C : ℝ) ≤ 2 * S := by linarith
    have hCpos : 0 < C := by
      have : (0 : ℝ) < C := hSpos.trans_le hSC
      exact_mod_cast this
    have hremaining : 2 ≤ y ^ (5 / 24 : ℝ) := by
      exact hU.trans (Real.rpow_le_rpow_of_exponent_le hyone (by norm_num))
    have hSR : S * R = y ^ (19 / 24 : ℝ) := by
      dsimp [S, R]
      rw [← Real.rpow_add hypos]
      norm_num
    have hfull : y ^ (19 / 24 : ℝ) * y ^ (5 / 24 : ℝ) = y := by
      rw [← Real.rpow_add hypos]
      norm_num
    have htwoSR : 2 * S * R ≤ y := by
      calc
        2 * S * R = 2 * (S * R) := by ring
        _ = 2 * y ^ (19 / 24 : ℝ) := by rw [hSR]
        _ ≤ y ^ (5 / 24 : ℝ) * y ^ (19 / 24 : ℝ) := by
          gcongr
        _ = y := by rw [mul_comm, hfull]
    have hCfy : (C : ℝ) * (f : ℝ) ≤ y := by
      calc
        (C : ℝ) * (f : ℝ) ≤ (2 * S) * R := by gcongr
        _ = 2 * S * R := by ring
        _ ≤ y := htwoSR
    have hCfY : C * f ≤ Y := by
      have : (C : ℝ) * (f : ℝ) ≤ (Y : ℝ) := by
        simpa [y] using hCfy
      exact_mod_cast this
    have hCv : C ≤ v := by
      exact (Nat.le_div_iff_mul_le hfpos).2 hCfY
    have hvpos : 0 < v := lt_of_lt_of_le hCpos hCv
    have hvone : 1 ≤ v := hvpos
    have hvY : v ≤ Y := Nat.div_le_self Y f
    have hSv : S ≤ (v : ℝ) :=
      hSC.trans (by exact_mod_cast hCv)
    have hMfour : 4 * v ≤ M := by
      dsimp [M]
      nlinarith
    have hMdiv : M / (4 * v) = 2 * C := by
      dsimp [M]
      rw [show 8 * v * C = (4 * v) * (2 * C) by ring]
      rw [Nat.mul_comm]
      exact Nat.mul_div_left (2 * C) (by omega : 0 < 4 * v)
    have hSdiv : S ≤ (M / (4 * v) : ℕ) := by
      rw [hMdiv]
      exact hSC.trans (by exact_mod_cast (show C ≤ 2 * C by omega))
    have hshell' : L ≤ (K * Real.log 2 / 2) * S := by
      simpa [L, S, y] using hshell
    have hcoefpos : 0 < K * (Real.log 2 / L) := by positivity
    have hcoefS : 2 ≤ K * (Real.log 2 / L) * S := by
      rw [show K * (Real.log 2 / L) * S =
          (K * Real.log 2 * S) / L by field_simp]
      apply (le_div_iff₀ hLpos).2
      nlinarith
    have hMlower : (8 : ℝ) * (v : ℝ) * S ≤ (M : ℝ) := by
      dsimp [M]
      push_cast
      gcongr
    have hendpointOne : ((2 * v + 1 : ℕ) : ℝ) ≤
        K * (Real.log 2 / L) * (M : ℝ) :=
      endpoint_one_of_shell_lower (K * (Real.log 2 / L)) S v M hvone
        hcoefS hcoefpos.le hMlower
    have hMupper : (M : ℝ) ≤ 16 * y * S := by
      have hvYreal : (v : ℝ) ≤ y := by
        change (v : ℝ) ≤ (Y : ℝ)
        exact_mod_cast hvY
      exact shell_cast_upper hvYreal hCtwo
    have hRtwo : 2 ≤ R := hU.trans
      (Real.rpow_le_rpow_of_exponent_le hyone (by norm_num))
    have hTN : T ≤ (N : ℝ) := by
      have hbound := rpow_seven_fourths_le_div_add_one
        (Y := Y) (X := X) (q := q) (by omega : 0 < Y) hqpos hYX
        (by simpa [R, y] using hqR) (by simpa [R, y] using hRtwo)
      simpa [T, y, N] using hbound
    have hyT : y ≤ T := by
      dsimp [T]
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le hyone (by norm_num : (1 : ℝ) ≤ 7 / 4)
    have hvN : (v : ℝ) ≤ (N : ℝ) := by
      have hvy : (v : ℝ) ≤ y := by
        change (v : ℝ) ≤ (Y : ℝ)
        exact natCast_le_natCast hvY
      exact hvy.trans (hyT.trans hTN)
    have hprefix' : L ≤
        (K * Real.log 2 / 32) * y ^ (1 / 12 : ℝ) := by
      simpa [L, y] using hprefix
    have hcoefGap : 32 ≤
        K * (Real.log 2 / L) * y ^ (1 / 12 : ℝ) :=
      coefficient_gap hLpos (by norm_num) hprefix'
    have hyST : y * S * y ^ (1 / 12 : ℝ) = T := by
      dsimp [S, T]
      exact rpow_one_mul_two_thirds_mul_one_twelfth hypos
    have hendpointTwo : 2 * (M : ℝ) ≤
        K * (Real.log 2 / L) * (N : ℝ) :=
      endpoint_two_of_gap hcoefpos.le (mul_nonneg hypos.le hSpos.le)
        hMupper hcoefGap hyST hTN
    have hendpointThree :
        (((N / (2 * v + 1) : ℕ) + 1 : ℕ) : ℝ) ≤
          K * (Real.log 2 / L) * (N : ℝ) :=
      endpoint_three_of_scale hSpos hvpos hSv hvN hcoefS
    simpa only [v, N, M, C, Q, L, S, y, fordSquarefreeShellStart] using
      ⟨hvone, hvY, hSv, hMfour, hSdiv, hendpointOne,
        hendpointTwo, hendpointThree⟩

end

end Erdos446
