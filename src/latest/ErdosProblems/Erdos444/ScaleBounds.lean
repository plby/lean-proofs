/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import ErdosProblems.Erdos444.Analytic
import ErdosProblems.Erdos444.Growth

/-!
# Base-four scale bounds for Erdős Problem 444

This file packages the elementary eventual comparisons for the finite
large-value argument.  At cutoff `X`, its principal parameter is
`m = Nat.log 4 X`; the moment order and prime cutoff are both `m²`.
-/

open Filter

namespace Erdos444

/-- The elementary inequality `m² ≤ 4^m`. -/
theorem sq_le_four_pow (m : ℕ) : m ^ 2 ≤ 4 ^ m := by
  induction m with
  | zero => norm_num
  | succ m ih =>
      cases m with
      | zero => norm_num
      | succ n =>
          have hstep : (n + 2) ^ 2 ≤ 4 * (n + 1) ^ 2 := by
            have hlin : n + 2 ≤ 2 * (n + 1) := by omega
            calc
              (n + 2) ^ 2 ≤ (2 * (n + 1)) ^ 2 := by gcongr
              _ = 4 * (n + 1) ^ 2 := by ring
          calc
            (n + 2) ^ 2 ≤ 4 * (n + 1) ^ 2 := hstep
            _ ≤ 4 * 4 ^ (n + 1) := Nat.mul_le_mul_left 4 ih
            _ = 4 ^ (n + 2) := by ring

/-- The base-four logarithmic parameter is eventually at least five. -/
theorem eventually_five_le_baseFourLog :
    ∀ᶠ X : ℕ in atTop, 5 ≤ Nat.log 4 X := by
  filter_upwards [eventually_ge_atTop (4 ^ 5)] with X hX
  have hmono := Nat.log_mono_right (b := 4) hX
  have heq : Nat.log 4 (4 ^ 5) = 5 := Nat.log_pow (by norm_num) 5
  rw [heq] at hmono
  exact hmono

/-- In fact the square of the logarithmic parameter never exceeds `X`
once `X` is positive. -/
theorem baseFourLog_sq_le {X : ℕ} (hX : 0 < X) :
    (Nat.log 4 X) ^ 2 ≤ X := by
  exact (sq_le_four_pow (Nat.log 4 X)).trans
    (Nat.pow_log_le_self 4 hX.ne')

theorem eventually_two_le_baseFourLog :
    ∀ᶠ X : ℕ in atTop, 2 ≤ Nat.log 4 X :=
  eventually_five_le_baseFourLog.mono fun _ h ↦ by omega

theorem eventually_baseFourLog_sq_le :
    ∀ᶠ X : ℕ in atTop, (Nat.log 4 X) ^ 2 ≤ X := by
  filter_upwards [eventually_gt_atTop 0] with X hX
  exact baseFourLog_sq_le hX

/-- The twice-iterated base-four natural logarithm tends to infinity. -/
theorem tendsto_iteratedBaseFourLog_atTop :
    Tendsto (fun X : ℕ ↦ Nat.log 4 (Nat.log 4 X)) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro J
  refine ⟨4 ^ (4 ^ J), ?_⟩
  intro X hX
  have houter := Nat.log_mono_right (b := 4) hX
  have hinner : 4 ^ J ≤ Nat.log 4 X := by
    simpa [Nat.log_pow (by norm_num : 1 < 4)] using houter
  have hsecond := Nat.log_mono_right (b := 4) hinner
  simpa [Nat.log_pow (by norm_num : 1 < 4)] using hsecond

theorem tendsto_iteratedBaseFourLog_cast_atTop :
    Tendsto (fun X : ℕ ↦ (Nat.log 4 (Nat.log 4 X) : ℝ)) atTop atTop :=
  tendsto_natCast_atTop_atTop.comp tendsto_iteratedBaseFourLog_atTop

/-- A fixed affine function of the iterated logarithm is eventually at
most the first base-four logarithm. -/
theorem eventually_const_mul_iteratedBaseFourLog_add_le_baseFourLog
    (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D) :
    ∀ᶠ X : ℕ in atTop,
      C * ((Nat.log 4 (Nat.log 4 X) : ℝ) + 1) + D ≤
        (Nat.log 4 X : ℝ) := by
  let K : ℝ := 2 * C + D
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hpolyReal := eventually_const_mul_pow_lt_exp K 1
  have hpoly := tendsto_iteratedBaseFourLog_cast_atTop.eventually hpolyReal
  have hjone := tendsto_iteratedBaseFourLog_atTop.eventually
    (eventually_ge_atTop 1)
  filter_upwards [hpoly, hjone] with X hpolyX hj
  let m := Nat.log 4 X
  let j := Nat.log 4 m
  change 1 ≤ j at hj
  have hm0 : m ≠ 0 := by
    intro hm
    have : j = 0 := by simp [j, hm]
    omega
  have hjR : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have htargetK : C * ((j : ℝ) + 1) + D ≤ K * (j : ℝ) := by
    dsimp [K]
    nlinarith [mul_nonneg hC (sub_nonneg.mpr hjR),
      mul_nonneg hD (sub_nonneg.mpr hjR)]
  have hexp4 : Real.exp (j : ℝ) ≤ (4 : ℝ) ^ j := by
    rw [show Real.exp (j : ℝ) = (Real.exp 1) ^ j by
      simpa only [mul_one] using Real.exp_nat_mul 1 j]
    exact pow_le_pow_left₀ (Real.exp_pos 1).le
      (Real.exp_one_lt_three.le.trans (by norm_num)) j
  have hpowm : (4 : ℝ) ^ j ≤ (m : ℝ) := by
    exact_mod_cast Nat.pow_log_le_self 4 hm0
  change K * (j : ℝ) ^ 1 < Real.exp (j : ℝ) at hpolyX
  simp only [pow_one] at hpolyX
  change C * ((j : ℝ) + 1) + D ≤ (m : ℝ)
  exact htargetK.trans (hpolyX.le.trans (hexp4.trans hpowm))

/-- The reciprocal mass of the moving prime window `(m²,X]` is eventually
at most `m`. -/
theorem eventually_primeWindowMass_baseFourLog_sq_le :
    ∀ᶠ X : ℕ in atTop,
      Erdos697.PrimeWindow.reciprocalMass ((Nat.log 4 X) ^ 2) X ≤
        (Nat.log 4 X : ℝ) := by
  let C : ℝ := Real.log 4 + Real.log (Real.log 4)
  have hC : 0 ≤ C := by
    have hlog4 : 1 < Real.log (4 : ℝ) := by
      exact (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 4)).2
        (Real.exp_one_lt_three.trans (by norm_num))
    dsimp [C]
    exact add_nonneg (zero_lt_one.trans hlog4).le
      (Real.log_nonneg hlog4.le)
  have hscale :=
    eventually_const_mul_iteratedBaseFourLog_add_le_baseFourLog C
      Erdos444.PrimeBounds.mertensConstant hC
      Erdos444.PrimeBounds.mertensConstant_nonneg
  filter_upwards [eventually_ge_atTop 9, eventually_baseFourLog_sq_le,
      hscale] with X hX9 hmX hscaleX
  let m := Nat.log 4 X
  have hX2 : 2 ≤ X := by omega
  have hMertens := Erdos444.PrimeBounds.primeWindowMass_le_log_log_add
    hX2 hmX
  have hloglog := log_log_le_baseFourIterate X hX9
  change Erdos697.PrimeWindow.reciprocalMass (m ^ 2) X ≤ (m : ℝ)
  dsimp [C] at hscaleX
  have hsum : Real.log (Real.log (X : ℝ)) +
      Erdos444.PrimeBounds.mertensConstant ≤
        (Real.log 4 + Real.log (Real.log 4)) *
            ((Nat.log 4 (Nat.log 4 X) + 1 : ℕ) : ℝ) +
          Erdos444.PrimeBounds.mertensConstant :=
    by simpa [add_comm] using
      add_le_add_right hloglog Erdos444.PrimeBounds.mertensConstant
  norm_num only [Nat.cast_add, Nat.cast_one] at hsum
  change (Real.log 4 + Real.log (Real.log 4)) *
      ((Nat.log 4 (Nat.log 4 X) : ℝ) + 1) +
        Erdos444.PrimeBounds.mertensConstant ≤ (m : ℝ) at hscaleX
  exact hMertens.trans (hsum.trans hscaleX)

/-- The reciprocal mass at the product cutoff used by the `m²`-nd moment
is eventually bounded by `m⁴`. -/
theorem eventually_reciprocalMassNat_pow_baseFourLog_sq_le_four
    (A : Set ℕ) :
    ∀ᶠ X : ℕ in atTop,
      reciprocalMassNat A
          (X ^ ((Nat.log 4 X) ^ 2) + 1) ≤
        (Nat.log 4 X : ℝ) ^ 4 := by
  filter_upwards [eventually_five_le_baseFourLog,
      eventually_gt_atTop 0] with X hm5 hX
  let m := Nat.log 4 X
  let N := X ^ (m ^ 2)
  have hmR : (5 : ℝ) ≤ m := by exact_mod_cast hm5
  have hm0 : (0 : ℝ) < m := by positivity
  have hXpos : (0 : ℝ) < X := by exact_mod_cast hX
  have hNposNat : 0 < N := by dsimp [N]; positivity
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hNposNat
  have hXpowNat : X ≤ 4 ^ (m + 1) :=
    (Nat.lt_pow_succ_log_self (by norm_num : 1 < 4) X).le
  have hXpow : (X : ℝ) ≤ (4 : ℝ) ^ (m + 1) := by
    exact_mod_cast hXpowNat
  have hlogX : Real.log (X : ℝ) ≤ 4 * (m : ℝ) := by
    have hfirst : Real.log (X : ℝ) ≤
        ((m + 1 : ℕ) : ℝ) * Real.log 4 := by
      calc
        Real.log (X : ℝ) ≤ Real.log ((4 : ℝ) ^ (m + 1)) :=
          Real.log_le_log hXpos hXpow
        _ = ((m + 1 : ℕ) : ℝ) * Real.log 4 := by rw [Real.log_pow]
    have hlog4 : Real.log (4 : ℝ) < 2 := by
      rw [show (4 : ℝ) = 2 * 2 by norm_num,
        Real.log_mul (by norm_num) (by norm_num)]
      linarith [Real.log_two_lt_d9]
    norm_num only [Nat.cast_add, Nat.cast_one] at hfirst
    nlinarith
  have hYle : ((N + 1 : ℕ) : ℝ) ≤ 2 * (N : ℝ) := by
    norm_num only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
    have hNone : (1 : ℝ) ≤ N := by exact_mod_cast hNposNat
    linarith
  have hlogY : Real.log ((N + 1 : ℕ) : ℝ) ≤
      Real.log 2 + ((m : ℝ) ^ 2) * Real.log (X : ℝ) := by
    calc
      Real.log ((N + 1 : ℕ) : ℝ) ≤ Real.log (2 * (N : ℝ)) :=
        Real.log_le_log (by positivity) hYle
      _ = Real.log 2 + Real.log (N : ℝ) := by
        rw [Real.log_mul (by norm_num) hNpos.ne']
      _ = Real.log 2 + ((m : ℝ) ^ 2) * Real.log (X : ℝ) := by
        dsimp [N]
        norm_num only [Nat.cast_pow]
        rw [Real.log_pow]
        norm_num [Nat.cast_pow]
  have hlogYcoarse : 1 + Real.log ((N + 1 : ℕ) : ℝ) ≤
      2 + 4 * (m : ℝ) ^ 3 := by
    have hlog2 : Real.log (2 : ℝ) < 1 := Real.log_two_lt_d9.trans (by norm_num)
    have hmul := mul_le_mul_of_nonneg_left hlogX (sq_nonneg (m : ℝ))
    calc
      1 + Real.log ((N + 1 : ℕ) : ℝ) ≤
          1 + (Real.log 2 + (m : ℝ) ^ 2 * Real.log (X : ℝ)) :=
        by simpa [add_comm, add_left_comm] using add_le_add_right hlogY 1
      _ ≤ 2 + 4 * (m : ℝ) ^ 3 := by
        nlinarith
  have hpoly : 2 + 4 * (m : ℝ) ^ 3 ≤ (m : ℝ) ^ 4 := by
    have hm3 : (2 : ℝ) ≤ (m : ℝ) ^ 3 := by
      nlinarith [pow_pos hm0 3]
    have hfour : (5 : ℝ) * (m : ℝ) ^ 3 ≤
        (m : ℝ) * (m : ℝ) ^ 3 :=
      mul_le_mul_of_nonneg_right hmR (pow_nonneg hm0.le 3)
    calc
      2 + 4 * (m : ℝ) ^ 3 ≤ 5 * (m : ℝ) ^ 3 := by linarith
      _ ≤ (m : ℝ) * (m : ℝ) ^ 3 := hfour
      _ = (m : ℝ) ^ 4 := by ring
  change reciprocalMassNat A (N + 1) ≤ (m : ℝ) ^ 4
  exact (reciprocalMassNat_le_one_add_log A (N + 1)).trans
    (hlogYcoarse.trans hpoly)

end Erdos444
