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

import Mathlib
import ErdosProblems.Erdos285.RoughCounts
import ErdosProblems.Erdos444.PrimeBounds

/-!
# Erdős Problem 444: factorial and large-deviation inequalities

This file packages the analytic inequalities which turn a finite
elementary-symmetric bound of the form `μ ^ r / r!` into exponential decay.
They are independent of the number-theoretic definitions and can therefore
be used both for prescribed prime sets and for later support estimates.
-/

namespace Erdos444

open Filter
open scoped BigOperators

/-- A fixed polynomial is eventually strictly smaller than the real
exponential.  This is the final generic domination step when a retained
mass has an exponential lower bound in its logarithmic scale. -/
theorem eventually_const_mul_pow_lt_exp (C : ℝ) (d : ℕ) :
    ∀ᶠ u : ℝ in atTop, C * u ^ d < Real.exp u := by
  have hratio := (Real.tendsto_exp_div_pow_atTop d).eventually_gt_atTop C
  filter_upwards [hratio, eventually_gt_atTop (0 : ℝ)] with u hu hu0
  exact (lt_div_iff₀ (pow_pos hu0 d)).mp hu

/-- A high-growth lower bound by `exp u` therefore dominates every fixed
multiple of every fixed power of `u`. -/
theorem eventually_const_mul_pow_lt_of_exp_le (C : ℝ) (d : ℕ) :
    ∀ᶠ u : ℝ in atTop, ∀ F : ℝ, Real.exp u ≤ F → C * u ^ d < F := by
  filter_upwards [eventually_const_mul_pow_lt_exp C d] with u hu F hF
  exact hu.trans_le hF

/-! ## A uniform prime-power Mertens bound -/

/-- The asymptotic prime-power Mertens formula, enlarged over its finite
initial segment, gives one global constant on the useful range `X ≥ 9`.

Keeping the constant existential is substantially more convenient than
extracting a numerical value: later arguments only use that it is fixed and
nonnegative. -/
theorem exists_primePowerReciprocalUpTo_le_log_log_add :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 9 ≤ X →
      Erdos285.RoughCounts.primePowerReciprocalUpTo X ≤
        Real.log (Real.log (X : ℝ)) + C := by
  obtain ⟨b, hb⟩ :=
    Erdos285.RoughCounts.exists_primePowerReciprocalUpTo_error_tendsto_zero
  have hevent : ∀ᶠ X : ℕ in atTop,
      Erdos285.RoughCounts.primePowerReciprocalUpTo X -
          (Real.log (Real.log (X : ℝ)) + b) < 1 :=
    hb.eventually_lt_const (by norm_num)
  rw [eventually_atTop] at hevent
  obtain ⟨N, hN⟩ := hevent
  let initialError : ℕ → ℝ := fun X ↦
    max 0 (Erdos285.RoughCounts.primePowerReciprocalUpTo X -
      Real.log (Real.log (X : ℝ)))
  let C : ℝ := max 0 (b + 1) +
    ∑ X ∈ Finset.Ico 9 N, initialError X
  refine ⟨C, ?_, ?_⟩
  · exact add_nonneg (le_max_left _ _)
      (Finset.sum_nonneg fun _ _ ↦ le_max_left _ _)
  · intro X hX9
    by_cases hNX : N ≤ X
    · have herr := hN X hNX
      have hbC : b + 1 ≤ C := by
        have hsum : 0 ≤ ∑ Y ∈ Finset.Ico 9 N, initialError Y :=
          Finset.sum_nonneg fun _ _ ↦ le_max_left _ _
        exact (le_max_right 0 (b + 1)).trans
          (le_add_of_nonneg_right hsum)
      linarith
    · have hXN : X < N := Nat.lt_of_not_ge hNX
      have hmem : X ∈ Finset.Ico 9 N := Finset.mem_Ico.mpr ⟨hX9, hXN⟩
      have hsingle : initialError X ≤
          ∑ Y ∈ Finset.Ico 9 N, initialError Y := by
        exact Finset.single_le_sum
          (fun Y _ ↦ by exact le_max_left 0 _) hmem
      have herr :
          Erdos285.RoughCounts.primePowerReciprocalUpTo X -
              Real.log (Real.log (X : ℝ)) ≤ initialError X := by
        exact le_max_right _ _
      have hfirst : 0 ≤ max 0 (b + 1) := le_max_left _ _
      dsimp [C]
      linarith

/-- A comparison between the real double logarithm and the twice-iterated
base-four natural logarithm used in the dyadic-shell argument. -/
theorem log_log_le_baseFourIterate (X : ℕ) (hX : 9 ≤ X) :
    Real.log (Real.log (X : ℝ)) ≤
      (Real.log 4 + Real.log (Real.log 4)) *
        ((Nat.log 4 (Nat.log 4 X) + 1 : ℕ) : ℝ) := by
  let m := Nat.log 4 X
  let j := Nat.log 4 m
  have hXpos : (0 : ℝ) < X := by positivity
  have hlogXpos : 0 < Real.log (X : ℝ) := by
    exact Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hlog4pos : 0 < Real.log (4 : ℝ) := Real.log_pos (by norm_num)
  have hlog4one : 1 < Real.log (4 : ℝ) := by
    apply (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 4)).2
    exact Real.exp_one_lt_three.trans (by norm_num)
  have hloglog4 : 0 ≤ Real.log (Real.log (4 : ℝ)) :=
    Real.log_nonneg hlog4one.le
  have hXpowNat : X ≤ 4 ^ (m + 1) := by
    exact (Nat.lt_pow_succ_log_self (by omega : 1 < 4) X).le
  have hXpow : (X : ℝ) ≤ (4 : ℝ) ^ (m + 1) := by
    exact_mod_cast hXpowNat
  have hlogX : Real.log (X : ℝ) ≤
      ((m + 1 : ℕ) : ℝ) * Real.log 4 := by
    calc
      Real.log (X : ℝ) ≤ Real.log ((4 : ℝ) ^ (m + 1)) :=
        Real.log_le_log hXpos hXpow
      _ = ((m + 1 : ℕ) : ℝ) * Real.log 4 := by
        rw [Real.log_pow]
  have hmpos : 0 < m := by
    dsimp [m]
    exact Nat.log_pos (by omega) (by omega)
  have hmPowNat : m + 1 ≤ 4 ^ (j + 1) := by
    apply Nat.succ_le_iff.mpr
    simpa [j] using Nat.lt_pow_succ_log_self (by omega : 1 < 4) m
  have hmPow : ((m + 1 : ℕ) : ℝ) ≤ (4 : ℝ) ^ (j + 1) := by
    exact_mod_cast hmPowNat
  have hlogm : Real.log ((m + 1 : ℕ) : ℝ) ≤
      ((j + 1 : ℕ) : ℝ) * Real.log 4 := by
    calc
      Real.log ((m + 1 : ℕ) : ℝ) ≤ Real.log ((4 : ℝ) ^ (j + 1)) :=
        Real.log_le_log (by positivity) hmPow
      _ = ((j + 1 : ℕ) : ℝ) * Real.log 4 := by
        rw [Real.log_pow]
  have hlogprod : Real.log (Real.log (X : ℝ)) ≤
      Real.log (((m + 1 : ℕ) : ℝ) * Real.log 4) :=
    Real.log_le_log hlogXpos hlogX
  have hsplit : Real.log (((m + 1 : ℕ) : ℝ) * Real.log 4) =
      Real.log ((m + 1 : ℕ) : ℝ) + Real.log (Real.log 4) := by
    rw [Real.log_mul (by positivity) hlog4pos.ne']
  have hjone : (1 : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by norm_num
  change Real.log (Real.log (X : ℝ)) ≤
    (Real.log 4 + Real.log (Real.log 4)) * (((j + 1 : ℕ) : ℝ))
  rw [hsplit] at hlogprod
  nlinarith

/-- The prime-power reciprocal mass is bounded by a fixed multiple of the
twice-iterated base-four logarithmic scale. -/
theorem exists_primePowerReciprocalUpTo_le_baseFourIterate :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ U : ℕ, ∀ X : ℕ, U ≤ X →
      Erdos285.RoughCounts.primePowerReciprocalUpTo X ≤
        C * ((Nat.log 4 (Nat.log 4 X) + 1 : ℕ) : ℝ) := by
  obtain ⟨C₀, hC₀, hC₀bound⟩ :=
    exists_primePowerReciprocalUpTo_le_log_log_add
  let C : ℝ := Real.log 4 + Real.log (Real.log 4) + C₀
  refine ⟨C, ?_, 9, ?_⟩
  · have hlog4 : 0 ≤ Real.log (4 : ℝ) := Real.log_nonneg (by norm_num)
    have hloglog4 : 0 ≤ Real.log (Real.log (4 : ℝ)) := by
      apply Real.log_nonneg
      exact (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 4)).2
        (Real.exp_one_lt_three.trans (by norm_num)) |>.le
    positivity
  · intro X hX
    let s : ℝ := ((Nat.log 4 (Nat.log 4 X) + 1 : ℕ) : ℝ)
    have hs : 1 ≤ s := by dsimp [s]; norm_num
    have hbase := hC₀bound X hX
    have hlog := log_log_le_baseFourIterate X hX
    dsimp [C, s]
    nlinarith

/-- Multiplying two quantities which are linear in `s` with a fixed
truncated exponential whose base is also linear in `s` costs at most the
`(t+1)`-st power of `s`. -/
theorem mul_truncatedExp_le_of_linear_bounds
    (E H CE CH s : ℝ) (t : ℕ)
    (_hE0 : 0 ≤ E) (hH0 : 0 ≤ H) (hCE : 0 ≤ CE) (_hCH : 0 ≤ CH)
    (hs : 1 ≤ s) (hE : E ≤ CE * s) (hH : H ≤ CH * s) :
    E * (∑ i ∈ Finset.range t, H ^ i / (i.factorial : ℝ)) ≤
      (CE * (t : ℝ) * (max 1 CH) ^ t) * s ^ (t + 1) := by
  let M : ℝ := max 1 CH
  have hM1 : 1 ≤ M := le_max_left _ _
  have hM0 : 0 ≤ M := zero_le_one.trans hM1
  have hs0 : 0 ≤ s := zero_le_one.trans hs
  have hbase1 : 1 ≤ M * s := by
    calc
      (1 : ℝ) = 1 * 1 := by ring
      _ ≤ M * s := mul_le_mul hM1 hs (by norm_num) hM0
  have hHbase : H ≤ M * s :=
    hH.trans (mul_le_mul_of_nonneg_right (le_max_right 1 CH) hs0)
  have hterm : ∀ i ∈ Finset.range t,
      H ^ i / (i.factorial : ℝ) ≤ (M * s) ^ t := by
    intro i hi
    have hit : i ≤ t := (Finset.mem_range.mp hi).le
    have hfac : (1 : ℝ) ≤ (i.factorial : ℕ) := by
      exact_mod_cast (Nat.succ_le_iff.mpr (Nat.factorial_pos i))
    exact (div_le_self (pow_nonneg hH0 i) hfac).trans
      ((pow_le_pow_left₀ hH0 hHbase i).trans
        (pow_le_pow_right₀ hbase1 hit))
  have hsum : (∑ i ∈ Finset.range t, H ^ i / (i.factorial : ℝ)) ≤
      (t : ℝ) * (M * s) ^ t := by
    calc
      (∑ i ∈ Finset.range t, H ^ i / (i.factorial : ℝ)) ≤
          ∑ _i ∈ Finset.range t, (M * s) ^ t :=
        Finset.sum_le_sum hterm
      _ = (t : ℝ) * (M * s) ^ t := by simp
  have hsum0 : 0 ≤ ∑ i ∈ Finset.range t,
      H ^ i / (i.factorial : ℝ) := by positivity
  have hupperE0 : 0 ≤ CE * s := mul_nonneg hCE hs0
  calc
    E * (∑ i ∈ Finset.range t, H ^ i / (i.factorial : ℝ)) ≤
        (CE * s) * ((t : ℝ) * (M * s) ^ t) :=
      mul_le_mul hE hsum hsum0 hupperE0
    _ = (CE * (t : ℝ) * (max 1 CH) ^ t) * s ^ (t + 1) := by
      dsimp [M]
      rw [mul_pow, pow_succ]
      ring

/-- On the base-four scales `m = log₄ X` and `j = log₄ m`, the complete
smooth-factor times fixed truncated prime-power exponential is polynomial
of degree `t+1` in `j+1`.  This is the packaged estimate used to discard
members with fewer than a fixed number of primes above `m²`. -/
theorem exists_smallPrimeEulerProduct_mul_truncatedPrimePowerExp_le_baseFourPow
    (t : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ U : ℕ, ∀ X : ℕ, U ≤ X →
      let m := Nat.log 4 X
      let j := Nat.log 4 m
      Erdos444.PrimeBounds.smallPrimeEulerProduct (m ^ 2) *
          (∑ i ∈ Finset.range t,
            Erdos285.RoughCounts.primePowerReciprocalUpTo X ^ i /
              (i.factorial : ℝ)) ≤
        C * (((j + 1 : ℕ) : ℝ) ^ (t + 1)) := by
  obtain ⟨CH, hCH, UH, hHbound⟩ :=
    exists_primePowerReciprocalUpTo_le_baseFourIterate
  let CE : ℝ := 2 * Real.exp (Erdos444.PrimeBounds.mertensConstant + 2) *
    Real.log 4
  let C : ℝ := CE * (t : ℝ) * (max 1 CH) ^ t
  refine ⟨C, ?_, max UH 16, ?_⟩
  · dsimp [C, CE]
    positivity
  · intro X hX
    dsimp only
    let m := Nat.log 4 X
    let j := Nat.log 4 m
    let s : ℝ := ((j + 1 : ℕ) : ℝ)
    have hXH : UH ≤ X := (le_max_left UH 16).trans hX
    have hX16 : 16 ≤ X := (le_max_right UH 16).trans hX
    have hX9 : 9 ≤ X := (by omega : 9 ≤ 16).trans hX16
    have hm2 : 2 ≤ m := by
      have hmmono := Nat.log_mono_right (b := 4) hX16
      norm_num [m] at hmmono ⊢
      exact hmmono
    have hmpos : 0 < m := by omega
    have hmSq : 2 ≤ m ^ 2 := by nlinarith
    have hs : 1 ≤ s := by dsimp [s]; norm_num
    have hs0 : 0 ≤ s := zero_le_one.trans hs
    have hmpowNat : m ≤ 4 ^ (j + 1) := by
      exact (Nat.lt_pow_succ_log_self (by omega : 1 < 4) m).le
    have hmpow : (m : ℝ) ≤ (4 : ℝ) ^ (j + 1) := by
      exact_mod_cast hmpowNat
    have hlogm : Real.log (m : ℝ) ≤ s * Real.log 4 := by
      calc
        Real.log (m : ℝ) ≤ Real.log ((4 : ℝ) ^ (j + 1)) :=
          Real.log_le_log (by positivity) hmpow
        _ = s * Real.log 4 := by
          rw [Real.log_pow]
    have hEuler0 : 0 ≤ Erdos444.PrimeBounds.smallPrimeEulerProduct (m ^ 2) := by
      unfold Erdos444.PrimeBounds.smallPrimeEulerProduct
      apply Finset.prod_nonneg
      intro p hp
      have hpPrime := (Nat.mem_primesLE.mp hp).2
      have hpR : (1 : ℝ) < p := by exact_mod_cast hpPrime.one_lt
      exact inv_nonneg.mpr
        (sub_nonneg.mpr ((div_le_one (by positivity)).2 hpR.le))
    have hEuler : Erdos444.PrimeBounds.smallPrimeEulerProduct (m ^ 2) ≤
        CE * s := by
      calc
        Erdos444.PrimeBounds.smallPrimeEulerProduct (m ^ 2) ≤
            Real.exp (Erdos444.PrimeBounds.mertensConstant + 2) *
              Real.log ((m ^ 2 : ℕ) : ℝ) :=
          Erdos444.PrimeBounds.smallPrimeEulerProduct_le_const_mul_log hmSq
        _ = Real.exp (Erdos444.PrimeBounds.mertensConstant + 2) *
              (2 * Real.log (m : ℝ)) := by
          norm_num [Nat.cast_pow, Real.log_pow]
        _ ≤ CE * s := by
          dsimp [CE]
          nlinarith [Real.exp_pos (Erdos444.PrimeBounds.mertensConstant + 2)]
    have hH := hHbound X hXH
    have hH0 : 0 ≤ Erdos285.RoughCounts.primePowerReciprocalUpTo X := by
      unfold Erdos285.RoughCounts.primePowerReciprocalUpTo
      positivity
    change Erdos444.PrimeBounds.smallPrimeEulerProduct (m ^ 2) *
          (∑ i ∈ Finset.range t,
            Erdos285.RoughCounts.primePowerReciprocalUpTo X ^ i /
              (i.factorial : ℝ)) ≤ C * s ^ (t + 1)
    exact mul_truncatedExp_le_of_linear_bounds
      (Erdos444.PrimeBounds.smallPrimeEulerProduct (m ^ 2))
      (Erdos285.RoughCounts.primePowerReciprocalUpTo X)
      CE CH s t hEuler0 hH0 (by dsimp [CE]; positivity) hCH hs hEuler hH

/-- The weak Stirling lower bound `r! ≥ (r / e)^r`, in the real numbers. -/
theorem factorial_stirling_lower (r : ℕ) :
    ((r : ℝ) / Real.exp 1) ^ r ≤ (r.factorial : ℝ) := by
  by_cases hr : r = 0
  · simp [hr]
  have hr1 : (1 : ℝ) ≤ r := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hr)
  have hsqrt : (1 : ℝ) ≤ √(2 * Real.pi * r) := by
    rw [Real.one_le_sqrt]
    nlinarith [Real.pi_gt_three]
  calc
    ((r : ℝ) / Real.exp 1) ^ r =
        1 * ((r : ℝ) / Real.exp 1) ^ r := by ring
    _ ≤ √(2 * Real.pi * r) * ((r : ℝ) / Real.exp 1) ^ r := by
      exact mul_le_mul_of_nonneg_right hsqrt (pow_nonneg (by positivity) r)
    _ ≤ (r.factorial : ℝ) := Stirling.le_factorial_stirling r

/-- The standard consequence `μ^r / r! ≤ (e μ / r)^r` of weak Stirling. -/
theorem pow_div_factorial_le_exp_mul_div_pow
    (μ : ℝ) (r : ℕ) (hμ : 0 ≤ μ) (hr : 0 < r) :
    μ ^ r / (r.factorial : ℝ) ≤
      (Real.exp 1 * μ / (r : ℝ)) ^ r := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hbase : 0 < ((r : ℝ) / Real.exp 1) ^ r :=
    pow_pos (div_pos hrR (Real.exp_pos 1)) r
  calc
    μ ^ r / (r.factorial : ℝ) ≤
        μ ^ r / (((r : ℝ) / Real.exp 1) ^ r) :=
      div_le_div_of_nonneg_left (pow_nonneg hμ r) hbase
        (factorial_stirling_lower r)
    _ = (μ / ((r : ℝ) / Real.exp 1)) ^ r :=
      (div_pow μ ((r : ℝ) / Real.exp 1) r).symm
    _ = (Real.exp 1 * μ / (r : ℝ)) ^ r := by
      congr 1
      field_simp [hrR.ne', Real.exp_ne_zero]

/-- If `r ≥ α μ`, then the base `e μ / r` is at most `e / α`. -/
theorem exp_mul_div_le_exp_div
    (μ α : ℝ) (r : ℕ) (hα : 0 < α) (hr : 0 < r)
    (hαμ : α * μ ≤ r) :
    Real.exp 1 * μ / (r : ℝ) ≤ Real.exp 1 / α := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  rw [div_le_div_iff₀ hrR hα]
  have hexp : 0 < Real.exp 1 := Real.exp_pos 1
  nlinarith

/-- Power-form large-deviation estimate following from weak Stirling. -/
theorem pow_div_factorial_le_exp_div_pow
    (μ α : ℝ) (r : ℕ) (hμ : 0 ≤ μ) (hα : 0 < α) (hr : 0 < r)
    (hαμ : α * μ ≤ r) :
    μ ^ r / (r.factorial : ℝ) ≤ (Real.exp 1 / α) ^ r := by
  exact (pow_div_factorial_le_exp_mul_div_pow μ r hμ hr).trans
    (pow_le_pow_left₀ (by positivity)
      (exp_mul_div_le_exp_div μ α r hα hr hαμ) r)

/-- Exponential-form large-deviation estimate.  It is useful whenever the
threshold factor `α` is strictly larger than `e`. -/
theorem pow_div_factorial_le_exp_decay
    (μ α : ℝ) (r : ℕ) (hμ : 0 ≤ μ) (hα : Real.exp 1 < α) (hr : 0 < r)
    (hαμ : α * μ ≤ r) :
    μ ^ r / (r.factorial : ℝ) ≤
      Real.exp (-(Real.log α - 1) * (α * μ)) := by
  have hαpos : 0 < α := (Real.exp_pos 1).trans hα
  have hlog : 1 < Real.log α := (Real.lt_log_iff_exp_lt hαpos).2 hα
  calc
    μ ^ r / (r.factorial : ℝ) ≤ (Real.exp 1 / α) ^ r :=
      pow_div_factorial_le_exp_div_pow μ α r hμ hαpos hr hαμ
    _ = Real.exp ((r : ℝ) * (1 - Real.log α)) := by
      rw [show Real.exp 1 / α = Real.exp (1 - Real.log α) by
        rw [Real.exp_sub, Real.exp_log hαpos], Real.exp_nat_mul]
    _ ≤ Real.exp (-(Real.log α - 1) * (α * μ)) := by
      apply Real.exp_monotone
      nlinarith

/-- A canonical integral threshold strictly above `α μ`.  The additional
one makes the threshold positive even when `μ = 0`. -/
noncomputable def deviationIndex (α μ : ℝ) : ℕ :=
  ⌈α * μ⌉₊ + 1

theorem deviationIndex_pos (α μ : ℝ) : 0 < deviationIndex α μ := by
  simp [deviationIndex]

theorem scaled_le_deviationIndex (α μ : ℝ) :
    α * μ ≤ (deviationIndex α μ : ℝ) := by
  calc
    α * μ ≤ (⌈α * μ⌉₊ : ℕ) := Nat.le_ceil _
    _ ≤ (deviationIndex α μ : ℕ) := by
      exact_mod_cast Nat.le_succ ⌈α * μ⌉₊

theorem deviationIndex_lt_scaled_add_two (α μ : ℝ) (hαμ : 0 ≤ α * μ) :
    (deviationIndex α μ : ℝ) < α * μ + 2 := by
  have hceil := Nat.ceil_lt_add_one hαμ
  rw [deviationIndex, Nat.cast_add, Nat.cast_one]
  linarith

/-- Exponential decay at the canonical ceiling threshold. -/
theorem pow_div_factorial_deviationIndex_le_exp_decay
    (μ α : ℝ) (hμ : 0 ≤ μ) (hα : Real.exp 1 < α) :
    μ ^ deviationIndex α μ / (deviationIndex α μ).factorial ≤
      Real.exp (-(Real.log α - 1) * (α * μ)) := by
  exact pow_div_factorial_le_exp_decay μ α (deviationIndex α μ) hμ hα
    (deviationIndex_pos α μ) (scaled_le_deviationIndex α μ)

/-! ## Truncated exponential sums -/

/-- Consecutive terms `H^j / j!` increase as long as `j + 1 ≤ H`. -/
theorem expTerm_step (H : ℝ) (j : ℕ) (hH : (j + 1 : ℕ) ≤ H) :
    H ^ j / (j.factorial : ℝ) ≤
      H ^ (j + 1) / ((j + 1).factorial : ℝ) := by
  have hjfac : (0 : ℝ) < (j.factorial : ℕ) := by positivity
  have hj1 : (0 : ℝ) < j + 1 := by positivity
  have hH' : (j : ℝ) + 1 ≤ H := by exact_mod_cast hH
  have hH0 : 0 ≤ H :=
    (by positivity : (0 : ℝ) ≤ (j : ℝ) + 1) |>.trans hH'
  have hfactor : (1 : ℝ) ≤ H / (j + 1 : ℝ) := by
    rw [le_div_iff₀ hj1]
    simpa using hH'
  rw [show H ^ (j + 1) / ((j + 1).factorial : ℝ) =
      (H ^ j / (j.factorial : ℝ)) * (H / (j + 1 : ℝ)) by
    rw [pow_succ, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    field_simp]
  exact le_mul_of_one_le_right
    (div_nonneg (pow_nonneg hH0 j) hjfac.le) hfactor

/-- Every term up to index `t` is bounded by the `t`-th term when `t ≤ H`. -/
theorem expTerm_mono_to (H : ℝ) {j t : ℕ} (hjt : j ≤ t)
    (htH : (t : ℝ) ≤ H) :
    H ^ j / (j.factorial : ℝ) ≤ H ^ t / (t.factorial : ℝ) := by
  induction t with
  | zero =>
      have : j = 0 := Nat.eq_zero_of_le_zero hjt
      simp [this]
  | succ t ih =>
      by_cases hj : j = t + 1
      · simp [hj]
      · have hjt' : j ≤ t := by omega
        have htcast : (t : ℝ) ≤ (t + 1 : ℕ) := by norm_num
        have htH' : (t : ℝ) ≤ H := htcast.trans htH
        exact (ih hjt' htH').trans (expTerm_step H t htH)

/-- A weak but uniform truncated-exponential estimate.  It deliberately
drops the square-root factor from sharp Stirling; this loses only a
polynomial factor in applications to Problem 444. -/
theorem truncatedExp_le (H : ℝ) (t : ℕ) (ht : 0 < t)
    (htH : (t : ℝ) ≤ H) :
    (∑ j ∈ Finset.range t, H ^ j / (j.factorial : ℝ)) ≤
      (t : ℝ) * (Real.exp 1 * H / (t : ℝ)) ^ t := by
  have hH0 : 0 ≤ H :=
    (by exact_mod_cast (Nat.zero_le t) : (0 : ℝ) ≤ t) |>.trans htH
  have hterm : ∀ j ∈ Finset.range t,
      H ^ j / (j.factorial : ℝ) ≤ H ^ t / (t.factorial : ℝ) := by
    intro j hj
    exact expTerm_mono_to H (Nat.le_of_lt (Finset.mem_range.mp hj)) htH
  calc
    (∑ j ∈ Finset.range t, H ^ j / (j.factorial : ℝ)) ≤
        ∑ _j ∈ Finset.range t, H ^ t / (t.factorial : ℝ) :=
      Finset.sum_le_sum hterm
    _ = (t : ℝ) * (H ^ t / (t.factorial : ℝ)) := by simp
    _ ≤ (t : ℝ) * (Real.exp 1 * H / (t : ℝ)) ^ t := by
      exact mul_le_mul_of_nonneg_left
        (pow_div_factorial_le_exp_mul_div_pow H t hH0 ht)
        (Nat.cast_nonneg t)

end Erdos444
