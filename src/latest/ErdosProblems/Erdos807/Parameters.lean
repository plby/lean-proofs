/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import Mathlib

/-!
# Lattice parameters for Erdős Problem 807

This file isolates the rounding in the Alon--Bohman--Huang parameter choice.
We use the binary natural logarithm

`m = logParameter n`, `k = structuredSize n`, `r = blockCount n`,

where `k` is the largest multiple of `100` not exceeding `(203 / 100) m`.
All inequalities below are stated over the naturals.  In particular, the
power bounds can be used without introducing real logarithms or floors.
-/

namespace Erdos807

open Filter

/-- The dyadic exponent `⌊log₂ n⌋`. -/
def logParameter (n : ℕ) : ℕ := Nat.log 2 n

/-- The admissible structured-subgraph order: a multiple of `100` just below
`(203 / 100) * logParameter n`. -/
def structuredSize (n : ℕ) : ℕ :=
  100 * ((203 * logParameter n) / 10000)

/-- The number of ten-vertex blocks in the small side of the structured graph. -/
def blockCount (n : ℕ) : ℕ := structuredSize n / 100

/-- Short aliases matching the notation in the mathematical writeup. -/
abbrev m := logParameter
abbrev k := structuredSize
abbrev r := blockCount

@[simp] theorem blockCount_eq (n : ℕ) :
    blockCount n = (203 * logParameter n) / 10000 := by
  simp [blockCount, structuredSize]

@[simp] theorem structuredSize_eq_mul_blockCount (n : ℕ) :
    structuredSize n = 100 * blockCount n := by
  simp [structuredSize, blockCount]

theorem hundred_dvd_structuredSize (n : ℕ) : 100 ∣ structuredSize n := by
  exact ⟨blockCount n, structuredSize_eq_mul_blockCount n⟩

@[simp] theorem structuredSize_mod_hundred (n : ℕ) :
    structuredSize n % 100 = 0 :=
  Nat.mod_eq_zero_of_dvd (hundred_dvd_structuredSize n)

@[simp] theorem structuredSize_div_hundred (n : ℕ) :
    structuredSize n / 100 = blockCount n := rfl

@[simp] theorem structuredSize_div_ten (n : ℕ) :
    structuredSize n / 10 = 10 * blockCount n := by
  rw [structuredSize_eq_mul_blockCount]
  omega

@[simp] theorem nine_mul_structuredSize_div_ten (n : ℕ) :
    9 * structuredSize n / 10 = 90 * blockCount n := by
  rw [structuredSize_eq_mul_blockCount]
  omega

@[simp] theorem structuredSize_sub_blockCount (n : ℕ) :
    structuredSize n - blockCount n = 99 * blockCount n := by
  rw [structuredSize_eq_mul_blockCount]
  omega

/-- Exact lower floor inequality: `k * 100 ≤ 203m`. -/
theorem structuredSize_mul_100_le (n : ℕ) :
    structuredSize n * 100 ≤ 203 * logParameter n := by
  rw [structuredSize]
  calc
    100 * (203 * logParameter n / 10000) * 100 =
        203 * logParameter n / 10000 * 10000 := by ring
    _ ≤ 203 * logParameter n := Nat.div_mul_le_self _ _

/-- Exact upper floor inequality: `203m < 100(k+100)`.  Thus rounding down
loses strictly less than `100` vertices. -/
theorem mul_logParameter_lt_100_mul_structuredSize_add (n : ℕ) :
    203 * logParameter n < 100 * (structuredSize n + 100) := by
  have h := Nat.lt_div_mul_add (a := 203 * logParameter n)
    (b := 10000) (by norm_num)
  rw [structuredSize]
  omega

/-- A convenient rational relaxation, `k ≤ (51/25)m`. -/
theorem twentyfive_mul_structuredSize_le (n : ℕ) :
    25 * structuredSize n ≤ 51 * logParameter n := by
  have h := structuredSize_mul_100_le n
  omega

theorem structuredSize_le_three_mul_logParameter (n : ℕ) :
    structuredSize n ≤ 3 * logParameter n := by
  have h := twentyfive_mul_structuredSize_le n
  omega

theorem blockCount_le_logParameter (n : ℕ) :
    blockCount n ≤ logParameter n := by
  rw [blockCount_eq]
  apply (Nat.div_le_iff_le_mul (by norm_num : 0 < 10000)).2
  omega

/-- The defining dyadic power lies below `n`. -/
theorem pow_logParameter_le {n : ℕ} (hn : 0 < n) :
    2 ^ logParameter n ≤ n := by
  exact Nat.pow_log_le_self 2 hn.ne'

/-- The next dyadic power lies strictly above `n`. -/
theorem lt_pow_logParameter_succ (n : ℕ) :
    n < 2 ^ (logParameter n + 1) := by
  simpa [logParameter, Nat.succ_eq_add_one] using
    Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) n

/-- An exact exponential form of `k ≤ 2.04 log₂ n`. -/
theorem pow_structuredSize_le_pow_logParameter (n : ℕ) :
    2 ^ (25 * structuredSize n) ≤ 2 ^ (51 * logParameter n) := by
  exact Nat.pow_le_pow_right (by norm_num) (twentyfive_mul_structuredSize_le n)

/-- An exact, denominator-free form of `k ≤ 2.04 log₂ n`. -/
theorem pow_structuredSize_le_n {n : ℕ} (hn : 0 < n) :
    2 ^ (25 * structuredSize n) ≤ n ^ 51 := by
  calc
    2 ^ (25 * structuredSize n) ≤ 2 ^ (51 * logParameter n) :=
      pow_structuredSize_le_pow_logParameter n
    _ = (2 ^ logParameter n) ^ 51 := by rw [← pow_mul]; congr 1; omega
    _ ≤ n ^ 51 := Nat.pow_le_pow_left (pow_logParameter_le hn) _

/-- Binary natural logarithms tend to infinity. -/
theorem tendsto_logParameter_atTop :
    Tendsto logParameter atTop atTop := by
  have hlogb : Tendsto (fun n : ℕ ↦ Real.logb 2 (n : ℝ)) atTop atTop :=
    (Real.tendsto_logb_atTop (by norm_num)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have hfloor := (tendsto_nat_floor_atTop (α := ℝ)).comp hlogb
  convert hfloor using 1
  funext n
  change Nat.log 2 n = ⌊Real.logb 2 (n : ℝ)⌋₊
  simpa [logParameter] using (Real.natFloor_logb_natCast 2 n).symm

/-- The block count grows without bound. -/
theorem tendsto_blockCount_atTop :
    Tendsto blockCount atTop atTop := by
  refine tendsto_atTop.2 fun C => ?_
  filter_upwards [tendsto_atTop.1 tendsto_logParameter_atTop (10000 * C)] with n hn
  rw [blockCount_eq]
  apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 10000)).2
  calc
    C * 10000 = 10000 * C := by omega
    _ ≤ logParameter n := hn
    _ ≤ 203 * logParameter n := by omega

/-- Consequently the admissible structured order itself grows without bound. -/
theorem tendsto_structuredSize_atTop :
    Tendsto structuredSize atTop atTop := by
  refine tendsto_atTop_mono' _ ?_ tendsto_blockCount_atTop
  filter_upwards with n
  rw [structuredSize_eq_mul_blockCount]
  omega

/-- A fixed polynomial in the dyadic exponent is eventually dominated by
the corresponding power of two. -/
private theorem eventually_three_mul_pow_fifty_le_two_pow :
    ∀ᶠ x : ℕ in atTop, (3 * x) ^ 50 ≤ 2 ^ x := by
  have ho := (isLittleO_pow_exp_pos_mul_atTop 50
    (Real.log_pos (by norm_num : (1 : ℝ) < 2))).comp_tendsto
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have hsmall := ho.def (by positivity : (0 : ℝ) < 1 / 3 ^ 50)
  filter_upwards [hsmall] with x hx
  simp only [Function.comp_apply] at hx
  rw [Real.norm_of_nonneg (by positivity),
    Real.norm_of_nonneg (Real.exp_pos _).le] at hx
  have hreal : ((3 * x : ℕ) ^ 50 : ℝ) ≤ ((2 ^ x : ℕ) : ℝ) := by
    calc
      ((3 * x : ℕ) ^ 50 : ℝ) = (3 : ℝ) ^ 50 * (x : ℝ) ^ 50 := by
        norm_num only [Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat]
        ring
      _ ≤ (3 : ℝ) ^ 50 *
          ((1 / (3 : ℝ) ^ 50) * Real.exp (Real.log 2 * (x : ℝ))) := by
        gcongr
      _ = Real.exp (Real.log 2 * (x : ℝ)) := by
        field_simp
      _ = (2 : ℝ) ^ x := by
        rw [mul_comm, Real.exp_nat_mul, Real.exp_log (by norm_num)]
      _ = ((2 ^ x : ℕ) : ℝ) := by norm_num
  exact_mod_cast hreal

/-- The polynomial factor used in the moderate-overlap estimate is eventually
absorbed by one dyadic power. -/
theorem eventually_structuredSize_pow_fifty_le_pow_logParameter :
    ∀ᶠ n : ℕ in atTop,
      structuredSize n ^ 50 ≤ 2 ^ logParameter n := by
  have hpoly := tendsto_logParameter_atTop.eventually
    eventually_three_mul_pow_fifty_le_two_pow
  filter_upwards [hpoly] with n hn
  exact (Nat.pow_le_pow_left (structuredSize_le_three_mul_logParameter n) 50).trans hn

/-- Real-valued root form of the polynomial absorption estimate. -/
theorem eventually_structuredSize_cast_le_rpow :
    ∀ᶠ n : ℕ in atTop,
      (structuredSize n : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 50) := by
  filter_upwards [eventually_ge_atTop 1,
    eventually_structuredSize_pow_fifty_le_pow_logParameter] with n hn hpoly
  have hnat : structuredSize n ^ 50 ≤ n :=
    hpoly.trans (pow_logParameter_le (by omega))
  have hreal : Real.rpow (structuredSize n : ℝ) (50 : ℝ) ≤ (n : ℝ) := by
    calc
      Real.rpow (structuredSize n : ℝ) (50 : ℝ) =
          (structuredSize n : ℝ) ^ 50 := Real.rpow_natCast _ _
      _ ≤ (n : ℝ) := by exact_mod_cast hnat
  have hroot := (Real.le_rpow_inv_iff_of_pos
    (by positivity : (0 : ℝ) ≤ structuredSize n)
    (by positivity : (0 : ℝ) ≤ n) (by norm_num : (0 : ℝ) < 50)).2 hreal
  simpa [one_div] using hroot

/-- Any negative power with exponent strictly larger than `1/50` absorbs the
structured-size factor. -/
theorem tendsto_structuredSize_mul_rpow_neg_of
    {a : ℝ} (ha : (1 : ℝ) / 50 < a) :
    Tendsto (fun n : ℕ ↦
      (structuredSize n : ℝ) * (n : ℝ) ^ (-a)) atTop (nhds 0) := by
  have hmajor : Tendsto (fun n : ℕ ↦
      (n : ℝ) ^ (-(a - (1 : ℝ) / 50))) atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop (sub_pos.mpr ha)).comp
      tendsto_natCast_atTop_atTop
  apply squeeze_zero'
  · filter_upwards with n
    positivity
  · filter_upwards [eventually_ge_atTop 1,
      eventually_structuredSize_cast_le_rpow] with n hn hk
    calc
      (structuredSize n : ℝ) * (n : ℝ) ^ (-a) ≤
          (n : ℝ) ^ ((1 : ℝ) / 50) * (n : ℝ) ^ (-a) := by
        gcongr
      _ = (n : ℝ) ^ (-(a - (1 : ℝ) / 50)) := by
        rw [← Real.rpow_add (by positivity : (0 : ℝ) < n)]
        congr 1
        ring
  · exact hmajor

theorem tendsto_structuredSize_mul_rpow_neg_two_div_twentyfive :
    Tendsto (fun n : ℕ ↦
      (structuredSize n : ℝ) * (n : ℝ) ^ (-(2 / 25 : ℝ)))
      atTop (nhds 0) := by
  exact tendsto_structuredSize_mul_rpow_neg_of (by norm_num)

theorem tendsto_structuredSize_mul_rpow_neg_two_div_five :
    Tendsto (fun n : ℕ ↦
      (structuredSize n : ℝ) * (n : ℝ) ^ (-(2 / 5 : ℝ)))
      atTop (nhds 0) := by
  exact tendsto_structuredSize_mul_rpow_neg_of (by norm_num)

/-- Taking a twenty-fifth root and dividing by `n` converts the natural
power estimate used in moderate overlaps into the corresponding real base
estimate. -/
theorem div_le_rpow_neg_one_div_twentyfive_of_pow_le
    {A n : ℕ} (hn : 0 < n) (hpow : A ^ 25 ≤ n ^ 24) :
    (A : ℝ) / (n : ℝ) ≤ (n : ℝ) ^ (-(1 / 25 : ℝ)) := by
  have hpowReal : Real.rpow (A : ℝ) (25 : ℝ) ≤ ((n : ℝ) ^ 24) := by
    calc
      Real.rpow (A : ℝ) (25 : ℝ) = (A : ℝ) ^ 25 := Real.rpow_natCast _ _
      _ ≤ (n : ℝ) ^ 24 := by exact_mod_cast hpow
  have hroot : (A : ℝ) ≤ ((n : ℝ) ^ 24) ^ ((25 : ℝ)⁻¹) :=
    (Real.le_rpow_inv_iff_of_pos (by positivity) (by positivity)
      (by norm_num : (0 : ℝ) < 25)).2 hpowReal
  have hroot' : (A : ℝ) ≤ (n : ℝ) ^ (24 / 25 : ℝ) := by
    calc
      (A : ℝ) ≤ ((n : ℝ) ^ 24) ^ ((25 : ℝ)⁻¹) := hroot
      _ = (n : ℝ) ^ ((24 : ℝ) * (25 : ℝ)⁻¹) := by
        symm
        exact Real.rpow_natCast_mul (by positivity) 24 ((25 : ℝ)⁻¹)
      _ = (n : ℝ) ^ (24 / 25 : ℝ) := rfl
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < n)]
  calc
    (A : ℝ) ≤ (n : ℝ) ^ (24 / 25 : ℝ) := hroot'
    _ = (n : ℝ) ^ (-(1 / 25 : ℝ) + 1) := by congr 1; norm_num
    _ = (n : ℝ) ^ (-(1 / 25 : ℝ)) * (n : ℝ) ^ (1 : ℝ) :=
      Real.rpow_add (by positivity) _ _
    _ = (n : ℝ) ^ (-(1 / 25 : ℝ)) * (n : ℝ) := by
      rw [Real.rpow_one]

/-- Reusable moderate-overlap ratio estimate. -/
theorem div_pow_le_rpow_neg_two_div_twentyfive_of_pow_le
    {A n i : ℕ} (hn : 0 < n) (hi : 2 ≤ i)
    (hpow : A ^ 25 ≤ n ^ 24) :
    ((A : ℝ) / (n : ℝ)) ^ i ≤ (n : ℝ) ^ (-(2 / 25 : ℝ)) := by
  have hbase := div_le_rpow_neg_one_div_twentyfive_of_pow_le hn hpow
  have hbase0 : (0 : ℝ) ≤ (A : ℝ) / (n : ℝ) := by positivity
  have hmajor1 : (n : ℝ) ^ (-(1 / 25 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hn)
      (by norm_num)
  have hbase1 : (A : ℝ) / (n : ℝ) ≤ 1 := hbase.trans hmajor1
  calc
    ((A : ℝ) / (n : ℝ)) ^ i ≤ ((A : ℝ) / (n : ℝ)) ^ 2 :=
      pow_le_pow_of_le_one hbase0 hbase1 hi
    _ ≤ ((n : ℝ) ^ (-(1 / 25 : ℝ))) ^ 2 := by gcongr
    _ = Real.rpow ((n : ℝ) ^ (-(1 / 25 : ℝ))) (2 : ℝ) := by
      symm
      exact Real.rpow_natCast _ _
    _ = (n : ℝ) ^ (-(1 / 25 : ℝ) * 2) := by
      exact (Real.rpow_mul (by positivity : (0 : ℝ) ≤ n)
        (-(1 / 25 : ℝ)) 2).symm
    _ = (n : ℝ) ^ (-(2 / 25 : ℝ)) := by congr 1; norm_num

/-- Reusable fifth-power conversion for the large-overlap range. -/
theorem div_pow_le_rpow_neg_two_div_five_of_pow_mul_lt
    {A B n j : ℕ} (hn : 0 < n) (hB : 0 < B) (hj : 1 ≤ j)
    (hpow : A ^ 5 * n ^ 2 < B ^ 5) :
    ((A : ℝ) / (B : ℝ)) ^ j ≤ (n : ℝ) ^ (-(2 / 5 : ℝ)) := by
  have hpowReal : (A : ℝ) ^ 5 * (n : ℝ) ^ 2 < (B : ℝ) ^ 5 := by
    exact_mod_cast hpow
  have hratioFive : ((A : ℝ) / (B : ℝ)) ^ 5 < 1 / (n : ℝ) ^ 2 := by
    rw [div_pow, div_lt_iff₀ (by positivity : (0 : ℝ) < (B : ℝ) ^ 5)]
    rw [div_mul_eq_mul_div, lt_div_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) ^ 2)]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hpowReal
  have hbase0 : (0 : ℝ) ≤ (A : ℝ) / (B : ℝ) := by positivity
  have hmajor0 : (0 : ℝ) ≤ (n : ℝ) ^ (-(2 / 5 : ℝ)) := by positivity
  have hmajorPow : Real.rpow ((n : ℝ) ^ (-(2 / 5 : ℝ))) (5 : ℝ) =
      1 / (n : ℝ) ^ 2 := by
    calc
      Real.rpow ((n : ℝ) ^ (-(2 / 5 : ℝ))) (5 : ℝ) =
          (n : ℝ) ^ (-(2 / 5 : ℝ) * 5) := by
        exact (Real.rpow_mul (by positivity : (0 : ℝ) ≤ n)
          (-(2 / 5 : ℝ)) 5).symm
      _ = (n : ℝ) ^ (-2 : ℝ) := by congr 1; norm_num
      _ = ((n : ℝ) ^ (2 : ℝ))⁻¹ := Real.rpow_neg (by positivity) 2
      _ = 1 / (n : ℝ) ^ 2 := by simp [one_div]
  have hbase : (A : ℝ) / (B : ℝ) ≤ (n : ℝ) ^ (-(2 / 5 : ℝ)) := by
    apply (Real.rpow_le_rpow_iff hbase0 hmajor0 (by norm_num : (0 : ℝ) < 5)).mp
    calc
      Real.rpow ((A : ℝ) / (B : ℝ)) (5 : ℝ) =
          ((A : ℝ) / (B : ℝ)) ^ 5 := Real.rpow_natCast _ _
      _ ≤ 1 / (n : ℝ) ^ 2 := hratioFive.le
      _ = Real.rpow ((n : ℝ) ^ (-(2 / 5 : ℝ))) (5 : ℝ) := hmajorPow.symm
  have hmajor1 : (n : ℝ) ^ (-(2 / 5 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hn) (by norm_num)
  have hbase1 : (A : ℝ) / (B : ℝ) ≤ 1 := hbase.trans hmajor1
  exact (pow_le_of_le_one hbase0 hbase1 (by omega)).trans hbase

/-- Denominator-free moderate-overlap estimate.  After dividing by `n ^ 25`,
this is the paper's bound
`k^2 * 2^((i-1)/2) / n ≤ n^(-1/25)` (with a little extra slack). -/
theorem moderate_overlap_power_bound_of
    {n i : ℕ} (hn : 0 < n)
    (hpoly : structuredSize n ^ 50 ≤ 2 ^ logParameter n)
    (hi : 10 * i ≤ 9 * structuredSize n) :
    (structuredSize n ^ 2 * 2 ^ ((i - 1) / 2)) ^ 25 ≤ n ^ 24 := by
  have hexponent :
      logParameter n + 25 * ((i - 1) / 2) ≤ 24 * logParameter n := by
    have hk := twentyfive_mul_structuredSize_le n
    omega
  calc
    (structuredSize n ^ 2 * 2 ^ ((i - 1) / 2)) ^ 25 =
        structuredSize n ^ 50 * 2 ^ (25 * ((i - 1) / 2)) := by
      simp only [mul_pow, ← pow_mul]
      rw [mul_comm ((i - 1) / 2) 25]
    _ ≤ 2 ^ logParameter n * 2 ^ (25 * ((i - 1) / 2)) :=
      Nat.mul_le_mul_right _ hpoly
    _ = 2 ^ (logParameter n + 25 * ((i - 1) / 2)) := by rw [pow_add]
    _ ≤ 2 ^ (24 * logParameter n) :=
      Nat.pow_le_pow_right (by norm_num) hexponent
    _ = (2 ^ logParameter n) ^ 24 := by
      rw [← pow_mul]
      congr 1
      omega
    _ ≤ n ^ 24 := Nat.pow_le_pow_left (pow_logParameter_le hn) _

theorem eventually_moderate_overlap_power_bound :
    ∀ᶠ n : ℕ in atTop, ∀ i : ℕ,
      10 * i ≤ 9 * structuredSize n →
        (structuredSize n ^ 2 * 2 ^ ((i - 1) / 2)) ^ 25 ≤ n ^ 24 := by
  filter_upwards [eventually_ge_atTop 1,
    eventually_structuredSize_pow_fifty_le_pow_logParameter] with n hn hpoly
  intro i hi
  exact moderate_overlap_power_bound_of (by omega) hpoly hi

/-- Strengthened moderate-overlap estimate with the factor `2` arising when
slot buckets are bounded using `n ≤ 2*k*q`. -/
theorem moderate_overlap_power_bound_with_two_of
    {n i : ℕ} (hn : 0 < n) (hm : 500 ≤ logParameter n)
    (hpoly : structuredSize n ^ 50 ≤ 2 ^ logParameter n)
    (hi : 10 * i ≤ 9 * structuredSize n) :
    (2 * structuredSize n ^ 2 * 2 ^ ((i - 1) / 2)) ^ 25 ≤ n ^ 24 := by
  have hexponent :
      25 + logParameter n + 25 * ((i - 1) / 2) ≤
        24 * logParameter n := by
    have hk := twentyfive_mul_structuredSize_le n
    omega
  calc
    (2 * structuredSize n ^ 2 * 2 ^ ((i - 1) / 2)) ^ 25 =
        2 ^ 25 * structuredSize n ^ 50 *
          2 ^ (25 * ((i - 1) / 2)) := by
      ring
    _ ≤ 2 ^ 25 * 2 ^ logParameter n *
          2 ^ (25 * ((i - 1) / 2)) := by
      gcongr
    _ = 2 ^ (25 + logParameter n + 25 * ((i - 1) / 2)) := by
      rw [← pow_add, ← pow_add]
    _ ≤ 2 ^ (24 * logParameter n) :=
      Nat.pow_le_pow_right (by norm_num) hexponent
    _ = (2 ^ logParameter n) ^ 24 := by
      rw [← pow_mul]
      congr 1
      omega
    _ ≤ n ^ 24 := Nat.pow_le_pow_left (pow_logParameter_le hn) _

theorem eventually_moderate_overlap_power_bound_with_two :
    ∀ᶠ n : ℕ in atTop, ∀ i : ℕ,
      10 * i ≤ 9 * structuredSize n →
        (2 * structuredSize n ^ 2 * 2 ^ ((i - 1) / 2)) ^ 25 ≤ n ^ 24 := by
  filter_upwards [eventually_ge_atTop 1,
    tendsto_logParameter_atTop.eventually_ge_atTop 500,
    eventually_structuredSize_pow_fifty_le_pow_logParameter] with n hn hm hpoly
  intro i hi
  exact moderate_overlap_power_bound_with_two_of (by omega) hm hpoly hi

/-- Real ratio form consumed by the moderate-overlap moment sum. -/
theorem eventually_moderate_overlap_ratio_bound :
    ∀ᶠ n : ℕ in atTop, ∀ i : ℕ, 2 ≤ i →
      10 * i ≤ 9 * structuredSize n →
        (((2 * structuredSize n ^ 2 * 2 ^ ((i - 1) / 2) : ℕ) : ℝ) /
          (n : ℝ)) ^ i ≤ (n : ℝ) ^ (-(2 / 25 : ℝ)) := by
  filter_upwards [eventually_ge_atTop 1,
    eventually_moderate_overlap_power_bound_with_two] with n hn hpower
  intro i hi hioverlap
  exact div_pow_le_rpow_neg_two_div_twentyfive_of_pow_le
    (by omega) hi (hpower i hioverlap)

/-- The exponent budget behind the large-overlap estimate.  The terms are,
respectively, the seven powers of `n`, one power absorbing `k ^ 5`, the
fixed rounding allowance, and the incidence bits for the new vertices. -/
theorem large_overlap_exponent_bound_of_logParameter_ge
    {n j : ℕ} (hn : 25000 ≤ logParameter n)
    (hj : 10 * j ≤ structuredSize n) :
    8 * logParameter n + 7 +
        5 * (2 * blockCount n + 9 * structuredSize n / 100) ≤
      5 * (structuredSize n - j) := by
  have hround := mul_logParameter_lt_100_mul_structuredSize_add n
  rw [structuredSize_eq_mul_blockCount] at hround hj ⊢
  omega

/-- Denominator-free large-overlap estimate.  It is the fifth-power
cross-multiplication of
`k*n*2^(2r+9k/100-(k-j)) ≤ n^(-2/5)`; keeping the negative exponent on the
right as a denominator avoids every real-valued rounding issue. -/
theorem large_overlap_power_bound_of
    {n j : ℕ} (hn : 25000 ≤ logParameter n)
    (hpoly : structuredSize n ^ 50 ≤ 2 ^ logParameter n)
    (hj : 10 * j ≤ structuredSize n) :
    (structuredSize n * n *
          2 ^ (2 * blockCount n + 9 * structuredSize n / 100)) ^ 5 * n ^ 2 <
      (2 ^ (structuredSize n - j)) ^ 5 := by
  have hnpos : 0 < n := by
    by_contra hnzero
    have : n = 0 := Nat.eq_zero_of_not_pos hnzero
    subst n
    norm_num [logParameter] at hn
  have hkpos : 0 < structuredSize n := by
    rw [structuredSize_eq_mul_blockCount]
    have hr : 0 < blockCount n := by
      rw [blockCount_eq]
      apply Nat.div_pos
      · omega
      · norm_num
    omega
  have hkfive : structuredSize n ^ 5 ≤ 2 ^ logParameter n := by
    exact (Nat.pow_le_pow_right hkpos (by norm_num : 5 ≤ 50)).trans hpoly
  have hnseven : n ^ 7 < 2 ^ (7 * (logParameter n + 1)) := by
    calc
      n ^ 7 < (2 ^ (logParameter n + 1)) ^ 7 :=
        Nat.pow_lt_pow_left (lt_pow_logParameter_succ n) (by norm_num)
      _ = 2 ^ (7 * (logParameter n + 1)) := by
        rw [← pow_mul]
        congr 1
        omega
  have hexponent := large_overlap_exponent_bound_of_logParameter_ge hn hj
  calc
    (structuredSize n * n *
          2 ^ (2 * blockCount n + 9 * structuredSize n / 100)) ^ 5 * n ^ 2 =
        structuredSize n ^ 5 * n ^ 7 *
          2 ^ (5 * (2 * blockCount n + 9 * structuredSize n / 100)) := by
      ring
    _ ≤ 2 ^ logParameter n * n ^ 7 *
          2 ^ (5 * (2 * blockCount n + 9 * structuredSize n / 100)) := by
      gcongr
    _ < 2 ^ logParameter n * 2 ^ (7 * (logParameter n + 1)) *
          2 ^ (5 * (2 * blockCount n + 9 * structuredSize n / 100)) := by
      gcongr
    _ = 2 ^ (8 * logParameter n + 7 +
          5 * (2 * blockCount n + 9 * structuredSize n / 100)) := by
      rw [← pow_add, ← pow_add]
      congr 1
      omega
    _ ≤ 2 ^ (5 * (structuredSize n - j)) :=
      Nat.pow_le_pow_right (by norm_num) hexponent
    _ = (2 ^ (structuredSize n - j)) ^ 5 := by
      rw [← pow_mul]
      congr 1
      omega

theorem eventually_large_overlap_power_bound :
    ∀ᶠ n : ℕ in atTop, ∀ j : ℕ,
      10 * j ≤ structuredSize n →
        (structuredSize n * n *
            2 ^ (2 * blockCount n + 9 * structuredSize n / 100)) ^ 5 * n ^ 2 <
          (2 ^ (structuredSize n - j)) ^ 5 := by
  filter_upwards [tendsto_logParameter_atTop.eventually_ge_atTop 25000,
    eventually_structuredSize_pow_fifty_le_pow_logParameter] with n hn hpoly
  intro j hj
  exact large_overlap_power_bound_of hn hpoly hj

/-- Real ratio form consumed by the large-overlap moment sum. -/
theorem eventually_large_overlap_ratio_bound :
    ∀ᶠ n : ℕ in atTop, ∀ j : ℕ, 1 ≤ j →
      10 * j ≤ structuredSize n →
        ((((structuredSize n * n *
            2 ^ (2 * blockCount n + 9 * structuredSize n / 100) : ℕ) : ℝ) /
          ((2 ^ (structuredSize n - j) : ℕ) : ℝ)) ^ j ≤
            (n : ℝ) ^ (-(2 / 5 : ℝ))) := by
  filter_upwards [eventually_ge_atTop 1,
    eventually_large_overlap_power_bound] with n hn hpower
  intro j hjpos hjoverlap
  exact div_pow_le_rpow_neg_two_div_five_of_pow_mul_lt
    (by omega) (by positivity) hjpos (hpower j hjoverlap)

theorem eventually_hundred_le_structuredSize :
    ∀ᶠ n : ℕ in atTop, 100 ≤ structuredSize n :=
  tendsto_structuredSize_atTop.eventually_ge_atTop 100

theorem eventually_one_le_blockCount :
    ∀ᶠ n : ℕ in atTop, 1 ≤ blockCount n :=
  tendsto_blockCount_atTop.eventually_ge_atTop 1

private theorem three_mul_le_two_pow {x : ℕ} (hx : 4 ≤ x) :
    3 * x ≤ 2 ^ x := by
  induction x, hx using Nat.le_induction with
  | base => norm_num
  | succ x hx ih =>
      rw [pow_succ]
      have hthree : 3 ≤ 2 ^ x := by omega
      omega

/-- Eventually the logarithmic structured order fits inside the ambient
vertex set. -/
theorem eventually_structuredSize_le :
    ∀ᶠ n : ℕ in atTop, structuredSize n ≤ n := by
  filter_upwards [eventually_ge_atTop 64] with n hn
  have hnpos : 0 < n := by omega
  calc
    structuredSize n ≤ 3 * logParameter n :=
      structuredSize_le_three_mul_logParameter n
    _ ≤ n := by
      by_cases hsmall : logParameter n ≤ 5
      · omega
      · have hlogpow : 3 * logParameter n ≤ 2 ^ logParameter n := by
          exact three_mul_le_two_pow (by omega)
        exact hlogpow.trans (pow_logParameter_le hnpos)

/-- Once the dyadic exponent is large enough, the saving `k-r` is at least
`2.008 (m+1)`.  The `m+1` formulation absorbs the gap between `logParameter`
and the real binary logarithm. -/
theorem saving_bound_of_logParameter_ge {n : ℕ}
    (hn : 62000 ≤ logParameter n) :
    2008 * (logParameter n + 1) ≤
      1000 * (structuredSize n - blockCount n) := by
  have hround := mul_logParameter_lt_100_mul_structuredSize_add n
  rw [structuredSize_eq_mul_blockCount] at hround ⊢
  omega

theorem eventually_saving_bound :
    ∀ᶠ n : ℕ in atTop,
      2008 * (logParameter n + 1) ≤
        1000 * (structuredSize n - blockCount n) := by
  filter_upwards [tendsto_logParameter_atTop.eventually_ge_atTop 62000] with n hn
  exact saving_bound_of_logParameter_ge hn

/-- A power-only version of the eventual `2.008 log₂ n` saving. -/
theorem saving_power_bound_of_logParameter_ge {n : ℕ}
    (hn : 62000 ≤ logParameter n) :
    n ^ 2008 < 2 ^ (1000 * (structuredSize n - blockCount n)) := by
  calc
    n ^ 2008 < (2 ^ (logParameter n + 1)) ^ 2008 :=
      Nat.pow_lt_pow_left (lt_pow_logParameter_succ n) (by norm_num)
    _ = 2 ^ (2008 * (logParameter n + 1)) := by
      rw [← pow_mul]
      congr 1
      omega
    _ ≤ 2 ^ (1000 * (structuredSize n - blockCount n)) :=
      Nat.pow_le_pow_right (by norm_num) (saving_bound_of_logParameter_ge hn)

theorem eventually_saving_power_bound :
    ∀ᶠ n : ℕ in atTop,
      n ^ 2008 < 2 ^ (1000 * (structuredSize n - blockCount n)) := by
  filter_upwards [tendsto_logParameter_atTop.eventually_ge_atTop 62000] with n hn
  exact saving_power_bound_of_logParameter_ge hn

end Erdos807
