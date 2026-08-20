/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ErdosProblems.Erdos733.Counting
import ErdosProblems.Erdos733.AnalyticAlt
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Data.Nat.Choose.Bounds

/-!
# Erdős Problem 733: analytic estimates for the dyadic code

This file records the analytic part of the stars-and-bars estimate.  We use
integer division rather than a ceiling of a positive real expression.  This
is important: a ceiling would contribute one dummy line in every remote
dyadic bucket, while the integer cap below is eventually zero.
-/

namespace Erdos733

noncomputable section

/-- A piecewise integral majorant for the usual rich-line estimate.  In the
range `q² ≤ n` its first summand dominates, and in the complementary range
its second summand dominates. -/
def dyadicAnalyticCap (A n i : ℕ) : ℕ :=
  let q := dyadicScale i
  if q ^ 2 ≤ n then A * n ^ 2 / q ^ 3 else A * n / q

lemma dyadicAnalyticCap_of_sq_le {A n i : ℕ}
    (h : dyadicScale i ^ 2 ≤ n) :
    dyadicAnalyticCap A n i = A * n ^ 2 / dyadicScale i ^ 3 := by
  simp [dyadicAnalyticCap, h]

lemma dyadicAnalyticCap_of_lt_sq {A n i : ℕ}
    (h : n < dyadicScale i ^ 2) :
    dyadicAnalyticCap A n i = A * n / dyadicScale i := by
  simp [dyadicAnalyticCap, Nat.not_le_of_lt h]

lemma dyadicAnalyticCap_le_first {A n i : ℕ}
    (h : dyadicScale i ^ 2 ≤ n) :
    dyadicAnalyticCap A n i ≤ A * n ^ 2 / dyadicScale i ^ 3 := by
  rw [dyadicAnalyticCap_of_sq_le h]

lemma dyadicAnalyticCap_le_second {A n i : ℕ}
    (h : n < dyadicScale i ^ 2) :
    dyadicAnalyticCap A n i ≤ A * n / dyadicScale i := by
  rw [dyadicAnalyticCap_of_lt_sq h]

/-- The piecewise cap dominates half the sum of the two real rich-line
terms.  This denominator-cleared form is what is used to pass from the
Szemerédi--Trotter estimate to the integral stars-and-bars code. -/
lemma le_dyadicAnalyticCap_of_cast_le (A n i s : ℕ)
    (hs : (s : ℝ) ≤ (A : ℝ) / 2 *
      ((n : ℝ) ^ 2 / (dyadicScale i : ℝ) ^ 3 +
        (n : ℝ) / dyadicScale i)) :
    s ≤ dyadicAnalyticCap A n i := by
  let q := dyadicScale i
  have hq : 0 < q := dyadicScale_pos i
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  by_cases hlo : q ^ 2 ≤ n
  · rw [dyadicAnalyticCap_of_sq_le hlo]
    apply (Nat.le_div_iff_mul_le (by positivity : 0 < q ^ 3)).2
    exact_mod_cast (show (s : ℝ) * q ^ 3 ≤ A * n ^ 2 by
      have hloR : (q : ℝ) ^ 2 ≤ n := by exact_mod_cast hlo
      have hsecond : (n : ℝ) / q ≤ (n : ℝ) ^ 2 / q ^ 3 := by
        rw [div_le_div_iff₀ hqR (pow_pos hqR 3)]
        calc
          (n : ℝ) * (q : ℝ) ^ 3 = ((n : ℝ) * q) * q ^ 2 := by ring
          _ ≤ ((n : ℝ) * q) * n :=
            mul_le_mul_of_nonneg_left hloR
              (mul_nonneg (Nat.cast_nonneg n) hqR.le)
          _ = (n : ℝ) ^ 2 * q := by ring
      have hmain : (s : ℝ) ≤ A * ((n : ℝ) ^ 2 / q ^ 3) := by
        dsimp [q] at hs ⊢
        nlinarith
      calc
        (s : ℝ) * q ^ 3 ≤
            (A * ((n : ℝ) ^ 2 / q ^ 3)) * q ^ 3 :=
          mul_le_mul_of_nonneg_right hmain (by positivity)
        _ = A * n ^ 2 := by field_simp)
  · have hhi : n < q ^ 2 := Nat.lt_of_not_ge hlo
    rw [dyadicAnalyticCap_of_lt_sq hhi]
    apply (Nat.le_div_iff_mul_le hq).2
    exact_mod_cast (show (s : ℝ) * q ≤ A * n by
      have hhiR : (n : ℝ) ≤ q ^ 2 := by exact_mod_cast hhi.le
      have hfirst : (n : ℝ) ^ 2 / q ^ 3 ≤ (n : ℝ) / q := by
        rw [div_le_div_iff₀ (pow_pos hqR 3) hqR]
        calc
          (n : ℝ) ^ 2 * q = ((n : ℝ) * q) * n := by ring
          _ ≤ ((n : ℝ) * q) * q ^ 2 :=
            mul_le_mul_of_nonneg_left hhiR
              (mul_nonneg (Nat.cast_nonneg n) hqR.le)
          _ = (n : ℝ) * q ^ 3 := by ring
      have hmain : (s : ℝ) ≤ A * ((n : ℝ) / q) := by
        dsimp [q] at hs ⊢
        nlinarith
      calc
        (s : ℝ) * q ≤ (A * ((n : ℝ) / q)) * q :=
          mul_le_mul_of_nonneg_right hmain hqR.le
        _ = A * n := by field_simp)

/-- The standard `e N/k` upper bound for a binomial coefficient. -/
lemma choose_cast_le_exp_mul_log (N k : ℕ) (hk : 0 < k) (hkN : k ≤ N) :
    (N.choose k : ℝ) ≤
      Real.exp ((k : ℝ) * Real.log (Real.exp 1 * (N : ℝ) / k)) := by
  have hchoose : 0 < (N.choose k : ℝ) := by
    exact_mod_cast Nat.choose_pos hkN
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hN : 0 < N := hk.trans_le hkN
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  rw [← Real.log_le_iff_le_exp hchoose]
  calc
    Real.log (N.choose k : ℝ) ≤
        Real.log ((N : ℝ) ^ k / (k.factorial : ℝ)) :=
      Real.log_le_log hchoose (Nat.choose_le_pow_div k N)
    _ = (k : ℝ) * Real.log N - Real.log (k.factorial : ℝ) := by
      rw [Real.log_div (pow_ne_zero _ hNR.ne') (by positivity), Real.log_pow]
    _ ≤ (k : ℝ) * Real.log N -
        ((k : ℝ) * Real.log k - k) := by
      have hstirling := Stirling.le_log_factorial_stirling hk.ne'
      have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
      have hpi1 : (1 : ℝ) ≤ 2 * Real.pi := by
        nlinarith [Real.pi_gt_three]
      linarith [Real.log_nonneg hk1, Real.log_nonneg hpi1]
    _ = (k : ℝ) * Real.log (Real.exp 1 * (N : ℝ) / k) := by
      rw [Real.log_div (mul_pos (Real.exp_pos 1) hNR).ne' hkR.ne',
        Real.log_mul (Real.exp_ne_zero 1) hNR.ne',
        Real.log_exp]
      ring

/-- A logarithm-free consequence of `choose_cast_le_exp_mul_log`, useful
with a small fixed value of `ε` on each side of the square-root cutoff. -/
lemma choose_cast_le_exp_rpow (N k : ℕ) (hk : 0 < k) (hkN : k ≤ N)
    {ε : ℝ} (hε : 0 < ε) :
    (N.choose k : ℝ) ≤
      Real.exp ((k : ℝ) *
        ((Real.exp 1 * (N : ℝ) / k) ^ ε / ε)) := by
  refine (choose_cast_le_exp_mul_log N k hk hkN).trans ?_
  apply Real.exp_le_exp.mpr
  gcongr
  exact Real.log_le_rpow_div (by positivity) hε

/-- Coordinatewise exponential estimates multiply to the exponential of
their sum. -/
lemma cast_prod_choose_le_exp_sum {b : ℕ} (cap : Fin b → ℕ)
    (g : Fin b → ℝ)
    (h : ∀ i : Fin b,
      ((dyadicScale i + cap i).choose (cap i) : ℝ) ≤ Real.exp (g i)) :
    ((∏ i : Fin b, (dyadicScale i + cap i).choose (cap i) : ℕ) : ℝ) ≤
      Real.exp (∑ i : Fin b, g i) := by
  rw [Nat.cast_prod, Real.exp_sum]
  exact Finset.prod_le_prod (fun _ _ ↦ by positivity) (fun i _ ↦ h i)

/-- The exponent used for a single dyadic coordinate.  Below the square-root
cutoff we use symmetry and choose the `q` objects; above the cutoff we choose
the `cap` objects.  Exponents `1/8` and `1/4` leave geometrically summable
majorants on the two respective sides. -/
def dyadicAnalyticExponent (A n i : ℕ) : ℝ :=
  let q := dyadicScale i
  let c := dyadicAnalyticCap A n i
  if c = 0 then 0
  else if q ^ 2 ≤ n then
    (q : ℝ) *
      ((Real.exp 1 * ((q + c : ℕ) : ℝ) / q) ^ (1 / 8 : ℝ) / (1 / 8 : ℝ))
  else
    (c : ℝ) *
      ((Real.exp 1 * ((q + c : ℕ) : ℝ) / c) ^ (1 / 4 : ℝ) / (1 / 4 : ℝ))

lemma choose_dyadicAnalyticCap_le_exp (A n i : ℕ) :
    (((dyadicScale i + dyadicAnalyticCap A n i).choose
      (dyadicAnalyticCap A n i) : ℕ) : ℝ) ≤
      Real.exp (dyadicAnalyticExponent A n i) := by
  let q := dyadicScale i
  let c := dyadicAnalyticCap A n i
  have hq : 0 < q := dyadicScale_pos i
  by_cases hc : c = 0
  · simp [dyadicAnalyticExponent, q, c, hc]
  · have hcpos : 0 < c := Nat.pos_of_ne_zero hc
    by_cases hlo : q ^ 2 ≤ n
    · change (((q + c).choose c : ℕ) : ℝ) ≤
        Real.exp (dyadicAnalyticExponent A n i)
      rw [← Nat.choose_symm_add]
      simpa [dyadicAnalyticExponent, q, c, hc, hlo] using
        (choose_cast_le_exp_rpow (q + c) q hq (Nat.le_add_right q c)
          (by norm_num : (0 : ℝ) < 1 / 8))
    · simpa [dyadicAnalyticExponent, q, c, hc, hlo] using
        (choose_cast_le_exp_rpow (q + c) c hcpos (Nat.le_add_left c q)
          (by norm_num : (0 : ℝ) < 1 / 4))

theorem cast_prod_dyadicAnalyticCap_le_exp_sum (A b n : ℕ) :
    ((∏ i : Fin b,
      (dyadicScale i + dyadicAnalyticCap A n i).choose
        (dyadicAnalyticCap A n i) : ℕ) : ℝ) ≤
      Real.exp (∑ i : Fin b, dyadicAnalyticExponent A n i) := by
  exact cast_prod_choose_le_exp_sum
    (fun i : Fin b ↦ dyadicAnalyticCap A n i)
    (fun i : Fin b ↦ dyadicAnalyticExponent A n i)
    (fun i ↦ choose_dyadicAnalyticCap_le_exp A n i)

lemma sqrt_two_pow (m : ℕ) :
    Real.sqrt ((2 : ℝ) ^ m) = Real.sqrt 2 ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [pow_succ, Real.sqrt_mul (by positivity), ih, pow_succ]

lemma sqrt_dyadicScale (i : ℕ) :
    Real.sqrt (dyadicScale i) = Real.sqrt 2 ^ (i + 1) := by
  simpa [dyadicScale, Nat.cast_pow] using sqrt_two_pow (i + 1)

lemma four_thirds_le_sqrt_two : (4 / 3 : ℝ) ≤ Real.sqrt 2 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hnonneg := Real.sqrt_nonneg 2
  nlinarith

/-- A convenient explicit bound for the increasing half-geometric sum. -/
lemma sum_range_sqrtTwo_pow_succ_le (m : ℕ) :
    ∑ i ∈ Finset.range m, Real.sqrt 2 ^ (i + 1) ≤
      4 * Real.sqrt 2 ^ m := by
  induction m with
  | zero => norm_num
  | succ m ih =>
      rw [Finset.sum_range_succ]
      calc
        ∑ i ∈ Finset.range m, Real.sqrt 2 ^ (i + 1) +
            Real.sqrt 2 ^ (m + 1) ≤
            4 * Real.sqrt 2 ^ m + Real.sqrt 2 ^ (m + 1) :=
          add_le_add ih le_rfl
        _ = (4 + Real.sqrt 2) * Real.sqrt 2 ^ m := by
          rw [pow_succ]
          ring
        _ ≤ 4 * Real.sqrt 2 ^ (m + 1) := by
          rw [pow_succ]
          have hp : 0 ≤ Real.sqrt 2 ^ m := by positivity
          calc
            (4 + Real.sqrt 2) * Real.sqrt 2 ^ m ≤
                (4 * Real.sqrt 2) * Real.sqrt 2 ^ m :=
              mul_le_mul_of_nonneg_right (by
                nlinarith [four_thirds_le_sqrt_two]) hp
            _ = 4 * (Real.sqrt 2 ^ m * Real.sqrt 2) := by ring

/-- The reciprocal half-geometric sum is uniformly bounded. -/
lemma sum_range_inv_sqrtTwo_pow_le_four (m : ℕ) :
    ∑ i ∈ Finset.range m, (1 / Real.sqrt 2) ^ i ≤ 4 := by
  let r : ℝ := 1 / Real.sqrt 2
  have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hr0 : r ≠ 0 := by dsimp [r]; positivity
  have hr1 : r < 1 := by
    dsimp [r]
    rw [div_lt_one hsqrt]
    nlinarith [four_thirds_le_sqrt_two]
  have hsum := geom_sum_Ico_le_of_lt_one (m := 0) (n := m)
    (le_of_lt (by dsimp [r]; positivity : (0 : ℝ) < r)) hr1
  have hinv : (1 - r)⁻¹ ≤ 4 := by
    have hrle : r ≤ 3 / 4 := by
      dsimp [r]
      rw [div_le_iff₀ hsqrt]
      nlinarith [four_thirds_le_sqrt_two]
    rw [inv_eq_one_div, div_le_iff₀ (by linarith : 0 < 1 - r)]
    nlinarith
  have hsum' : ∑ i ∈ Finset.range m, r ^ i ≤ (1 - r)⁻¹ := by
    simpa using hsum
  exact hsum'.trans hinv

lemma rpow_one_eighth_mul_sq_div_fourth {K x y : ℝ}
    (hK : 0 ≤ K) (hx : 0 ≤ x) (hy : 0 < y) :
    (K * x ^ 2 / y ^ 4) ^ (1 / 8 : ℝ) =
      K ^ (1 / 8 : ℝ) * x ^ (1 / 4 : ℝ) / Real.sqrt y := by
  rw [Real.div_rpow (mul_nonneg hK (sq_nonneg x)) (by positivity),
    Real.mul_rpow hK (sq_nonneg x),
    ← Real.rpow_natCast_mul hx 2 (1 / 8 : ℝ),
    ← Real.rpow_natCast_mul hy.le 4 (1 / 8 : ℝ),
    Real.sqrt_eq_rpow]
  norm_num

lemma rpow_one_fourth_mul_sq_div {K x y : ℝ}
    (hK : 0 ≤ K) (hx : 0 ≤ x) (hy : 0 < y) :
    (K * x ^ 2 / y) ^ (1 / 4 : ℝ) =
      K ^ (1 / 4 : ℝ) * Real.sqrt x / y ^ (1 / 4 : ℝ) := by
  rw [Real.div_rpow (mul_nonneg hK (sq_nonneg x)) hy.le,
    Real.mul_rpow hK (sq_nonneg x),
    ← Real.rpow_natCast_mul hx 2 (1 / 4 : ℝ),
    Real.sqrt_eq_rpow]
  norm_num

/-- Pointwise majorant below the square-root cutoff. -/
lemma dyadicAnalyticExponent_le_low (A n i : ℕ)
    (hlo : dyadicScale i ^ 2 ≤ n) :
    dyadicAnalyticExponent A n i ≤
      8 * (Real.exp 1 * ((A : ℝ) + 1)) ^ (1 / 8 : ℝ) *
        (n : ℝ) ^ (1 / 4 : ℝ) * Real.sqrt (dyadicScale i) := by
  let q := dyadicScale i
  let c := dyadicAnalyticCap A n i
  have hq : 0 < q := dyadicScale_pos i
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hloR : (q : ℝ) ^ 2 ≤ n := by exact_mod_cast hlo
  by_cases hc : c = 0
  · simp [dyadicAnalyticExponent, c, hc]
    positivity
  · have hcR : (c : ℝ) ≤ (A : ℝ) * (n : ℝ) ^ 2 / q ^ 3 := by
      rw [show c = A * n ^ 2 / q ^ 3 by
        dsimp [c, q]
        exact dyadicAnalyticCap_of_sq_le hlo]
      calc
        ((A * n ^ 2 / q ^ 3 : ℕ) : ℝ) ≤
            ((A * n ^ 2 : ℕ) : ℝ) / (q ^ 3 : ℕ) := Nat.cast_div_le
        _ = (A : ℝ) * (n : ℝ) ^ 2 / q ^ 3 := by norm_num
    have hcMul : (c : ℝ) * q ^ 3 ≤ A * (n : ℝ) ^ 2 := by
      calc
        (c : ℝ) * q ^ 3 ≤
            ((A : ℝ) * n ^ 2 / q ^ 3) * q ^ 3 :=
          mul_le_mul_of_nonneg_right hcR (by positivity)
        _ = A * n ^ 2 := by field_simp
    have hq4 : (q : ℝ) ^ 4 ≤ (n : ℝ) ^ 2 := by nlinarith
    have hsum : ((q : ℝ) + c) * q ^ 3 ≤
        ((A : ℝ) + 1) * n ^ 2 := by nlinarith
    have hratio : (((q + c : ℕ) : ℝ) / q) ≤
        ((A : ℝ) + 1) * n ^ 2 / q ^ 4 := by
      rw [div_le_div_iff₀ hqR (pow_pos hqR 4)]
      have := mul_le_mul_of_nonneg_right hsum hqR.le
      norm_num at this ⊢
      nlinarith
    have hbase : Real.exp 1 * (((q + c : ℕ) : ℝ) / q) ≤
        Real.exp 1 * (((A : ℝ) + 1) * n ^ 2 / q ^ 4) :=
      mul_le_mul_of_nonneg_left hratio (Real.exp_pos 1).le
    have hrpow := Real.rpow_le_rpow (by positivity) hbase
      (by norm_num : (0 : ℝ) ≤ 1 / 8)
    rw [show dyadicAnalyticExponent A n i =
        (q : ℝ) *
          ((Real.exp 1 * (((q + c : ℕ) : ℝ) / q)) ^ (1 / 8 : ℝ) /
            (1 / 8 : ℝ)) by
      simp only [dyadicAnalyticExponent, q, c, hc, if_false, hlo, if_true]
      field_simp]
    calc
      (q : ℝ) *
          ((Real.exp 1 * (((q + c : ℕ) : ℝ) / q)) ^ (1 / 8 : ℝ) /
            (1 / 8 : ℝ)) ≤
          q * ((Real.exp 1 * (((A : ℝ) + 1) * n ^ 2 / q ^ 4)) ^
            (1 / 8 : ℝ) / (1 / 8 : ℝ)) := by gcongr
      _ = 8 * (Real.exp 1 * ((A : ℝ) + 1)) ^ (1 / 8 : ℝ) *
          (n : ℝ) ^ (1 / 4 : ℝ) * Real.sqrt q := by
        rw [show Real.exp 1 * (((A : ℝ) + 1) * n ^ 2 / q ^ 4) =
            (Real.exp 1 * ((A : ℝ) + 1)) * n ^ 2 / q ^ 4 by ring,
          rpow_one_eighth_mul_sq_div_fourth (by positivity) (Nat.cast_nonneg n) hqR]
        have hsqrt : Real.sqrt q ≠ 0 := (Real.sqrt_pos.2 hqR).ne'
        have hsquare := Real.sq_sqrt hqR.le
        have hqdiv : (q : ℝ) / Real.sqrt q = Real.sqrt q := by
          rw [div_eq_iff hsqrt]
          nlinarith
        field_simp [hsqrt]
        rw [← hsquare]
        rw [Real.sqrt_sq (Real.sqrt_nonneg q)]
        ring

/-- Pointwise majorant above the square-root cutoff. -/
lemma dyadicAnalyticExponent_le_high (A n i : ℕ) (hA : 1 ≤ A)
    (hhi : n < dyadicScale i ^ 2) :
    dyadicAnalyticExponent A n i ≤
      4 * (A : ℝ) * (3 * Real.exp 1) ^ (1 / 4 : ℝ) *
        (n : ℝ) ^ (3 / 4 : ℝ) / Real.sqrt (dyadicScale i) := by
  let q := dyadicScale i
  let c := dyadicAnalyticCap A n i
  have hq : 0 < q := dyadicScale_pos i
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  by_cases hc : c = 0
  · simp [dyadicAnalyticExponent, c, hc]
    positivity
  · have hcpos : 0 < c := Nat.pos_of_ne_zero hc
    have hcEq : c = A * n / q := by
      dsimp [c, q]
      exact dyadicAnalyticCap_of_lt_sq hhi
    have hqle : q ≤ A * n := by
      by_contra hnot
      have hlt : A * n < q := Nat.lt_of_not_ge hnot
      have hz : A * n / q = 0 := Nat.div_eq_of_lt hlt
      omega
    have hn : 0 < n := by
      by_contra hn0
      have : n = 0 := Nat.eq_zero_of_not_pos hn0
      subst n
      have hczero : c = 0 := by simpa using hcEq
      exact hc hczero
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hcR : (c : ℝ) ≤ (A : ℝ) * n / q := by
      rw [hcEq]
      calc
        ((A * n / q : ℕ) : ℝ) ≤ ((A * n : ℕ) : ℝ) / q := Nat.cast_div_le
        _ = (A : ℝ) * n / q := by norm_num
    have hfloor : A * n < (c + 1) * q := by
      rw [← Nat.div_lt_iff_lt_mul hq]
      rw [← hcEq]
      omega
    have hfloorR : (A : ℝ) * n < 2 * c * q := by
      exact_mod_cast (hfloor.trans_le (by
        have hc1 : c + 1 ≤ 2 * c := by omega
        exact Nat.mul_le_mul_right q hc1))
    have hratio : (((q + c : ℕ) : ℝ) / c) ≤
        3 * (q : ℝ) ^ 2 / n := by
      rw [div_le_div_iff₀ (by exact_mod_cast hcpos) hnR]
      have hAreal : (1 : ℝ) ≤ A := by exact_mod_cast hA
      have hhiR : (n : ℝ) ≤ q ^ 2 := by exact_mod_cast hhi.le
      have hqc : (q : ℝ) * n ≤ 2 * c * q ^ 2 := by
        have hAn : (n : ℝ) ≤ A * n := by nlinarith
        have := hAn.trans hfloorR.le
        nlinarith
      norm_num at hqc ⊢
      nlinarith
    have hbase : Real.exp 1 * (((q + c : ℕ) : ℝ) / c) ≤
        Real.exp 1 * (3 * (q : ℝ) ^ 2 / n) :=
      mul_le_mul_of_nonneg_left hratio (Real.exp_pos 1).le
    have hrpow := Real.rpow_le_rpow (by positivity) hbase
      (by norm_num : (0 : ℝ) ≤ 1 / 4)
    rw [show dyadicAnalyticExponent A n i =
        (c : ℝ) *
          ((Real.exp 1 * (((q + c : ℕ) : ℝ) / c)) ^ (1 / 4 : ℝ) /
            (1 / 4 : ℝ)) by
      simp only [dyadicAnalyticExponent, q, c, hc, if_false,
        Nat.not_le_of_lt hhi, if_false]
      field_simp]
    calc
      (c : ℝ) *
          ((Real.exp 1 * (((q + c : ℕ) : ℝ) / c)) ^ (1 / 4 : ℝ) /
            (1 / 4 : ℝ)) ≤
          c * ((Real.exp 1 * (3 * (q : ℝ) ^ 2 / n)) ^ (1 / 4 : ℝ) /
            (1 / 4 : ℝ)) := by gcongr
      _ ≤ ((A : ℝ) * n / q) *
          ((Real.exp 1 * (3 * (q : ℝ) ^ 2 / n)) ^ (1 / 4 : ℝ) /
            (1 / 4 : ℝ)) := by gcongr
      _ = 4 * (A : ℝ) * (3 * Real.exp 1) ^ (1 / 4 : ℝ) *
          (n : ℝ) ^ (3 / 4 : ℝ) / Real.sqrt q := by
        rw [show Real.exp 1 * (3 * (q : ℝ) ^ 2 / n) =
            (3 * Real.exp 1) * q ^ 2 / n by ring,
          rpow_one_fourth_mul_sq_div (by positivity) hqR.le hnR]
        have hsqrt : Real.sqrt q ≠ 0 := (Real.sqrt_pos.2 hqR).ne'
        have hsquare := Real.sq_sqrt hqR.le
        have hn14 : (n : ℝ) ^ (1 / 4 : ℝ) ≠ 0 :=
          (Real.rpow_pos_of_pos hnR _).ne'
        have hnpow : (n : ℝ) ^ (3 / 4 : ℝ) *
            n ^ (1 / 4 : ℝ) = n := by
          rw [← Real.rpow_add hnR]
          norm_num
        field_simp [hsqrt, hn14]
        rw [← hsquare]
        rw [Real.sqrt_sq (Real.sqrt_nonneg q)]
        nlinarith

private lemma sqrt_sqrt_natCast_eq_rpow_quarter (n : ℕ) :
    Real.sqrt (Real.sqrt n) = (n : ℝ) ^ (1 / 4 : ℝ) := by
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul (Nat.cast_nonneg n)]
  norm_num

private lemma rpow_quarter_mul_self (n : ℕ) :
    (n : ℝ) ^ (1 / 4 : ℝ) * n ^ (1 / 4 : ℝ) = Real.sqrt n := by
  obtain rfl | hn := n.eq_zero_or_pos
  · norm_num
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [← Real.rpow_add hnR, Real.sqrt_eq_rpow]
  norm_num

private lemma rpow_three_quarters_mul_inv_quarter {n : ℕ} (hn : 0 < n) :
    (n : ℝ) ^ (3 / 4 : ℝ) * ((n : ℝ) ^ (1 / 4 : ℝ))⁻¹ = Real.sqrt n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [← Real.rpow_neg hnR.le, ← Real.rpow_add hnR, Real.sqrt_eq_rpow]
  norm_num

/-- An explicit positive constant for the dyadic product estimate. -/
def dyadicAnalyticConstant (A : ℕ) : ℝ :=
  32 * (Real.exp 1 * ((A : ℝ) + 1)) ^ (1 / 8 : ℝ) +
    16 * (A : ℝ) * (3 * Real.exp 1) ^ (1 / 4 : ℝ)

lemma dyadicAnalyticConstant_pos (A : ℕ) : 0 < dyadicAnalyticConstant A := by
  unfold dyadicAnalyticConstant
  positivity

/-- The sum of all coordinate exponents is `O(√n)`, uniformly in the
number of dyadic coordinates retained. -/
lemma sum_dyadicAnalyticExponent_le (A b n : ℕ) (hA : 1 ≤ A) :
    ∑ i : Fin b, dyadicAnalyticExponent A n i ≤
      dyadicAnalyticConstant A * Real.sqrt n := by
  obtain rfl | hn := n.eq_zero_or_pos
  · simp [dyadicAnalyticExponent, dyadicAnalyticCap]
  rw [Fin.sum_univ_eq_sum_range]
  let Klo : ℝ := 8 * (Real.exp 1 * ((A : ℝ) + 1)) ^ (1 / 8 : ℝ)
  let Khi : ℝ := 4 * (A : ℝ) * (3 * Real.exp 1) ^ (1 / 4 : ℝ)
  have hpoint : ∀ i ∈ Finset.range b,
      dyadicAnalyticExponent A n i ≤
        (if dyadicScale i ^ 2 ≤ n then
          Klo * (n : ℝ) ^ (1 / 4 : ℝ) * Real.sqrt (dyadicScale i)
        else
          Khi * (n : ℝ) ^ (3 / 4 : ℝ) *
            (Real.sqrt (dyadicScale i))⁻¹) := by
    intro i hi
    by_cases hlo : dyadicScale i ^ 2 ≤ n
    · rw [if_pos hlo]
      simpa [Klo, mul_assoc] using dyadicAnalyticExponent_le_low A n i hlo
    · rw [if_neg hlo]
      have hhi : n < dyadicScale i ^ 2 := Nat.lt_of_not_ge hlo
      simpa [Khi, div_eq_mul_inv, mul_assoc] using
        dyadicAnalyticExponent_le_high A n i hA hhi
  calc
    ∑ i ∈ Finset.range b, dyadicAnalyticExponent A n i ≤
        ∑ i ∈ Finset.range b,
          (if dyadicScale i ^ 2 ≤ n then
            Klo * (n : ℝ) ^ (1 / 4 : ℝ) * Real.sqrt (dyadicScale i)
          else
            Khi * (n : ℝ) ^ (3 / 4 : ℝ) *
              (Real.sqrt (dyadicScale i))⁻¹) :=
      Finset.sum_le_sum hpoint
    _ = Klo * (n : ℝ) ^ (1 / 4 : ℝ) *
          ∑ i ∈ Finset.range b,
            (if dyadicScale i ^ 2 ≤ n then Real.sqrt (dyadicScale i) else 0) +
        Khi * (n : ℝ) ^ (3 / 4 : ℝ) *
          ∑ i ∈ Finset.range b,
            (if n < dyadicScale i ^ 2 then
              (Real.sqrt (dyadicScale i))⁻¹ else 0) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      by_cases hlo : dyadicScale i ^ 2 ≤ n
      · simp [hlo, Nat.not_lt_of_ge hlo]
      · have hhi : n < dyadicScale i ^ 2 := Nat.lt_of_not_ge hlo
        simp [hlo, hhi]
    _ ≤ Klo * (n : ℝ) ^ (1 / 4 : ℝ) *
          (4 * Real.sqrt (Real.sqrt n)) +
        Khi * (n : ℝ) ^ (3 / 4 : ℝ) *
          (4 * (Real.sqrt (Real.sqrt n))⁻¹) := by
      gcongr
      · exact sum_low_sqrt_dyadicScale n b
      · simpa only [Nat.zero_add] using
          (sum_high_inv_sqrt_dyadicScale n 0 b hn)
    _ = dyadicAnalyticConstant A * Real.sqrt n := by
      rw [sqrt_sqrt_natCast_eq_rpow_quarter]
      calc
        Klo * (n : ℝ) ^ (1 / 4 : ℝ) *
              (4 * (n : ℝ) ^ (1 / 4 : ℝ)) +
            Khi * (n : ℝ) ^ (3 / 4 : ℝ) *
              (4 * ((n : ℝ) ^ (1 / 4 : ℝ))⁻¹) =
            4 * Klo *
                ((n : ℝ) ^ (1 / 4 : ℝ) * (n : ℝ) ^ (1 / 4 : ℝ)) +
              4 * Khi *
                ((n : ℝ) ^ (3 / 4 : ℝ) *
                  ((n : ℝ) ^ (1 / 4 : ℝ))⁻¹) := by ring
        _ = 4 * Klo * Real.sqrt n + 4 * Khi * Real.sqrt n := by
          rw [rpow_quarter_mul_self,
            rpow_three_quarters_mul_inv_quarter hn]
        _ = dyadicAnalyticConstant A * Real.sqrt n := by
          dsimp [Klo, Khi, dyadicAnalyticConstant]
          ring

/-- The dyadic stars-and-bars product has the required square-root
exponential bound.  The result is uniform in the number `b` of coordinates,
and hence in particular applies with `b = n`. -/
theorem cast_prod_dyadicAnalyticCap_le_exp_sqrt (A : ℕ) (hA : 1 ≤ A) :
    ∃ D : ℝ, 0 < D ∧ ∀ (n b : ℕ),
      ((∏ i : Fin b,
        (dyadicScale i + dyadicAnalyticCap A n i).choose
          (dyadicAnalyticCap A n i) : ℕ) : ℝ) ≤
        Real.exp (D * Real.sqrt n) := by
  refine ⟨dyadicAnalyticConstant A, dyadicAnalyticConstant_pos A, ?_⟩
  intro n b
  exact (cast_prod_dyadicAnalyticCap_le_exp_sum A b n).trans
    (Real.exp_le_exp.mpr (sum_dyadicAnalyticExponent_le A b n hA))

end

end Erdos733
