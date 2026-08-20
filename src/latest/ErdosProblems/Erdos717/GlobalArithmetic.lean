/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Final real-variable estimates for the global chromatic argument. -/

import ErdosProblems.Erdos717.SparseInduction
import ErdosProblems.Erdos717.DensePotential
import Mathlib.Analysis.SpecialFunctions.Log.Monotone

open Function Set
open SimpleGraph

namespace Erdos717

/-- A single explicit constant large enough for every branch of the proof. -/
noncomputable def erdos717Constant : ℝ :=
  (10 : ℝ) ^ (200 : ℕ) + (10 : ℝ) ^ (20 : ℕ) * Real.exp 5001

/-- The target chromatic expression after clearing `sqrt n / log n`. -/
noncomputable def chromaticWeight (n c : ℕ) : ℝ :=
  (c : ℝ) * Real.log (n : ℝ) / Real.sqrt (n : ℝ)

/-- The fourth-root scale used to make independent-set deletion monotone. -/
noncomputable def fourthRoot (x : ℝ) : ℝ := Real.sqrt (Real.sqrt x)

theorem erdos717Constant_pos : 0 < erdos717Constant := by
  simp only [erdos717Constant]
  positivity

theorem fourthRoot_pos {x : ℝ} (hx : 0 < x) : 0 < fourthRoot x := by
  simp only [fourthRoot]
  positivity

theorem fourthRoot_sq {x : ℝ} (hx : 0 ≤ x) :
    fourthRoot x ^ 2 = Real.sqrt x := by
  simp only [fourthRoot]
  exact Real.sq_sqrt (Real.sqrt_nonneg x)

theorem fourthRoot_pow_four {x : ℝ} (hx : 0 ≤ x) :
    fourthRoot x ^ 4 = x := by
  rw [show fourthRoot x ^ 4 = (fourthRoot x ^ 2) ^ 2 by ring,
    fourthRoot_sq hx, Real.sq_sqrt hx]

theorem fourthRoot_eq_rpow {x : ℝ} (hx : 0 ≤ x) :
    fourthRoot x = x ^ (1 / 4 : ℝ) := by
  simp only [fourthRoot, Real.sqrt_eq_rpow]
  rw [← Real.rpow_mul hx]
  norm_num

/-- The universal elementary bound `log n ≤ 2 sqrt n`. -/
theorem chromaticWeight_le_two_mul (n c : ℕ) (hn : 0 < n) :
    chromaticWeight n c ≤ 2 * c := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnR
  have hlog := Real.log_natCast_le_rpow_div n
    (show (0 : ℝ) < 1 / 2 by norm_num)
  rw [← Real.sqrt_eq_rpow] at hlog
  norm_num at hlog
  have hlog' : Real.log (n : ℝ) ≤ 2 * Real.sqrt (n : ℝ) := by
    nlinarith
  rw [chromaticWeight, div_le_iff₀ hsqrt]
  calc
    (c : ℝ) * Real.log (n : ℝ) ≤ (c : ℝ) * (2 * Real.sqrt (n : ℝ)) :=
      mul_le_mul_of_nonneg_left hlog' (by positivity)
    _ = 2 * (c : ℝ) * Real.sqrt (n : ℝ) := by ring

/-- Removing a sufficiently large independent set increases
`χ / n^(1/4)`.  The numerical factor `100` leaves ample room over the
Bernoulli coefficient `4`. -/
theorem chromaticScale_le_after_deletion
    (n n' a c c' : ℕ) (hn : 0 < n) (hn' : 0 < n')
    (hc : 2 ≤ c) (hn'Eq : n' + a = n)
    (hchi : c ≤ c' + 1) (hlarge : 100 * n ≤ a * c) :
    (c : ℝ) / fourthRoot n ≤ (c' : ℝ) / fourthRoot n' := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn'R : (0 : ℝ) < n' := by exact_mod_cast hn'
  have hcR : (2 : ℝ) ≤ c := by exact_mod_cast hc
  have hchiCast : (c : ℝ) ≤ (c' : ℝ) + 1 := by exact_mod_cast hchi
  have hchiR : (c : ℝ) - 1 ≤ c' := by linarith
  have hlargeR : (100 : ℝ) * n ≤ a * c := by exact_mod_cast hlarge
  have hnEqR : (n' : ℝ) + a = n := by exact_mod_cast hn'Eq
  have hbern : (c : ℝ) ^ 4 - 4 * (c : ℝ) ^ 3 ≤ ((c : ℝ) - 1) ^ 4 := by
    have h := pow_add_mul_le_add_pow (R := ℝ)
      (a := (c : ℝ)) (b := (-1 : ℝ)) (by positivity)
      (by nlinarith) 4
    norm_num at h ⊢
    nlinarith
  have hca : (4 : ℝ) * (c : ℝ) ^ 3 * n ≤ (c : ℝ) ^ 4 * a := by
    have hmul := mul_le_mul_of_nonneg_left hlargeR
      (show (0 : ℝ) ≤ (c : ℝ) ^ 3 by positivity)
    calc
      (4 : ℝ) * (c : ℝ) ^ 3 * n ≤ 100 * (c : ℝ) ^ 3 * n := by
        gcongr
        norm_num
      _ = (c : ℝ) ^ 3 * (100 * n) := by ring
      _ ≤ (c : ℝ) ^ 3 * (a * c) := hmul
      _ = (c : ℝ) ^ 4 * a := by ring
  have hpowerSub : (c : ℝ) ^ 4 * n' ≤ ((c : ℝ) - 1) ^ 4 * n := by
    have hbernMul := mul_le_mul_of_nonneg_right hbern
      (show (0 : ℝ) ≤ n by positivity)
    calc
      (c : ℝ) ^ 4 * n' ≤
          ((c : ℝ) ^ 4 - 4 * (c : ℝ) ^ 3) * n := by
        rw [← hnEqR]
        nlinarith
      _ ≤ ((c : ℝ) - 1) ^ 4 * n := hbernMul
  have hpowerChi : ((c : ℝ) - 1) ^ 4 * n ≤ (c' : ℝ) ^ 4 * n := by
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (by nlinarith) hchiR 4) (by positivity)
  have hcrossPower :
      ((c : ℝ) * fourthRoot n') ^ 4 ≤
        ((c' : ℝ) * fourthRoot n) ^ 4 := by
    rw [mul_pow, mul_pow, fourthRoot_pow_four hn'R.le,
      fourthRoot_pow_four hnR.le]
    exact hpowerSub.trans hpowerChi
  have hcross : (c : ℝ) * fourthRoot n' ≤
      (c' : ℝ) * fourthRoot n :=
    (pow_le_pow_iff_left₀
      (mul_nonneg (by positivity) (fourthRoot_pos hn'R).le)
      (mul_nonneg (by positivity) (fourthRoot_pos hnR).le)
      (by norm_num)).mp hcrossPower
  exact (div_le_div_iff₀ (fourthRoot_pos hnR) (fourthRoot_pos hn'R)).2 hcross

/-- The second fourth-root factor, `log x / x^(1/4)`, is antitone once
`x ≥ exp 4`. -/
theorem log_div_fourthRoot_antitone
    {x y : ℝ} (hx : Real.exp 4 ≤ x) (hy : x ≤ y) :
    Real.log y / fourthRoot y ≤ Real.log x / fourthRoot x := by
  have hy0 : 0 ≤ y := (Real.exp_pos 4).le.trans (hx.trans hy)
  have hx0 : 0 ≤ x := (Real.exp_pos 4).le.trans hx
  have hanti := Real.log_div_self_rpow_antitoneOn
    (show (0 : ℝ) < 1 / 4 by norm_num)
    (show x ∈ Set.Ici (Real.exp ((1 / 4 : ℝ))⁻¹) by
      have hinv : ((1 / 4 : ℝ)⁻¹) = 4 := by norm_num
      simpa only [Set.mem_Ici, hinv] using hx)
    (show y ∈ Set.Ici (Real.exp ((1 / 4 : ℝ))⁻¹) by
      have hinv : ((1 / 4 : ℝ)⁻¹) = 4 := by norm_num
      simpa only [Set.mem_Ici, hinv] using hx.trans hy)
    hy
  simpa only [fourthRoot_eq_rpow hx0, fourthRoot_eq_rpow hy0] using hanti

/-- Factorization of the final weight into the two fourth-root factors. -/
theorem chromaticWeight_eq_fourthRoot_factors
    (n c : ℕ) (hn : 0 < n) :
    chromaticWeight n c =
      ((c : ℝ) / fourthRoot n) *
        (Real.log (n : ℝ) / fourthRoot n) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hroot : fourthRoot (n : ℝ) ≠ 0 := (fourthRoot_pos hnR).ne'
  rw [chromaticWeight]
  rw [div_mul_div_comm]
  rw [← pow_two, fourthRoot_sq hnR.le]

theorem exp_four_lt_hundred : Real.exp 4 < 100 := by
  calc
    Real.exp 4 = (Real.exp 1) ^ (4 : ℕ) := by
      norm_num [← Real.exp_nat_mul]
    _ < (3 : ℝ) ^ (4 : ℕ) := by gcongr; exact Real.exp_one_lt_three
    _ < 100 := by norm_num

theorem densePotential_eq_product (n a : ℕ) (hn : 0 < n) :
    densePotential n a =
      Real.exp (-5000) * Real.sqrt (n : ℝ) *
        Real.exp (Real.log (n : ℝ) / (8 * a)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnR
  rw [densePotential]
  rw [show Real.log (n : ℝ) / 2 + Real.log (n : ℝ) / (8 * (a : ℝ)) - 5000 =
    -5000 + Real.log (Real.sqrt (n : ℝ)) +
      Real.log (n : ℝ) / (8 * (a : ℝ)) by
      rw [Real.log_sqrt hnR.le]
      ring]
  rw [Real.exp_add, Real.exp_add, Real.exp_log hsqrt]

/-- The dense potential estimate implies the desired weighted chromatic
bound whenever the independence number is within a fixed factor of
`n / χ`. -/
theorem dense_active_weight_lt
    (n a c s : ℕ) (hn : 0 < n) (ha : 0 < a) (hs : 1 ≤ s)
    (hlogn : 0 < Real.log (n : ℝ))
    (hactive : (c : ℝ) * a < 100 * n)
    (hpot : densePotential n a < s + 1) :
    chromaticWeight n c < erdos717Constant * s := by
  let x := Real.log (n : ℝ)
  let t := x / (8 * (a : ℝ))
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hsR : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnR
  have htPos : 0 < t := by
    dsimp only [t, x]
    positivity
  have hcast : (s : ℝ) + 1 ≤ 2 * (s : ℝ) := by linarith
  have hpotBound : densePotential n a < 2 * (s : ℝ) := hpot.trans_le hcast
  have hpot' : Real.exp (-5000) * Real.sqrt (n : ℝ) * Real.exp t <
      2 * (s : ℝ) := by
    simpa only [densePotential_eq_product n a hn, t, x] using hpotBound
  have htBound : t ≤ Real.exp (-1) * Real.exp t := by
    have hstd := Real.mul_exp_neg_le_exp_neg_one t
    have hmul := mul_le_mul_of_nonneg_right hstd (Real.exp_pos t).le
    rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one] at hmul
    exact hmul
  have hconstant :
      800 * (Real.exp (-1) * Real.exp t) <
        (erdos717Constant / 2) * Real.exp (-5000) * Real.exp t := by
    have he1 : (1 : ℝ) < Real.exp 1 := Real.one_lt_exp_iff.mpr (by norm_num)
    have heNeg : Real.exp (-1) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
    have hlarge : (800 : ℝ) <
        (erdos717Constant / 2) * Real.exp (-5000) := by
      have hpart : ((10 : ℝ) ^ (20 : ℕ) * Real.exp 5001 / 2) *
          Real.exp (-5000) = (10 : ℝ) ^ (20 : ℕ) / 2 * Real.exp 1 := by
        calc
          ((10 : ℝ) ^ (20 : ℕ) * Real.exp 5001 / 2) * Real.exp (-5000) =
              ((10 : ℝ) ^ (20 : ℕ) / 2) *
                (Real.exp 5001 * Real.exp (-5000)) := by ring
          _ = ((10 : ℝ) ^ (20 : ℕ) / 2) * Real.exp (5001 + -5000) := by
            rw [Real.exp_add]
          _ = (10 : ℝ) ^ (20 : ℕ) / 2 * Real.exp 1 := by norm_num
      have hCpart : (10 : ℝ) ^ (20 : ℕ) * Real.exp 5001 ≤
          erdos717Constant := by
        simp only [erdos717Constant]
        exact le_add_of_nonneg_left (by positivity)
      have hnonneg : (0 : ℝ) ≤ Real.exp (-5000) := (Real.exp_pos _).le
      have hmul := mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right hCpart (by norm_num : (0 : ℝ) ≤ 2)) hnonneg
      rw [hpart] at hmul
      have hnum : (800 : ℝ) < (10 : ℝ) ^ (20 : ℕ) / 2 := by norm_num
      have hgrow := mul_lt_mul_of_pos_left he1
        (show (0 : ℝ) < (10 : ℝ) ^ (20 : ℕ) / 2 by positivity)
      have hgrow' : (10 : ℝ) ^ (20 : ℕ) / 2 <
          (10 : ℝ) ^ (20 : ℕ) / 2 * Real.exp 1 := by
        simpa only [mul_one] using hgrow
      exact hnum.trans (hgrow'.trans_le hmul)
    have hcoef : 800 * Real.exp (-1) <
        (erdos717Constant / 2) * Real.exp (-5000) := by
      have hshrink : 800 * Real.exp (-1) < (800 : ℝ) := by
        simpa only [mul_one] using
          (mul_lt_mul_of_pos_left heNeg (by norm_num : (0 : ℝ) < 800))
      exact hshrink.trans hlarge
    simpa only [mul_assoc] using
      mul_lt_mul_of_pos_right hcoef (Real.exp_pos t)
  have htConstant : 800 * t <
      (erdos717Constant / 2) * Real.exp (-5000) * Real.exp t :=
    (mul_le_mul_of_nonneg_left htBound (by norm_num)).trans_lt hconstant
  have hcx : (c : ℝ) * x < 800 * (n : ℝ) * t := by
    have hactive' : (c : ℝ) * a < 100 * (n : ℝ) := by
      simpa only [Nat.cast_ofNat, Nat.cast_mul] using hactive
    have htEq : x = 8 * (a : ℝ) * t := by
      dsimp only [t]
      field_simp
    calc
      (c : ℝ) * x = ((c : ℝ) * a) * (8 * t) := by rw [htEq]; ring
      _ < (100 * (n : ℝ)) * (8 * t) :=
        mul_lt_mul_of_pos_right hactive' (mul_pos (by norm_num) htPos)
      _ = 800 * (n : ℝ) * t := by ring
  have hweightPot : chromaticWeight n c <
      (erdos717Constant / 2) * densePotential n a := by
    rw [chromaticWeight, densePotential_eq_product n a hn]
    rw [div_lt_iff₀ hsqrt]
    have hsqrtSq : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = n := by
      nlinarith [Real.sq_sqrt hnR.le]
    change (c : ℝ) * x <
      (erdos717Constant / 2) *
        (Real.exp (-5000) * Real.sqrt (n : ℝ) * Real.exp t) *
          Real.sqrt (n : ℝ)
    calc
      (c : ℝ) * x < 800 * (n : ℝ) * t := hcx
      _ = (n : ℝ) * (800 * t) := by ring
      _ < (n : ℝ) *
          ((erdos717Constant / 2) * Real.exp (-5000) * Real.exp t) :=
        mul_lt_mul_of_pos_left htConstant hnR
      _ = ((erdos717Constant / 2) * Real.exp (-5000) * Real.exp t) *
          (Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ)) := by rw [hsqrtSq]; ring
      _ = (erdos717Constant / 2) *
          (Real.exp (-5000) * Real.sqrt (n : ℝ) * Real.exp t) *
            Real.sqrt (n : ℝ) := by ring
  calc
    chromaticWeight n c < (erdos717Constant / 2) * densePotential n a :=
      hweightPot
    _ < (erdos717Constant / 2) * (2 * (s : ℝ)) :=
      mul_lt_mul_of_pos_left hpotBound (by positivity [erdos717Constant_pos])
    _ = erdos717Constant * s := by ring

/-- The sparse potential estimate implies the desired weighted chromatic
bound in the logarithmically controlled sparse regime. -/
theorem sparse_active_weight_lt
    (n m a c s : ℕ) (hn : 0 < n) (hm : 0 < m) (ha : 0 < a)
    (hs : 1 ≤ s)
    (hlogn : 0 < Real.log (n : ℝ))
    (hactive : (c : ℝ) * a < 100 * n)
    (hlogCondition :
      ((m : ℝ) / (n : ℝ) ^ 2) * a *
          Real.log (1 / ((m : ℝ) / (n : ℝ) ^ 2)) ≤
        Real.log (n : ℝ) / 10000000000000000)
    (hpot : sparsePotential n m a < s + 1) :
    chromaticWeight n c < erdos717Constant * s := by
  let d : ℝ := (m : ℝ) / (n : ℝ) ^ 2
  let x : ℝ := Real.log (n : ℝ)
  let y : ℝ := Real.log (1 / d)
  let t : ℝ := x / (1000000000000 * d * a)
  let u : ℝ := 999 * t / 1000
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hsR : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hd : 0 < d := by positivity
  have hxPos : 0 < x := by simpa only [x] using hlogn
  have hx : 0 ≤ x := hxPos.le
  have htPos : 0 < t := by positivity
  have ht : 0 ≤ t := htPos.le
  have hu : 0 ≤ u := by positivity
  have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnR
  have hcast : (s : ℝ) + 1 ≤ 2 * (s : ℝ) := by linarith
  have hpotBound : sparsePotential n m a < 2 * (s : ℝ) := hpot.trans_le hcast
  have hpot' : Real.exp (-1000) * d ^ 4 * Real.sqrt (n : ℝ) * Real.exp t <
      2 * (s : ℝ) := by
    simpa only [d, x, t, sparsePotential] using hpotBound
  have htEq : x = 1000000000000 * d * (a : ℝ) * t := by
    dsimp only [t]
    field_simp
  have hyLe : y ≤ t / 10000 := by
    have hA : 0 < d * (a : ℝ) := mul_pos hd haR
    have hlog' : d * (a : ℝ) * y ≤ x / 10000000000000000 := by
      simpa only [d, x, y] using hlogCondition
    rw [htEq] at hlog'
    have hscaled : d * (a : ℝ) * y ≤
        (d * (a : ℝ)) * (t / 10000) := by
      calc
        d * (a : ℝ) * y ≤
            (1000000000000 * d * (a : ℝ) * t) / 10000000000000000 := hlog'
        _ = (d * (a : ℝ)) * (t / 10000) := by ring
    exact le_of_mul_le_mul_left (by simpa only [mul_assoc] using hscaled) hA
  have hthreeY : 3 * y ≤ t / 1000 := by nlinarith
  have hlogd : Real.log d = -y := by
    dsimp only [y]
    rw [one_div, Real.log_inv]
    ring
  have hdPow : d ^ 3 = Real.exp (-3 * y) := by
    calc
      d ^ 3 = Real.exp (Real.log (d ^ 3)) :=
        (Real.exp_log (pow_pos hd 3)).symm
      _ = Real.exp (-3 * y) := by
        rw [Real.log_pow, hlogd]
        congr 1
        ring
  have hdPowLower : Real.exp (-t / 1000) ≤ d ^ 3 := by
    rw [hdPow]
    exact Real.exp_le_exp.mpr (by linarith)
  have hproduct : Real.exp u ≤ d ^ 3 * Real.exp t := by
    calc
      Real.exp u = Real.exp (-t / 1000) * Real.exp t := by
        rw [← Real.exp_add]
        congr 1
        dsimp only [u]
        ring
      _ ≤ d ^ 3 * Real.exp t :=
        mul_le_mul_of_nonneg_right hdPowLower (Real.exp_pos t).le
  have htExp : t ≤ 2 * Real.exp u := by
    have huExp : u ≤ Real.exp u := by
      linarith [Real.add_one_le_exp u]
    have htu : t ≤ 2 * u := by
      dsimp only [u]
      nlinarith
    exact htu.trans (mul_le_mul_of_nonneg_left huExp (by norm_num))
  have htProduct : t ≤ 2 * (d ^ 3 * Real.exp t) :=
    htExp.trans (mul_le_mul_of_nonneg_left hproduct (by norm_num))
  have hconstant : (200000000000000 : ℝ) <
      (erdos717Constant / 2) * Real.exp (-1000) := by
    have he : (1 : ℝ) < Real.exp 4001 :=
      Real.one_lt_exp_iff.mpr (by norm_num)
    have hpart : ((10 : ℝ) ^ (20 : ℕ) * Real.exp 5001 / 2) *
        Real.exp (-1000) = (10 : ℝ) ^ (20 : ℕ) / 2 * Real.exp 4001 := by
      calc
        ((10 : ℝ) ^ (20 : ℕ) * Real.exp 5001 / 2) * Real.exp (-1000) =
            ((10 : ℝ) ^ (20 : ℕ) / 2) *
              (Real.exp 5001 * Real.exp (-1000)) := by ring
        _ = ((10 : ℝ) ^ (20 : ℕ) / 2) * Real.exp (5001 + -1000) := by
          rw [Real.exp_add]
        _ = (10 : ℝ) ^ (20 : ℕ) / 2 * Real.exp 4001 := by norm_num
    have hCpart : (10 : ℝ) ^ (20 : ℕ) * Real.exp 5001 ≤
        erdos717Constant := by
      simp only [erdos717Constant]
      exact le_add_of_nonneg_left (by positivity)
    have hnonneg : (0 : ℝ) ≤ Real.exp (-1000) := (Real.exp_pos _).le
    have hmul := mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right hCpart (by norm_num : (0 : ℝ) ≤ 2)) hnonneg
    rw [hpart] at hmul
    have hnum : (200000000000000 : ℝ) < (10 : ℝ) ^ (20 : ℕ) / 2 := by
      norm_num
    have hgrow := mul_lt_mul_of_pos_left he
      (show (0 : ℝ) < (10 : ℝ) ^ (20 : ℕ) / 2 by positivity)
    have hgrow' : (10 : ℝ) ^ (20 : ℕ) / 2 <
        (10 : ℝ) ^ (20 : ℕ) / 2 * Real.exp 4001 := by
      simpa only [mul_one] using hgrow
    exact hnum.trans (hgrow'.trans_le hmul)
  have htConstant : (100000000000000 : ℝ) * t <
      (erdos717Constant / 2) * Real.exp (-1000) * d ^ 3 * Real.exp t := by
    have hscaled := mul_le_mul_of_nonneg_left htProduct
      (show (0 : ℝ) ≤ 100000000000000 by norm_num)
    have hstrict := mul_lt_mul_of_pos_right hconstant
      (mul_pos (pow_pos hd 3) (Real.exp_pos t))
    nlinarith
  have hcx : (c : ℝ) * x <
      100000000000000 * d * (n : ℝ) * t := by
    have hactive' : (c : ℝ) * a < 100 * (n : ℝ) := by
      simpa only [Nat.cast_ofNat, Nat.cast_mul] using hactive
    calc
      (c : ℝ) * x = ((c : ℝ) * a) * (1000000000000 * d * t) := by
        rw [htEq]
        ring
      _ < (100 * (n : ℝ)) * (1000000000000 * d * t) :=
        mul_lt_mul_of_pos_right hactive'
          (show 0 < (1000000000000 : ℝ) * d * t by positivity)
      _ = 100000000000000 * d * (n : ℝ) * t := by ring
  have hweightPot : chromaticWeight n c <
      (erdos717Constant / 2) * sparsePotential n m a := by
    rw [chromaticWeight]
    rw [show sparsePotential n m a =
      Real.exp (-1000) * d ^ 4 * Real.sqrt (n : ℝ) * Real.exp t by rfl]
    rw [div_lt_iff₀ hsqrt]
    have hsqrtSq : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = n := by
      nlinarith [Real.sq_sqrt hnR.le]
    change (c : ℝ) * x <
      (erdos717Constant / 2) *
        (Real.exp (-1000) * d ^ 4 * Real.sqrt (n : ℝ) * Real.exp t) *
          Real.sqrt (n : ℝ)
    calc
      (c : ℝ) * x < 100000000000000 * d * (n : ℝ) * t := hcx
      _ = (d * (n : ℝ)) * (100000000000000 * t) := by ring
      _ < (d * (n : ℝ)) *
          ((erdos717Constant / 2) * Real.exp (-1000) * d ^ 3 * Real.exp t) :=
        mul_lt_mul_of_pos_left htConstant (mul_pos hd hnR)
      _ = ((erdos717Constant / 2) * Real.exp (-1000) * d ^ 4 * Real.exp t) *
          (Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ)) := by rw [hsqrtSq]; ring
      _ = (erdos717Constant / 2) *
          (Real.exp (-1000) * d ^ 4 * Real.sqrt (n : ℝ) * Real.exp t) *
            Real.sqrt (n : ℝ) := by ring
  calc
    chromaticWeight n c < (erdos717Constant / 2) * sparsePotential n m a :=
      hweightPot
    _ < (erdos717Constant / 2) * (2 * (s : ℝ)) :=
      mul_lt_mul_of_pos_left hpotBound (by positivity [erdos717Constant_pos])
    _ = erdos717Constant * s := by ring

/-- If the sparse logarithmic hypothesis fails, the elementary
topological-density estimate is already strong enough.  The factor
`sqrt d * log (1/d)` is bounded by an absolute constant. -/
theorem sparse_log_failure_active_weight_lt
    (n a c s : ℕ) (d : ℝ) (hn : 0 < n) (ha : 0 < a)
    (hc : 0 < c) (hs : 1 ≤ s)
    (hd : 0 < d) (hdle : d ≤ 1)
    (hactive : (c : ℝ) * a < 100 * n)
    (hlogFailure : Real.log (n : ℝ) / 10000000000000000 <
      d * a * Real.log (1 / d))
    (hdensity : d * n < 20 * (s : ℝ) ^ 2) :
    chromaticWeight n c < erdos717Constant * s := by
  let x : ℝ := Real.log (n : ℝ)
  let y : ℝ := Real.log (1 / d)
  let u : ℝ := y / 2
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  have hsR : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hsqrtN : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnR
  have hy : 0 ≤ y := by
    dsimp only [y]
    apply Real.log_nonneg
    rw [one_le_div₀ hd]
    exact hdle
  have hyPos : 0 < y := by
    have hfail : x / 10000000000000000 < d * (a : ℝ) * y := by
      simpa only [x, y] using hlogFailure
    have hx : 0 ≤ x := by
      dsimp only [x]
      exact Real.log_natCast_nonneg n
    by_contra hnot
    have hyNonpos : y ≤ 0 := le_of_not_gt hnot
    have hleft : 0 ≤ x / (10000000000000000 : ℝ) := by positivity
    have hright : d * (a : ℝ) * y ≤ 0 := by
      have hda : 0 < d * (a : ℝ) := mul_pos hd haR
      exact mul_nonpos_of_nonneg_of_nonpos hda.le hyNonpos
    linarith
  have hcx : (c : ℝ) * x <
      1000000000000000000 * d * (n : ℝ) * y := by
    have hfail : x / 10000000000000000 < d * (a : ℝ) * y := by
      simpa only [x, y] using hlogFailure
    have hfailMul := mul_lt_mul_of_pos_left hfail hcR
    have hactive' : (c : ℝ) * a < 100 * (n : ℝ) := by
      simpa only [Nat.cast_ofNat, Nat.cast_mul] using hactive
    have hactiveMul := mul_lt_mul_of_pos_left hactive'
      (mul_pos hd hyPos)
    nlinarith
  have hlogd : Real.log d = -y := by
    dsimp only [y]
    rw [one_div, Real.log_inv]
    ring
  have hsqrtD : Real.sqrt d = Real.exp (-u) := by
    have hsqrtDPos : 0 < Real.sqrt d := Real.sqrt_pos.2 hd
    calc
      Real.sqrt d = Real.exp (Real.log (Real.sqrt d)) :=
        (Real.exp_log hsqrtDPos).symm
      _ = Real.exp (-u) := by
        rw [Real.log_sqrt hd.le, hlogd]
        congr 1
        dsimp only [u]
        ring
  have hu : 0 ≤ u := by positivity
  have hySqrt : y * Real.sqrt d ≤ 2 := by
    have hstd := Real.mul_exp_neg_le_exp_neg_one u
    have heNeg : Real.exp (-1) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
    rw [hsqrtD]
    have hrewrite : y * Real.exp (-u) = 2 * (u * Real.exp (-u)) := by
      dsimp only [u]
      ring
    rw [hrewrite]
    nlinarith
  have hsqrtDensity : Real.sqrt (d * (n : ℝ)) < 5 * (s : ℝ) := by
    have hsq : d * (n : ℝ) < (5 * (s : ℝ)) ^ 2 := by
      nlinarith
    have hroot := Real.sqrt_lt_sqrt (mul_nonneg hd.le hnR.le) hsq
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)] at hroot
    exact hroot
  have hidentity :
      d * (n : ℝ) * y / Real.sqrt (n : ℝ) =
        Real.sqrt (d * (n : ℝ)) * (y * Real.sqrt d) := by
    apply (div_eq_iff hsqrtN.ne').2
    rw [Real.sqrt_mul hd.le]
    calc
      d * (n : ℝ) * y =
          Real.sqrt d ^ 2 * Real.sqrt (n : ℝ) ^ 2 * y := by
        rw [Real.sq_sqrt hd.le, Real.sq_sqrt hnR.le]
      _ = (Real.sqrt d * Real.sqrt (n : ℝ)) *
          (y * Real.sqrt d) * Real.sqrt (n : ℝ) := by ring
  have hproduct :
      Real.sqrt (d * (n : ℝ)) * (y * Real.sqrt d) < 10 * (s : ℝ) := by
    have hySqrtNonneg : 0 ≤ y * Real.sqrt d :=
      mul_nonneg hy (Real.sqrt_nonneg _)
    calc
      Real.sqrt (d * (n : ℝ)) * (y * Real.sqrt d) <
          (5 * (s : ℝ)) * (y * Real.sqrt d) :=
        mul_lt_mul_of_pos_right hsqrtDensity (mul_pos hyPos (Real.sqrt_pos.2 hd))
      _ ≤ (5 * (s : ℝ)) * 2 :=
        mul_le_mul_of_nonneg_left hySqrt (by positivity)
      _ = 10 * (s : ℝ) := by ring
  have hweight : chromaticWeight n c <
      (10000000000000000000 : ℝ) * s := by
    rw [chromaticWeight]
    have hdivide := (div_lt_div_iff_of_pos_right hsqrtN).2 hcx
    change (c : ℝ) * x / Real.sqrt (n : ℝ) <
      (10000000000000000000 : ℝ) * s
    calc
      (c : ℝ) * x / Real.sqrt (n : ℝ) <
          1000000000000000000 * d * (n : ℝ) * y /
            Real.sqrt (n : ℝ) := hdivide
      _ = 1000000000000000000 *
          (Real.sqrt (d * (n : ℝ)) * (y * Real.sqrt d)) := by
        rw [← hidentity]
        ring
      _ < 1000000000000000000 * (10 * (s : ℝ)) :=
        mul_lt_mul_of_pos_left hproduct (by norm_num)
      _ = 10000000000000000000 * (s : ℝ) := by ring
  have hconstant : (10000000000000000000 : ℝ) < erdos717Constant := by
    have hpow : (10000000000000000000 : ℝ) < (10 : ℝ) ^ (200 : ℕ) := by
      norm_num
    exact hpow.trans_le (by
      simp only [erdos717Constant]
      exact le_add_of_nonneg_right (by positivity))
  exact hweight.trans_le
    (mul_le_mul_of_nonneg_right hconstant.le (by positivity : (0 : ℝ) ≤ s))

/-- Combination of the dense potential, the sparse induction, and the
density fallback.  This is the complete Fox--Lee--Sudakov estimate for a
graph whose independence number is at most `100 n / c`. -/
theorem active_graph_weight_lt_forbidden_order
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (a c k : ℕ) (hind : G.indepNum ≤ a)
    (hnHuge : 10 ^ 100 ≤ Fintype.card V)
    (haHalf : 2 * a ≤ Fintype.card V)
    (ha : 0 < a) (hc : 0 < c)
    (hactive : (c : ℝ) * a < 100 * Fintype.card V)
    (hk : 2 ≤ k) (hnot : ¬Erdos718.ContainsCliqueSubdivision G k) :
    chromaticWeight (Fintype.card V) c <
      erdos717Constant * (k - 1) := by
  let n := Fintype.card V
  let m := G.edgeFinset.card
  let d : ℝ := (m : ℝ) / (n : ℝ) ^ 2
  let s := k - 1
  change chromaticWeight n c < erdos717Constant * ((k : ℝ) - 1)
  have hsCast : (s : ℝ) = (k : ℝ) - 1 := by
    dsimp only [s]
    rw [Nat.cast_sub (by omega : 1 ≤ k)]
    norm_num
  rw [← hsCast]
  have hn : 0 < n := lt_of_lt_of_le (by norm_num) hnHuge
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have haS : 1 ≤ s := by
    dsimp only [s]
    omega
  have hkEq : s + 1 = k := by
    dsimp only [s]
    omega
  have hm : 0 < m := by
    have hdom := card_le_indepBound_add_twice_edges G a hind
    by_contra hnotm
    have hm0 : m = 0 := Nat.eq_zero_of_not_pos hnotm
    change n ≤ a + 2 * m at hdom
    rw [hm0] at hdom
    change 2 * a ≤ n at haHalf
    omega
  have hd : 0 < d := by positivity
  have hlogn : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  by_cases hdLower : (1 / 10 ^ (20 : ℕ) : ℝ) ≤ d
  · have hpot := dense_graph_potential_lt_forbidden_order G a k hind
      (by simpa only [n] using hnHuge)
      (by simpa only [d, m, n] using hdLower)
      (by omega) hk hnot
    apply dense_active_weight_lt n a c s hn ha haS hlogn
      (by simpa only [n] using hactive)
    have hkCast : (s : ℝ) + 1 = (k : ℝ) := by exact_mod_cast hkEq
    rw [hkCast]
    simpa only [n] using hpot
  · have hdSmall : d ≤ 1 / 10 ^ (20 : ℕ) := le_of_not_ge hdLower
    by_cases hlogCondition :
        d * a * Real.log (1 / d) ≤
          Real.log (n : ℝ) / 10000000000000000
    · have hpot := sparse_graph_potential_lt_forbidden_order G a k hind
        (by simpa only [n] using haHalf)
        (by simpa only [d, m, n] using hdSmall)
        (by simpa only [d, m, n] using hlogCondition) hk hnot
      apply sparse_active_weight_lt n m a c s hn hm ha haS hlogn
        (by simpa only [n] using hactive)
        (by simpa only [d, m, n] using hlogCondition)
      have hkCast : (s : ℝ) + 1 = (k : ℝ) := by exact_mod_cast hkEq
      rw [hkCast]
      simpa only [n, m] using hpot
    · have hfailure : Real.log (n : ℝ) / 10000000000000000 <
          d * a * Real.log (1 / d) := lt_of_not_ge hlogCondition
      have hmDensity : m < 5 * (k * k) * n := by
        by_contra hlarge
        exact hnot
          (ThomasWollanMassed.containsCliqueSubdivision_of_five_mul_sq_mul_card_le_edges
            G k (by simpa only [n] using hn)
              (by simpa only [m, n] using Nat.le_of_not_gt hlarge))
      have hdensity : d * n < 20 * (s : ℝ) ^ 2 := by
        have hmDensityR : (m : ℝ) < 5 * ((k : ℝ) * k) * n := by
          exact_mod_cast hmDensity
        have hkS : (k : ℝ) ≤ 2 * s := by
          exact_mod_cast (show k ≤ 2 * s by omega)
        have hdn : d * n = (m : ℝ) / n := by
          dsimp only [d]
          field_simp
        rw [hdn]
        rw [div_lt_iff₀ hnR]
        have hcoef : 5 * ((k : ℝ) * k) ≤ 20 * (s : ℝ) ^ 2 := by
          nlinarith [sq_nonneg ((k : ℝ) - 2 * s)]
        exact hmDensityR.trans_le
          (mul_le_mul_of_nonneg_right hcoef hnR.le)
      exact sparse_log_failure_active_weight_lt n a c s d hn ha hc haS hd
        (hdSmall.trans (by norm_num))
        (by simpa only [n] using hactive)
        (by simpa only [n] using hfailure) hdensity

end Erdos717
