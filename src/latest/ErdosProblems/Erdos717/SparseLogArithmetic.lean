/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Elementary logarithmic inequalities used by the sparse high-density case. -/

import ErdosProblems.Erdos717.SparseDensity
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Stirling

open Function Set

namespace Erdos717

/-- The real-valued potential propagated by the sparse induction. -/
noncomputable def sparsePotential (n m a : ℕ) : ℝ :=
  let d := (m : ℝ) / (n : ℝ) ^ 2
  Real.exp (-1000) * d ^ 4 * Real.sqrt n *
    Real.exp (Real.log n / (1000000000000 * d * a))

theorem log_lt_hundred_of_le_ten_pow_ten {x : ℝ}
    (hx : 0 < x) (hupper : x ≤ 10 ^ (10 : ℕ)) :
    Real.log x < 100 := by
  have hlogx : Real.log x ≤ Real.log (10 ^ (10 : ℕ) : ℝ) :=
    Real.strictMonoOn_log.monotoneOn hx (by norm_num) hupper
  have hlogTen : Real.log (10 : ℝ) < 9 := by
    convert Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 10) using 1 <;>
      norm_num
  rw [Real.log_pow] at hlogx
  have hten : (10 : ℝ) * Real.log 10 < 90 := by nlinarith
  have : Real.log x < 90 := hlogx.trans_lt (by simpa using hten)
  linarith

/-- The standard entropy bound `choose(a,b) ≤ (e*a/b)^b`, recorded in the
logarithmic form actually consumed below. -/
theorem log_choose_le_mul_one_add_log_inv_density
    (a b : ℕ) (d : ℝ) (hb : 1 ≤ b) (hba : b ≤ a)
    (hd : 0 < d) (hpattern : 16 * d * a ≤ b) :
    Real.log (a.choose b : ℝ) ≤ (b : ℝ) * (1 + Real.log (1 / d)) := by
  have hchoosePos : (0 : ℝ) < a.choose b := by
    exact_mod_cast Nat.choose_pos hba
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have haR : (0 : ℝ) ≤ a := by positivity
  have hfactStirling := Stirling.le_factorial_stirling b
  have hsqrtOne : (1 : ℝ) ≤ Real.sqrt (2 * Real.pi * b) := by
    have hpi : (1 : ℝ) ≤ 2 * Real.pi * b := by
      have hp : 3 ≤ Real.pi := Real.pi_gt_three.le
      have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast hb
      have hmul := mul_le_mul_of_nonneg_right hp
        (show (0 : ℝ) ≤ 2 * b by positivity)
      nlinarith
    exact Real.one_le_sqrt.mpr hpi
  have hfact : ((b : ℝ) / Real.exp 1) ^ b ≤ (b.factorial : ℝ) := by
    calc
      ((b : ℝ) / Real.exp 1) ^ b ≤
          Real.sqrt (2 * Real.pi * b) * ((b : ℝ) / Real.exp 1) ^ b := by
            exact le_mul_of_one_le_left (by positivity) hsqrtOne
      _ ≤ (b.factorial : ℝ) := hfactStirling
  have hbasePos : 0 < (b : ℝ) / Real.exp 1 := div_pos hbR (Real.exp_pos _)
  have hchoose := Nat.choose_le_pow_div (α := ℝ) b a
  have hratio : (a : ℝ) ^ b / (b.factorial : ℝ) ≤
      ((Real.exp 1 * a) / b) ^ b := by
    calc
      (a : ℝ) ^ b / (b.factorial : ℝ) ≤
          (a : ℝ) ^ b / (((b : ℝ) / Real.exp 1) ^ b) := by
            exact div_le_div_of_nonneg_left (by positivity) (by positivity) hfact
      _ = ((Real.exp 1 * a) / b) ^ b := by
            rw [← div_pow]
            congr 1
            field_simp [ne_of_gt hbR, Real.exp_ne_zero]
            <;> ring
  have hchooseBound : (a.choose b : ℝ) ≤
      ((Real.exp 1 * a) / b) ^ b := hchoose.trans hratio
  have hpatternR : 16 * d * (a : ℝ) ≤ b := hpattern
  have hbaseBound : (Real.exp 1 * a) / b ≤ 1 / d := by
    apply (div_le_iff₀ hbR).2
    rw [one_div_mul_eq_div]
    apply (le_div_iff₀ hd).2
    have hexp : Real.exp 1 < 3 := Real.exp_one_lt_three
    have haPos : (0 : ℝ) < a := by
      exact_mod_cast (lt_of_lt_of_le hb hba)
    have hexpMul := mul_lt_mul_of_pos_right hexp (mul_pos haPos hd)
    nlinarith [hpatternR]
  have hbasePositive : 0 < (Real.exp 1 * a) / b := by
    have haPos : 0 < a := lt_of_lt_of_le hb hba
    positivity
  have hinvPos : 0 < 1 / d := by positivity
  have hpowBound : ((Real.exp 1 * a) / b) ^ b ≤ (1 / d) ^ b :=
    pow_le_pow_left₀ hbasePositive.le hbaseBound _
  have hlog : Real.log (a.choose b : ℝ) ≤ Real.log ((1 / d) ^ b) :=
    Real.strictMonoOn_log.monotoneOn hchoosePos
      (pow_pos (one_div_pos.mpr hd) _)
      (hchooseBound.trans hpowBound)
  rw [Real.log_pow] at hlog
  have haPos : (0 : ℝ) < a := by
    exact_mod_cast (lt_of_lt_of_le hb hba)
  have hdle : d ≤ 1 := by nlinarith [hpatternR, show (b : ℝ) ≤ a by exact_mod_cast hba]
  have hlogInv : 0 ≤ Real.log (1 / d) :=
    Real.log_nonneg (by
      rw [one_le_div₀ hd]
      exact hdle)
  nlinarith

theorem sparse_high_log_case_one
    {x y A B z : ℝ}
    (hx : 100 ≤ x) (hy : 1 ≤ y) (hA : 1 / 32 ≤ A)
    (hBone : 1 ≤ B)
    (hB : B ≤ 64 * A) (hAy : A * y ≤ x / 1000000)
    (h : x - y - 100 - B * (1 + y) < z) :
    x / 2 + x / (1000000000000 * A) - 4 * y - 1000 < z := by
  have hApos : 0 < A := lt_of_lt_of_le (by norm_num) hA
  have hx0 : 0 ≤ x := by linarith
  have hfrac : x / (1000000000000 * A) ≤ 32 * x / 1000000000000 := by
    rw [div_le_iff₀ (by positivity : 0 < 1000000000000 * A)]
    nlinarith
  have honeY : 1 + y ≤ 2 * y := by linarith
  have hBy : B * (1 + y) ≤ 128 * (A * y) := by
    calc
      B * (1 + y) ≤ B * (2 * y) := by
        have hB0 : 0 ≤ B := by linarith
        exact mul_le_mul_of_nonneg_left honeY hB0
      _ ≤ (64 * A) * (2 * y) := by
        exact mul_le_mul_of_nonneg_right hB (by positivity)
      _ = 128 * (A * y) := by ring
  have hBy' : B * (1 + y) ≤ 128 * (x / 1000000) :=
    hBy.trans (mul_le_mul_of_nonneg_left hAy (by norm_num))
  nlinarith

theorem sparse_high_log_case_two
    {x y A B z : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hA : 0 < A)
    (hBone : 1 ≤ B) (hB : B ≤ 64 * A)
    (h : B * x - 3 * B * y - 300 * B - 100 < (2 * B - 1) * z) :
    x / 2 + x / (1000000000000 * A) - 4 * y - 1000 < z := by
  have hcoef : 0 < 2 * B - 1 := by nlinarith
  have hfrac0 : 0 ≤ x / (1000000000000 * A) := by positivity
  have hBfrac : B * (x / (1000000000000 * A)) ≤ 64 * x / 1000000000000 := by
    rw [show B * (x / (1000000000000 * A)) =
      (B * x) / (1000000000000 * A) by ring]
    rw [div_le_iff₀ (by positivity : 0 < 1000000000000 * A)]
    nlinarith
  by_contra hn
  have hz : z ≤ x / 2 + x / (1000000000000 * A) - 4 * y - 1000 :=
    le_of_not_gt hn
  have hmul := mul_le_mul_of_nonneg_left hz hcoef.le
  have htwice : (2 * B - 1) * (x / (1000000000000 * A)) ≤
      128 * x / 1000000000000 := by
    nlinarith
  nlinarith

theorem sparsePotential_eq_exp_log
    (n m a : ℕ) (hn : 0 < n) (hm : 0 < m) (ha : 0 < a) :
    sparsePotential n m a =
      Real.exp (Real.log n / 2 +
        Real.log n /
          (1000000000000 * ((m : ℝ) / (n : ℝ) ^ 2) * a) -
        4 * Real.log (1 / ((m : ℝ) / (n : ℝ) ^ 2)) - 1000) := by
  let d : ℝ := (m : ℝ) / (n : ℝ) ^ 2
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hd : 0 < d := by positivity
  have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnR
  have hlogInv : Real.log (1 / d) = -Real.log d := by
    rw [one_div, Real.log_inv]
  have hpos : 0 < Real.exp (-1000) * d ^ 4 * Real.sqrt n *
      Real.exp (Real.log n / (1000000000000 * d * a)) := by positivity
  have hlogEq : Real.log (Real.exp (-1000) * d ^ 4 * Real.sqrt n *
      Real.exp (Real.log n / (1000000000000 * d * a))) =
      Real.log n / 2 + Real.log n / (1000000000000 * d * a) -
        4 * Real.log (1 / d) - 1000 := by
    rw [Real.log_mul
        (mul_ne_zero (mul_ne_zero (Real.exp_ne_zero _) (pow_ne_zero 4 hd.ne'))
          hsqrt.ne')
        (Real.exp_ne_zero _),
      Real.log_mul (mul_ne_zero (Real.exp_ne_zero _) (pow_ne_zero 4 hd.ne'))
        hsqrt.ne',
      Real.log_mul (Real.exp_ne_zero _) (pow_ne_zero 4 hd.ne'),
      Real.log_exp, Real.log_pow, Real.log_sqrt hnR.le, hlogInv]
    rw [Real.log_exp]
    ring
  simp only [sparsePotential, d]
  exact (Real.exp_log hpos).symm.trans (congrArg Real.exp hlogEq)

/-- Analytic extraction of the sparse potential from the two alternatives
produced by the canonical reservoir theorem. -/
theorem sparse_high_order_real
    (n a b k L cbin : ℕ) (d : ℝ)
    (hn : 0 < n) (ha : 0 < a) (hb : 1 ≤ b) (hk : 2 ≤ k)
    (hd : 0 < d) (hdsmall : d ≤ 1 / 10 ^ (20 : ℕ))
    (hA : 1 / 32 ≤ d * a) (hbupper : (b : ℝ) ≤ 64 * (d * a))
    (hlogn : 100 ≤ Real.log n)
    (hlogCondition : d * a * Real.log (1 / d) ≤ Real.log n / 1000000)
    (hcbin : cbin = a.choose b)
    (hpattern : 16 * d * a ≤ b)
    (hL : d ^ 2 * n < 10 ^ (10 : ℕ) * L)
    (hcases :
      d * n < 320000 * cbin * k ∨
      (L : ℝ) ^ (b - 1) * (d * n) <
        640000 * cbin * 38 ^ (b - 1) * k ^ (2 * b - 1)) :
    Real.exp (-1000) * d ^ 4 * Real.sqrt n *
        Real.exp (Real.log n / (1000000000000 * d * a)) < k := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hkR : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) hk)
  have hbinPosNat : 0 < cbin := by
    rw [hcbin]
    exact Nat.choose_pos (by
      have : (b : ℝ) ≤ a := by
        calc
          (b : ℝ) ≤ 64 * (d * a) := hbupper
          _ ≤ a := by
            have hd64 : 64 * d ≤ 1 := by
              have hpow : (10 : ℝ) ^ (20 : ℕ) ≥ 64 := by norm_num
              nlinarith
            nlinarith
      exact_mod_cast this)
  have hbinPos : (0 : ℝ) < cbin := by exact_mod_cast hbinPosNat
  have hdle : d ≤ 1 := hdsmall.trans (by norm_num)
  have hy : 1 ≤ Real.log (1 / d) := by
    have hdinv : (10 : ℝ) ^ (20 : ℕ) ≤ 1 / d := by
      rw [le_div_iff₀ hd]
      nlinarith
    have hlogMono : Real.log ((10 : ℝ) ^ (20 : ℕ)) ≤ Real.log (1 / d) :=
      Real.strictMonoOn_log.monotoneOn (by norm_num)
        (by exact one_div_pos.mpr hd) hdinv
    rw [Real.log_pow] at hlogMono
    have hlogTen : 1 < Real.log (10 : ℝ) := by
      rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 10)]
      exact Real.exp_one_lt_three.trans (by norm_num)
    nlinarith
  have hlogBin : Real.log (cbin : ℝ) ≤
      (b : ℝ) * (1 + Real.log (1 / d)) := by
    rw [hcbin]
    exact log_choose_le_mul_one_add_log_inv_density a b d hb
      (by
        have hbaR : (b : ℝ) ≤ a := by
          calc
            (b : ℝ) ≤ 64 * (d * a) := hbupper
            _ ≤ a := by
              have hd64 : 64 * d ≤ 1 := by
                have hpow : (10 : ℝ) ^ (20 : ℕ) ≥ 64 := by norm_num
                nlinarith
              nlinarith
        exact_mod_cast hbaR)
      hd hpattern
  have hlog320 : Real.log (320000 : ℝ) < 100 :=
    log_lt_hundred_of_le_ten_pow_ten (by norm_num) (by norm_num)
  have hlog640 : Real.log (640000 : ℝ) < 100 :=
    log_lt_hundred_of_le_ten_pow_ten (by norm_num) (by norm_num)
  have hlog38 : Real.log (38 : ℝ) < 100 := by
    have := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 38)
      (by norm_num : (38 : ℝ) ≠ 1)
    nlinarith
  have hlogTenPow : Real.log ((10 : ℝ) ^ (10 : ℕ)) < 100 :=
    log_lt_hundred_of_le_ten_pow_ten (by positivity) le_rfl
  have hlogd : Real.log d = -Real.log (1 / d) := by
    rw [one_div, Real.log_inv]
    ring
  have hLpos : (0 : ℝ) < L := by
    by_contra hnot
    have : (L : ℝ) = 0 := le_antisymm (le_of_not_gt hnot) (by positivity)
    rw [this, mul_zero] at hL
    have : 0 < d ^ 2 * (n : ℝ) := by positivity
    linarith
  have hlogL : Real.log n - 2 * Real.log (1 / d) - 100 <
      Real.log L := by
    have hlogIneq := Real.strictMonoOn_log
      (by positivity : 0 < d ^ 2 * (n : ℝ))
      (by positivity : 0 < (10 : ℝ) ^ (10 : ℕ) * L) hL
    rw [Real.log_mul (pow_ne_zero 2 hd.ne') hnR.ne', Real.log_pow,
      Real.log_mul (by positivity : (10 : ℝ) ^ (10 : ℕ) ≠ 0) hLpos.ne',
      hlogd] at hlogIneq
    norm_num at hlogIneq
    norm_num at hlogTenPow
    nlinarith
  have htargetLog : Real.log n / 2 +
      Real.log n / (1000000000000 * (d * a)) -
      4 * Real.log (1 / d) - 1000 < Real.log k := by
    rcases hcases with hcase | hcase
    · have hlogCase := Real.strictMonoOn_log
          (by positivity : 0 < d * (n : ℝ))
          (by positivity : 0 < (320000 : ℝ) * cbin * k) hcase
      rw [Real.log_mul hd.ne' hnR.ne',
        Real.log_mul
          (mul_ne_zero (by norm_num : (320000 : ℝ) ≠ 0) hbinPos.ne') hkR.ne',
        Real.log_mul (by norm_num : (320000 : ℝ) ≠ 0) hbinPos.ne',
        hlogd] at hlogCase
      apply sparse_high_log_case_one hlogn hy hA (by exact_mod_cast hb)
        hbupper hlogCondition
      nlinarith
    · have hlogCase := Real.strictMonoOn_log
          (mul_pos (pow_pos hLpos _) (mul_pos hd hnR))
          (by positivity :
            0 < (640000 : ℝ) * cbin * 38 ^ (b - 1) * k ^ (2 * b - 1))
          hcase
      rw [Real.log_mul (pow_ne_zero _ hLpos.ne') (mul_ne_zero hd.ne' hnR.ne'),
        Real.log_pow, Real.log_mul hd.ne' hnR.ne',
        Real.log_mul
          (mul_ne_zero (mul_ne_zero (by norm_num : (640000 : ℝ) ≠ 0) hbinPos.ne')
            (pow_ne_zero _ (by norm_num : (38 : ℝ) ≠ 0)))
          (pow_ne_zero _ hkR.ne'),
        Real.log_mul
          (mul_ne_zero (by norm_num : (640000 : ℝ) ≠ 0) hbinPos.ne')
          (pow_ne_zero _ (by norm_num : (38 : ℝ) ≠ 0)),
        Real.log_mul (by norm_num : (640000 : ℝ) ≠ 0) hbinPos.ne',
        Real.log_pow, Real.log_pow, hlogd] at hlogCase
      norm_num [Nat.cast_sub hb,
        Nat.cast_sub (by omega : 1 ≤ 2 * b)] at hlogCase
      apply sparse_high_log_case_two (by positivity) (by positivity)
        (lt_of_lt_of_le (by norm_num) hA) (by exact_mod_cast hb) hbupper
      have hbsub : (0 : ℝ) ≤ b - 1 := by
        have hbRone : (1 : ℝ) ≤ b := by exact_mod_cast hb
        linarith
      have hscaled := mul_le_mul_of_nonneg_left hlogL.le hbsub
      nlinarith
  have hpotentialEq : Real.exp (-1000) * d ^ 4 * Real.sqrt n *
      Real.exp (Real.log n / (1000000000000 * d * a)) =
      Real.exp (Real.log n / 2 + Real.log n / (1000000000000 * (d * a)) -
        4 * Real.log (1 / d) - 1000) := by
    have hlogInv : Real.log (1 / d) = -Real.log d := by
      rw [one_div, Real.log_inv]
    have hpos : 0 < Real.exp (-1000) * d ^ 4 * Real.sqrt n *
        Real.exp (Real.log n / (1000000000000 * d * a)) := by positivity
    have hlogEq : Real.log (Real.exp (-1000) * d ^ 4 * Real.sqrt n *
        Real.exp (Real.log n / (1000000000000 * d * a))) =
        Real.log n / 2 + Real.log n / (1000000000000 * (d * a)) -
          4 * Real.log (1 / d) - 1000 := by
      rw [Real.log_mul
          (mul_ne_zero
            (mul_ne_zero (Real.exp_ne_zero _) (pow_ne_zero 4 hd.ne'))
            (Real.sqrt_pos.2 hnR).ne')
          (Real.exp_ne_zero _),
        Real.log_mul
          (mul_ne_zero (Real.exp_ne_zero _) (pow_ne_zero 4 hd.ne'))
          (Real.sqrt_pos.2 hnR).ne',
        Real.log_mul (Real.exp_ne_zero _) (pow_ne_zero 4 hd.ne'),
        Real.log_exp, Real.log_pow, Real.log_sqrt hnR.le, hlogInv]
      rw [Real.log_exp]
      ring
    exact (Real.exp_log hpos).symm.trans (congrArg Real.exp hlogEq)
  rw [hpotentialEq]
  exact (Real.exp_lt_exp.mpr htargetLog).trans_eq (Real.exp_log hkR)

end Erdos717
