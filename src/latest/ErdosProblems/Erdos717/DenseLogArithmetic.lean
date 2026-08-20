/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Real estimates for the dense-reservoir alternative. -/

import ErdosProblems.Erdos717.DenseStep
import ErdosProblems.Erdos717.SparseLogArithmetic

open Function Set

namespace Erdos717

/-- A deliberately slack dense potential. -/
noncomputable def densePotential (n a : ℕ) : ℝ :=
  Real.exp (Real.log n / 2 + Real.log n / (8 * a) - 5000)

/-- The natural-number dense reservoir alternative implies that the dense
potential lies below the forbidden subdivision order. -/
theorem densePotential_lt_of_reservoir_alternative
    (n a k L Q : ℕ) (hn : 0 < n) (ha : 1 ≤ a) (hk : 2 ≤ k)
    (hL : 1 ≤ L) (hQ : 1 ≤ Q)
    (hlogn : 100 ≤ Real.log (n : ℝ))
    (hlogL : Real.log (n : ℝ) - 3000 ≤ Real.log (L : ℝ))
    (hlogQ : Real.log (n : ℝ) - 400 ≤ Real.log (Q : ℝ))
    (hcases : Q < k ∨
      L ^ (a - 1) * Q < 38 ^ (a - 1) * k ^ (2 * a - 1)) :
    densePotential n a < k := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have haR : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have haPos : (0 : ℝ) < a := lt_of_lt_of_le (by norm_num) haR
  have hkR : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) hk)
  have hLR : (0 : ℝ) < L := by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 1) hL)
  have hQR : (0 : ℝ) < Q := by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 1) hQ)
  let x := Real.log (n : ℝ)
  have hx : 100 ≤ x := by simpa only [x] using hlogn
  have hx0 : 0 ≤ x := by linarith
  have hfrac : x / (8 * (a : ℝ)) ≤ x / 8 := by
    rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 8 * a)
      (by norm_num : (0 : ℝ) < 8)]
    nlinarith
  rcases hcases with hQk | hpower
  · have hQkR : (Q : ℝ) < k := by exact_mod_cast hQk
    have hlogQk := Real.strictMonoOn_log hQR hkR hQkR
    have hexponent : x / 2 + x / (8 * (a : ℝ)) - 5000 <
        Real.log (k : ℝ) := by
      have hlower : x - 400 ≤ Real.log (Q : ℝ) := by
        simpa only [x] using hlogQ
      nlinarith
    rw [densePotential]
    exact (Real.lt_log_iff_exp_lt hkR).mp (by simpa only [x] using hexponent)
  · have hpowerR :
        (L : ℝ) ^ (a - 1) * Q <
          38 ^ (a - 1) * (k : ℝ) ^ (2 * a - 1) := by
      exact_mod_cast hpower
    have hleftPos : (0 : ℝ) < (L : ℝ) ^ (a - 1) * Q := by positivity
    have hrightPos : (0 : ℝ) <
        38 ^ (a - 1) * (k : ℝ) ^ (2 * a - 1) := by positivity
    have hlogPower := Real.strictMonoOn_log hleftPos hrightPos hpowerR
    rw [Real.log_mul (pow_ne_zero _ hLR.ne') hQR.ne',
      Real.log_mul (pow_ne_zero _ (by norm_num : (38 : ℝ) ≠ 0))
        (pow_ne_zero _ hkR.ne'),
      Real.log_pow, Real.log_pow, Real.log_pow] at hlogPower
    have htwoa : 1 ≤ 2 * a := by omega
    norm_num only [Nat.cast_sub ha, Nat.cast_sub htwoa, Nat.cast_mul,
      Nat.cast_one, Nat.cast_ofNat] at hlogPower
    have hlog38 : Real.log (38 : ℝ) < 37 := by
      convert Real.log_lt_sub_one_of_pos
        (by norm_num : (0 : ℝ) < 38) (by norm_num : (38 : ℝ) ≠ 1) using 1 <;>
        norm_num
    have hLlower : x - 3000 ≤ Real.log (L : ℝ) := by
      simpa only [x] using hlogL
    have hQlower : x - 400 ≤ Real.log (Q : ℝ) := by
      simpa only [x] using hlogQ
    have hfracScaled : ((2 : ℝ) * a - 1) * (x / (8 * a)) ≤ x / 4 := by
      calc
        ((2 : ℝ) * a - 1) * (x / (8 * a)) ≤
            (2 * a) * (x / (8 * a)) :=
          mul_le_mul_of_nonneg_right (by linarith)
            (div_nonneg hx0 (by positivity))
        _ = x / 4 := by field_simp; ring
    have haMinus : (0 : ℝ) ≤ a - 1 := by linarith
    have hleftLower :
        (a - 1) * (x - 3000) + (x - 400) ≤
          (a - 1) * Real.log (L : ℝ) + Real.log (Q : ℝ) :=
      add_le_add (mul_le_mul_of_nonneg_left hLlower haMinus) hQlower
    have hrightUpper :
        (a - 1) * Real.log (38 : ℝ) +
            (2 * a - 1) * Real.log (k : ℝ) ≤
          (a - 1) * 37 + (2 * a - 1) * Real.log (k : ℝ) :=
      add_le_add (mul_le_mul_of_nonneg_left hlog38.le haMinus) le_rfl
    have hkey :
        (a - 1) * (x - 3000) + (x - 400) <
          (a - 1) * 37 + (2 * a - 1) * Real.log (k : ℝ) :=
      lt_of_le_of_lt hleftLower (hlogPower.trans_le hrightUpper)
    have htargetUpper :
        ((2 : ℝ) * a - 1) * (x / 2 + x / (8 * a) - 5000) ≤
          (a - 1) * (x - 3000) + (x - 400) - (a - 1) * 37 := by
      nlinarith
    have hscaled : ((2 : ℝ) * a - 1) *
        (x / 2 + x / (8 * a) - 5000) <
          ((2 : ℝ) * a - 1) * Real.log (k : ℝ) := by
      linarith
    have hcoef : (0 : ℝ) < 2 * a - 1 := by nlinarith
    have hexponent : x / 2 + x / (8 * a) - 5000 <
        Real.log (k : ℝ) := by nlinarith
    rw [densePotential]
    exact (Real.lt_log_iff_exp_lt hkR).mp (by simpa only [x] using hexponent)

end Erdos717
