import ErdosProblems.Erdos788.ShortLinearCode
import ErdosProblems.Erdos788.TrevisanParameters

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Explicit logarithmic bound for the short-code coordinate length
-/

namespace Erdos788

/-- At the reconstruction value `η = 1/(40pr)`, the binary coordinate length
is at most an explicit constant times `log(pr)`. -/
theorem shortLinearCode_ell_lt_log_mul
    {p r : ℕ} [Fact p.Prime]
    (hp : 2 < p) (hr : 0 < r)
    (C : ShortLinearCode p (2 * r) (trevisanEta p r)) :
    (C.ell : ℝ) < 100 * Real.log ((p * r : ℕ) : ℝ) := by
  have hpR : (1 : ℝ) < p := by exact_mod_cast (show 1 < p by omega)
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hr1R : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hlogp : 0 < Real.log (p : ℝ) := Real.log_pos hpR
  have heta :
      9 * (2 * r : ℝ) * Real.log p / trevisanEta p r ^ 4 =
        46080000 * (p : ℝ) ^ 4 * (r : ℝ) ^ 5 * Real.log p := by
    rw [trevisanEta]
    field_simp
    ring
  have hlength : (2 ^ C.ell : ℝ) <
      50000000 * (p : ℝ) ^ 4 * (r : ℝ) ^ 5 * Real.log p := by
    calc
      (2 ^ C.ell : ℝ) <
          9 * (2 * r : ℝ) * Real.log p / trevisanEta p r ^ 4 := by
            simpa only [Nat.cast_mul, Nat.cast_ofNat] using! C.length_lt
      _ = 46080000 * (p : ℝ) ^ 4 * (r : ℝ) ^ 5 * Real.log p := heta
      _ ≤ 50000000 * (p : ℝ) ^ 4 * (r : ℝ) ^ 5 * Real.log p := by
        have : 0 ≤ (p : ℝ) ^ 4 * (r : ℝ) ^ 5 * Real.log p := by positivity
        nlinarith
  have hlog := Real.log_lt_log
    (by positivity : (0 : ℝ) < (2 : ℝ) ^ C.ell) hlength
  have hlogExpand :
      Real.log
          (50000000 * (p : ℝ) ^ 4 * (r : ℝ) ^ 5 * Real.log p) =
        Real.log 50000000 + 4 * Real.log p +
          5 * Real.log r + Real.log (Real.log p) := by
    calc
      Real.log
          (((50000000 : ℝ) * p ^ 4 * r ^ 5) * Real.log p) =
          Real.log ((50000000 : ℝ) * p ^ 4 * r ^ 5) +
            Real.log (Real.log p) := by
              rw [Real.log_mul (by positivity) (by positivity)]
      _ = (Real.log ((50000000 : ℝ) * p ^ 4) + Real.log (r ^ 5)) +
            Real.log (Real.log p) := by
              rw [Real.log_mul (by positivity) (by positivity)]
      _ = ((Real.log 50000000 + Real.log (p ^ 4)) + Real.log (r ^ 5)) +
            Real.log (Real.log p) := by
              rw [Real.log_mul (by positivity) (by positivity)]
      _ = Real.log 50000000 + 4 * Real.log p +
          5 * Real.log r + Real.log (Real.log p) := by
            rw [Real.log_pow, Real.log_pow]
            ring
  rw [Real.log_pow, hlogExpand] at hlog
  have hconstNat : 50000000 ≤ 2 ^ 26 := by norm_num
  have hconstR : (50000000 : ℝ) ≤ (2 : ℝ) ^ 26 := by
    exact_mod_cast hconstNat
  have hconst : Real.log 50000000 ≤ 26 * Real.log 2 := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 50000000) hconstR
    simpa [Real.log_pow] using! h
  have hp_le_pr : p ≤ p * r := by
    simpa [mul_comm] using! Nat.mul_le_mul_left p (show 1 ≤ r by omega)
  have hr_le_pr : r ≤ p * r := by
    exact Nat.le_mul_of_pos_left r (show 0 < p by omega)
  have hlogp_le : Real.log (p : ℝ) ≤ Real.log (p * r : ℕ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hp_le_pr
  have hlogr_le : Real.log (r : ℝ) ≤ Real.log (p * r : ℕ) := by
    apply Real.log_le_log hrR
    exact_mod_cast hr_le_pr
  have hloglogp_le : Real.log (Real.log p) ≤ Real.log p := by
    have h := Real.log_le_sub_one_of_pos hlogp
    linarith
  have htwo_le_pr : 2 ≤ p * r := by
    have : 3 ≤ p := by omega
    nlinarith [show 1 ≤ r by omega]
  have hlogtwo_le : Real.log 2 ≤ Real.log (p * r : ℕ) := by
    apply Real.log_le_log (by norm_num)
    exact_mod_cast htwo_le_pr
  have hlogpr : 0 ≤ Real.log (p * r : ℕ) :=
    (Real.log_pos (by exact_mod_cast (show 1 < p * r by omega))).le
  have h36 :
      Real.log 50000000 + 4 * Real.log p +
          5 * Real.log r + Real.log (Real.log p) ≤
        36 * Real.log (p * r : ℕ) := by
    nlinarith
  have hell36 : (C.ell : ℝ) * Real.log 2 <
      36 * Real.log (p * r : ℕ) := hlog.trans_le h36
  have hlogtwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hcoef : (36 : ℝ) ≤ 100 * Real.log 2 := by
    nlinarith [Real.log_two_gt_d9]
  have hell100 : (C.ell : ℝ) * Real.log 2 <
      Real.log 2 * (100 * Real.log (p * r : ℕ)) := by
    calc
      (C.ell : ℝ) * Real.log 2 < 36 * Real.log (p * r : ℕ) := hell36
      _ ≤ Real.log 2 * (100 * Real.log (p * r : ℕ)) := by
        nlinarith
  nlinarith

end Erdos788
