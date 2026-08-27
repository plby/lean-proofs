import Arxiv.Arxiv2411_18291.PaperParameterMargins

/-!
# The explicit numerical inequality singled out in Section 10

This verifies the printed threshold's domination of the flattening input
coefficient. It is a scalar inequality, not a proof of the false
multiplicity-two conclusion or a certification of every construction threshold.
-/

namespace Arxiv2411_18291

theorem paper_colour_constant_bound {q : ℕ} (hq : 2 ≤ q) :
    2160 * q ^ 2 ≤ (4 * q) ^ 5 := by
  have hq3 : 8 ≤ q ^ 3 := Nat.pow_le_pow_left hq 3
  have hc : 2160 ≤ 1024 * q ^ 3 := by omega
  calc
    _ ≤ (1024 * q ^ 3) * q ^ 2 := Nat.mul_le_mul_right _ hc
    _ = _ := by ring

theorem paper_binomial_coefficient_bound {q : ℕ} (hq : 2 ≤ q) (r : ℕ) :
    2 ^ (5 * q) * (q.choose r) ^ 4 ≤ (4 * q) ^ (3 * q) := by
  calc
    _ ≤ 2 ^ (5 * q) * (2 ^ q) ^ 4 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.choose_le_two_pow q r) 4)
    _ = (2 ^ 3) ^ (3 * q) := by
      rw [← pow_mul, ← pow_add, ← pow_mul]
      congr 1
      omega
    _ ≤ _ := Nat.pow_le_pow_left (by norm_num; omega : 2 ^ 3 ≤ 4 * q) _

theorem paper_geometric_coefficient_bound {q r : ℕ} (hqr : r < q) :
    (4 * q) ^ r * (2 * q) ^ (2 * r) ≤ (4 * q) ^ (3 * q) := by
  calc
    _ ≤ (4 * q) ^ r * (4 * q) ^ (2 * r) :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega : 2 * q ≤ 4 * q) _)
    _ = (4 * q) ^ (3 * r) := by rw [← pow_add]; congr 1; omega
    _ ≤ _ := Nat.pow_le_pow_right (by omega : 0 < 4 * q) (by omega)

theorem paper_flattening_coefficient_le {q r M : ℕ} (hr : 1 ≤ r) (hqr : r < q)
    (hM : M ≤ 3 * (2 * q) ^ r * (q.choose r) ^ 2) :
    2 ^ (5 * q) * (4 * q) ^ r * paperColourCount q r M ≤ (4 * q) ^ (6 * q + 5) := by
  have hq : 2 ≤ q := by omega
  calc
    _ ≤ 2 ^ (5 * q) * (4 * q) ^ r *
        (2160 * q ^ 2 * (2 * q) ^ (2 * r) * (q.choose r) ^ 4) :=
      Nat.mul_le_mul_left _ (paperColourCount_bound q r M hM)
    _ = (2160 * q ^ 2) * (2 ^ (5 * q) * (q.choose r) ^ 4) *
        ((4 * q) ^ r * (2 * q) ^ (2 * r)) := by ring
    _ ≤ (4 * q) ^ 5 * (4 * q) ^ (3 * q) * (4 * q) ^ (3 * q) :=
      Nat.mul_le_mul (Nat.mul_le_mul (paper_colour_constant_bound hq)
        (paper_binomial_coefficient_bound hq r)) (paper_geometric_coefficient_bound hqr)
    _ = _ := by rw [← pow_add, ← pow_add]; congr 1; omega

theorem paper_flattening_threshold_nat {q r M : ℕ} (hr : 1 ≤ r) (hqr : r < q)
    (hM : M ≤ 3 * (2 * q) ^ r * (q.choose r) ^ 2) :
    (2 ^ (5 * q) * (4 * q) ^ r * paperColourCount q r M) ^
        (10 * paperInverseAlpha q r) < paperSizeThreshold q r := by
  have hshort : (6 * q + 5) * 10 < 90 * q := by omega
  have hexp : (6 * q + 5) * (10 * paperInverseAlpha q r) <
      90 * q * paperInverseAlpha q r := by
    rw [show (6 * q + 5) * (10 * paperInverseAlpha q r) =
      ((6 * q + 5) * 10) * paperInverseAlpha q r by ring]
    exact Nat.mul_lt_mul_of_pos_right hshort (paperInverseAlpha_pos hqr)
  calc
    _ ≤ ((4 * q) ^ (6 * q + 5)) ^ (10 * paperInverseAlpha q r) :=
      Nat.pow_le_pow_left (paper_flattening_coefficient_le hr hqr hM) _
    _ = (4 * q) ^ ((6 * q + 5) * (10 * paperInverseAlpha q r)) := (pow_mul _ _ _).symm
    _ < _ := Nat.pow_lt_pow_right (by omega : 1 < 4 * q) hexp

theorem paper_flattening_threshold_real {q r M : ℕ} (hr : 1 ≤ r) (hqr : r < q)
    (hM : M ≤ 3 * (2 * q) ^ r * (q.choose r) ^ 2) :
    ((2 : ℝ) ^ (5 * q) * (4 * q : ℝ) ^ r * paperColourCount q r M) ^
        (10 / paperAlpha q r) < (paperSizeThreshold q r : ℝ) := by
  have hexp : 10 / paperAlpha q r = (10 * paperInverseAlpha q r : ℕ) := by
    apply (div_eq_iff (paperAlpha_pos hqr).ne').mpr
    push_cast
    calc
      10 = 10 * (paperAlpha q r * paperInverseAlpha q r) := by
        rw [paperAlpha_mul_inverse hqr, mul_one]
      _ = _ := by ring
  rw [hexp, Real.rpow_natCast]
  exact_mod_cast paper_flattening_threshold_nat hr hqr hM

end Arxiv2411_18291
