import ErdosProblems.Erdos633.EulerProducts

/-!
# Rational points on the two Euler cubics

Clearing a reduced denominator produces a square integer. The sign of the
shifted numerator follows from positivity of the quadratic factor, so the
zero and positive cases exhaust all rational points.
-/

namespace Erdos633

theorem rational_cubic_numerator_square (x y : ℚ) (ε : ℤ)
    (h : y ^ 2 = x ^ 3 + (ε : ℚ)) :
    IsSquare ((x.den : ℤ) * (x.num ^ 3 + ε * (x.den : ℤ) ^ 3)) := by
  apply Rat.isSquare_intCast_iff.mp
  refine ⟨y * (x.den : ℚ) ^ 2, ?_⟩
  push_cast
  have hn : (x.den : ℚ) ≠ 0 := by exact_mod_cast x.den_ne_zero
  have hx : (x.num : ℚ) = x * x.den := (div_eq_iff hn).mp x.num_div_den
  rw [hx]
  linear_combination -(x.den : ℚ) ^ 4 * h

theorem euler_product_first_nonneg (ε c n : ℤ) (hε : ε ^ 2 = 1) (hn : 0 < n)
    (hsq : IsSquare (c * n * eulerQuadratic ε c n)) : 0 ≤ c := by
  apply nonneg_of_mul_nonneg_left (b := n * eulerQuadratic ε c n)
  · simpa only [mul_assoc] using hsq.nonneg
  · exact mul_pos hn (eulerQuadratic_pos ε c n hε hn)

theorem euler_rational_cubic_add_one (x y : ℚ) (h : y ^ 2 = x ^ 3 + 1) :
    x = -1 ∨ x = 0 ∨ x = 2 := by
  let m : ℤ := x.num
  let n : ℤ := x.den
  have hn : 0 < n := by dsimp [n]; exact_mod_cast x.den_pos
  have hn0 : (n : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt hn
  have hmn : IsCoprime m n := Int.isCoprime_iff_gcd_eq_one.mpr x.reduced
  have hx : (m : ℚ) / (n : ℚ) = x := by
    simpa only [m, n, Int.cast_natCast] using x.num_div_den
  have hcn : IsCoprime (m + n) n := by
    simpa only [one_mul] using hmn.add_mul_right_left 1
  have hsq : IsSquare ((m + n) * n * eulerQuadratic (-1) (m + n) n) := by
    rw [show (m + n) * n * eulerQuadratic (-1) (m + n) n =
      n * (m ^ 3 + n ^ 3) by dsimp [eulerQuadratic]; ring]
    simpa only [Int.cast_one, one_mul] using rational_cubic_numerator_square x y 1 h
  have hc := euler_product_first_nonneg (-1) (m + n) n (by norm_num) hn hsq
  by_cases hc0 : m + n = 0
  · left
    have hm : m = -n := by omega
    calc
      x = (m : ℚ) / (n : ℚ) := hx.symm
      _ = -1 := by rw [hm, Int.cast_neg]; field_simp
  · have hcpos : 0 < m + n := lt_of_le_of_ne hc (Ne.symm hc0)
    rcases euler_minus_product_cases (m + n) n hcpos hn hcn hsq with ⟨hc1, hn1⟩ | ⟨hc3, hn1⟩
    · right; left
      have hm : m = 0 := by omega
      calc
        x = (m : ℚ) / (n : ℚ) := hx.symm
        _ = 0 := by rw [hm]; norm_num
    · right; right
      have hm : m = 2 := by omega
      calc
        x = (m : ℚ) / (n : ℚ) := hx.symm
        _ = 2 := by rw [hm, hn1]; norm_num

theorem euler_rational_cubic_sub_one (x y : ℚ) (h : y ^ 2 = x ^ 3 - 1) :
    x = 1 ∧ y = 0 := by
  let m : ℤ := x.num
  let n : ℤ := x.den
  have hn : 0 < n := by dsimp [n]; exact_mod_cast x.den_pos
  have hn0 : (n : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt hn
  have hmn : IsCoprime m n := Int.isCoprime_iff_gcd_eq_one.mpr x.reduced
  have hx : (m : ℚ) / (n : ℚ) = x := by
    simpa only [m, n, Int.cast_natCast] using x.num_div_den
  have hcn : IsCoprime (m - n) n := by
    simpa only [neg_one_mul, sub_eq_add_neg] using hmn.add_mul_right_left (-1)
  have hsq : IsSquare ((m - n) * n * eulerQuadratic 1 (m - n) n) := by
    rw [show (m - n) * n * eulerQuadratic 1 (m - n) n =
      n * (m ^ 3 - n ^ 3) by dsimp [eulerQuadratic]; ring]
    simpa only [Int.cast_neg, Int.cast_one, neg_one_mul, sub_eq_add_neg] using
      rational_cubic_numerator_square x y (-1) (by simpa [sub_eq_add_neg] using h)
  have hc := euler_product_first_nonneg 1 (m - n) n (by norm_num) hn hsq
  have hc0 : m - n = 0 := by
    by_contra hne
    exact euler_plus_product_impossible (m - n) n (lt_of_le_of_ne hc (Ne.symm hne)) hn hcn hsq
  have hm : m = n := by omega
  have hx1 : x = 1 := by
    calc
      x = (m : ℚ) / (n : ℚ) := hx.symm
      _ = 1 := by rw [hm]; exact div_self hn0
  refine ⟨hx1, ?_⟩
  have hy : y ^ 2 = 0 := by simpa only [hx1, one_pow, sub_self] using h
  exact (sq_eq_zero_iff).mp hy

theorem rational_cubic_add_one_no_unit_interval (x y : ℚ)
    (hx0 : 0 < x) (hx1 : x < 1) (h : y ^ 2 = x ^ 3 + 1) : False := by
  rcases euler_rational_cubic_add_one x y h with h | h | h <;> linarith

end Erdos633
