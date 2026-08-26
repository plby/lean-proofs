import ErdosProblems.Erdos633b.GroupTwoSixtyAlgebra

/-! Exact rational eliminations for cases (5), (6), and (8), once their
actual perimeter equations and shared-angle area counts have been proved. -/

namespace Erdos633b

theorem caseEight_rational_pair_of_perimeter_area {x y k : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hk : 0 < k) (hconic : x ^ 2 + x * y + y ^ 2 = 1) (M L : ℤ) (hMp : 0 < M) (hLp : 0 < L)
    (hM : (M : ℝ) * (1 + x - y) = (k * y) * (2 * x + y - 1))
    (hL : (L : ℝ) * (1 - x + y) = (k * y) * (2 * x + y + 1)) (n : ℕ)
    (harea : (n : ℝ) = k ^ 2 * (2 * x + y) * (x + y)) :
    IsRational x ∧ IsRational y := by
  obtain ⟨hxr, K, hKr, hK⟩ := groupTwoSixty_rational_parameters hx hy hconic M L hMp hLp hM hL
  have hkK : k = K := mul_right_cancel₀ hy.ne' hK
  have hkr : IsRational k := hkK ▸ hKr
  have he : y = ((n : ℝ) / k ^ 2 - 1 - x ^ 2) / (2 * x) := by
    apply (eq_div_iff (mul_ne_zero (by norm_num) hx.ne')).mpr
    apply (eq_sub_iff_add_eq).mpr
    apply (eq_sub_iff_add_eq).mpr
    apply (eq_div_iff (pow_ne_zero 2 hk.ne')).mpr
    linear_combination -harea - k ^ 2 * hconic
  refine ⟨hxr, ?_⟩
  rw [he]
  have hk2 : IsRational (k ^ 2) := by simpa only [pow_two] using hkr.mul hkr
  have hx2 : IsRational (x ^ 2) := by simpa only [pow_two] using hxr.mul hxr
  exact ((((IsRational.natCast n).div hk2).sub
    (show IsRational (1 : ℝ) from ⟨1, by norm_num⟩)).sub hx2).div
      ((show IsRational (2 : ℝ) from ⟨2, by norm_num⟩).mul hxr)

theorem caseFive_rational_pair_of_perimeter_area {x y k : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hk : 0 < k) (hconic : x ^ 2 + x * y + y ^ 2 = 1) (M L : ℤ)
    (hM : (M : ℝ) * (1 + x - y) = k * (3 * x ^ 2 + x + 2 * y - 2))
    (hL : (L : ℝ) * (1 - x + y) = k * (-3 * x ^ 2 + x + 2 * y + 2)) (n : ℕ)
    (harea : (n : ℝ) = 3 * k ^ 2 * (x + 2 * y) * (x + y)) :
    IsRational x ∧ IsRational y := by
  have hx1 : x < 1 := by nlinarith [sq_nonneg y, mul_pos hx hy]
  have hy1 : y < 1 := by nlinarith [sq_nonneg x, mul_pos hx hy]
  have hp : 0 < 1 + x - y := by linarith
  have hm : 0 < 1 - x + y := by linarith
  let t := 2 * x + y
  have ht : 0 < t := by dsimp [t]; positivity
  have hM' : (M : ℝ) = k * (t - 1) := by
    apply mul_right_cancel₀ hp.ne'
    dsimp only [t]
    linear_combination hM + k * hconic
  have hL' : (L : ℝ) = k * (t + 1) := by
    apply mul_right_cancel₀ hm.ne'
    dsimp only [t]
    linear_combination hL - k * hconic
  have hkr : IsRational k := by
    refine ⟨((L : ℚ) - M) / 2, ?_⟩
    push_cast
    linarith [hM', hL']
  have hden : (0 : ℝ) < (L : ℝ) - M := by linarith [hM', hL']
  have htr : IsRational t := by
    refine ⟨((L : ℚ) + M) / ((L : ℚ) - M), ?_⟩
    push_cast
    apply (div_eq_iff hden.ne').mpr
    nlinarith [hM', hL']
  have he : y = ((n : ℝ) / (3 * k ^ 2) - 1) / t := by
    apply (eq_div_iff ht.ne').mpr
    apply (eq_sub_iff_add_eq).mpr
    apply (eq_div_iff (mul_ne_zero (by norm_num) (pow_ne_zero 2 hk.ne'))).mpr
    dsimp only [t]
    linear_combination -harea - 3 * k ^ 2 * hconic
  have hk2 : IsRational (k ^ 2) := by simpa only [pow_two] using hkr.mul hkr
  have hyr : IsRational y := by
    rw [he]
    exact (((IsRational.natCast n).div
      ((show IsRational (3 : ℝ) from ⟨3, by norm_num⟩).mul hk2)).sub
        (show IsRational (1 : ℝ) from ⟨1, by norm_num⟩)).div htr
  refine ⟨?_, hyr⟩
  have hx' : x = (t - y) / 2 := by dsimp [t]; ring
  rw [hx']
  exact (htr.sub hyr).div (show IsRational (2 : ℝ) from ⟨2, by norm_num⟩)

theorem caseSix_rational_parameter_of_perimeter_area {s k : ℝ}
    (hs : 0 < s) (hs1 : s < 1) (hk : 0 < k) (M L : ℤ) (hMp : 0 < M) (hLp : 0 < L)
    (htwin : (M : ℝ) * (2 + s - s ^ 2) = (L : ℝ) * (2 - s - s ^ 2))
    (hM : (M : ℝ) = k * (1 - s) * (2 + s)) (n : ℕ)
    (harea : (n : ℝ) = k ^ 2 * (2 - s ^ 2) * (3 - s ^ 2)) : IsRational s := by
  let r := s / (2 - s ^ 2)
  have hd : 0 < 2 - s ^ 2 := by nlinarith
  have hr : 0 < r := div_pos hs hd
  have hr1 : r < 1 := by
    apply (div_lt_one hd).mpr
    nlinarith
  have hMr : (0 : ℝ) < M := by exact_mod_cast hMp
  have hLr : (0 : ℝ) < L := by exact_mod_cast hLp
  have hden : (0 : ℝ) < (L : ℝ) + M := by positivity
  have hrr : IsRational r := by
    refine ⟨((L : ℚ) - M) / ((L : ℚ) + M), ?_⟩
    push_cast
    dsimp only [r]
    apply (div_eq_div_iff hden.ne' hd.ne').mpr
    linear_combination -htwin
  let K := k * s
  have hK : 0 < K := mul_pos hk hs
  have heK : K = (M : ℝ) * r / (1 - r) := by
    apply (eq_div_iff (sub_pos.mpr hr1).ne').mpr
    dsimp only [K, r]
    field_simp [hd.ne']
    linear_combination -hM
  have hKr : IsRational K := by
    rw [heK]
    exact ((IsRational.intCast M).mul hrr).div
      ((show IsRational (1 : ℝ) from ⟨1, by norm_num⟩).sub hrr)
  have he : ((n : ℝ) * r ^ 2 - K ^ 2) * s = K ^ 2 * r := by
    dsimp only [r, K]
    field_simp [hd.ne']
    linear_combination harea
  have hepos : 0 < (n : ℝ) * r ^ 2 - K ^ 2 := by
    have hp : 0 < ((n : ℝ) * r ^ 2 - K ^ 2) * s := by
      rw [he]
      exact mul_pos (sq_pos_of_pos hK) hr
    exact pos_of_mul_pos_left hp hs.le
  have hs' : s = (K ^ 2 * r) / ((n : ℝ) * r ^ 2 - K ^ 2) :=
    (eq_div_iff hepos.ne').mpr (by nlinarith [he])
  rw [hs']
  have hK2 : IsRational (K ^ 2) := by simpa only [pow_two] using hKr.mul hKr
  have hr2 : IsRational (r ^ 2) := by simpa only [pow_two] using hrr.mul hrr
  exact (hK2.mul hrr).div (((IsRational.natCast n).mul hr2).sub hK2)

end Erdos633b
