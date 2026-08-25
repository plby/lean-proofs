import StackExchange.Puzzling139335.PrefixCertificate.PolynomialBounds

/-!
# Angular estimates for the prefix certificate

The support inequality forces a small angle sum and small half-angle tangents.
The sharper estimate for the smaller tangent uses the triple-angle sine identity.
-/

namespace Puzzling139335.PrefixCertificate

lemma angle_sum_lt_pi_div_six {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hab : a + b < Real.pi / 2)
    (hH : 2 * Real.cos a * Real.sin (a + b) ≤ 1 - Real.sin a) :
    a + b < Real.pi / 6 := by
  have hca : 0 < Real.cos a := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos],
    by linarith⟩
  have hsa : 0 < Real.sin a := Real.sin_pos_of_pos_of_lt_pi ha (by linarith [Real.pi_pos])
  have hsc : 1 < Real.sin a + Real.cos a := by
    nlinarith [Real.sin_sq_add_cos_sq a, mul_pos hsa hca]
  have hs : Real.sin (a + b) < 1 / 2 := by
    have hmul : Real.cos a * (2 * Real.sin (a + b)) < Real.cos a * 1 := by
      nlinarith only [hH, hsc]
    have := lt_of_mul_lt_mul_left hmul hca.le
    linarith
  by_contra h
  have hle : Real.sin (Real.pi / 6) ≤ Real.sin (a + b) :=
    Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos]) hab.le
      (le_of_not_gt h)
  rw [Real.sin_pi_div_six] at hle
  linarith

lemma tan_half_pos {a : ℝ} (ha : 0 < a) (haπ : a < Real.pi) :
    0 < Real.tan (a / 2) :=
  Real.tan_pos_of_pos_of_lt_pi_div_two (by linarith) (by linarith)

lemma tan_half_lt_one {a : ℝ} (ha : 0 < a) (haπ : a < Real.pi / 2) :
    Real.tan (a / 2) < 1 := by
  have h := Real.tan_lt_tan_of_nonneg_of_lt_pi_div_two
    (show 0 ≤ a / 2 by linarith)
    (show Real.pi / 4 < Real.pi / 2 by linarith [Real.pi_pos])
    (show a / 2 < Real.pi / 4 by linarith)
  simpa only [Real.tan_pi_div_four] using h

lemma tan_half_lt_two_sevenths {a : ℝ} (ha : 0 < a) (haπ : a < Real.pi / 6) :
    Real.tan (a / 2) < 2 / 7 := by
  have ht0 : 0 < Real.tan (a / 2) := tan_half_pos ha (by linarith [Real.pi_pos])
  have ht1 : Real.tan (a / 2) < 1 := tan_half_lt_one ha (by linarith [Real.pi_pos])
  have hs : Real.sin a < 1 / 2 := by
    have h := Real.sin_lt_sin_of_lt_of_le_pi_div_two
      (show -(Real.pi / 2) ≤ a by linarith [Real.pi_pos])
      (show Real.pi / 6 ≤ Real.pi / 2 by linarith [Real.pi_pos]) haπ
    simpa only [Real.sin_pi_div_six] using h
  rw [Real.sin_eq_two_mul_tan_half_div_one_add_tan_half_sq] at hs
  have hden : 0 < 1 + Real.tan (a / 2) ^ 2 := by positivity
  have hpoly := (div_lt_iff₀ hden).mp hs
  by_contra h
  have ht : 2 / 7 ≤ Real.tan (a / 2) := le_of_not_gt h
  have hp : 0 ≤ (Real.tan (a / 2) - 2 / 7) * (4 - Real.tan (a / 2) - 2 / 7) :=
    mul_nonneg (by linarith) (by linarith)
  nlinarith only [hpoly, hp]

lemma tan_add_gt_sum {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hab : a + b < Real.pi / 2) :
    Real.tan a + Real.tan b < Real.tan (a + b) := by
  have hca : 0 < Real.cos a := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_pos], by linarith⟩
  have hcb : 0 < Real.cos b := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_pos], by linarith⟩
  have hcab : 0 < Real.cos (a + b) := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_pos], hab⟩
  have hsa : 0 < Real.sin a := Real.sin_pos_of_pos_of_lt_pi ha (by linarith [Real.pi_pos])
  have hsb : 0 < Real.sin b := Real.sin_pos_of_pos_of_lt_pi hb (by linarith [Real.pi_pos])
  have hsab : 0 < Real.sin (a + b) := Real.sin_pos_of_pos_of_lt_pi (by linarith)
    (by linarith [Real.pi_pos])
  rw [Real.tan_eq_sin_div_cos, Real.tan_eq_sin_div_cos, Real.tan_eq_sin_div_cos]
  calc
    Real.sin a / Real.cos a + Real.sin b / Real.cos b =
        Real.sin (a + b) / (Real.cos a * Real.cos b) := by
      rw [Real.sin_add]
      field_simp
    _ < Real.sin (a + b) / Real.cos (a + b) := by
      apply div_lt_div_of_pos_left hsab hcab
      rw [Real.cos_add]
      nlinarith only [mul_pos hsa hsb]

lemma tan_half_sum_lt_two_sevenths {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hab : a + b < Real.pi / 2)
    (hH : 2 * Real.cos a * Real.sin (a + b) ≤ 1 - Real.sin a) :
    Real.tan (a / 2) + Real.tan (b / 2) < 2 / 7 := by
  have hg := angle_sum_lt_pi_div_six ha hb hab hH
  have hsum := tan_add_gt_sum (show 0 < a / 2 by linarith)
    (show 0 < b / 2 by linarith)
    (show a / 2 + b / 2 < Real.pi / 2 by linarith [Real.pi_pos])
  rw [← add_div] at hsum
  exact hsum.trans (tan_half_lt_two_sevenths (by linarith) hg)

lemma sin_min_angle_certificate {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hab : a + b < Real.pi / 2)
    (hH : 2 * Real.cos a * Real.sin (a + b) ≤ 1 - Real.sin a) :
    5 * Real.sin (min a b) - 4 * Real.sin (min a b) ^ 3 ≤ 1 := by
  have hg := angle_sum_lt_pi_div_six ha hb hab hH
  have hk0 : 0 < min a b := lt_min ha hb
  have hka : min a b ≤ a := min_le_left _ _
  have hkb : min a b ≤ b := min_le_right _ _
  have hsa : Real.sin (min a b) ≤ Real.sin a :=
    Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos])
      (by linarith) hka
  have hsb : Real.sin (min a b) ≤ Real.sin b :=
    Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos])
      (by linarith) hkb
  have hs3 : Real.sin (3 * min a b) ≤ Real.sin (2 * a + b) :=
    Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos])
      (by linarith [Real.pi_pos]) (by linarith)
  have hid := Real.two_mul_sin_mul_cos (a + b) a
  have hsub : a + b - a = b := by ring
  have hadd : a + b + a = 2 * a + b := by ring
  rw [hsub, hadd] at hid
  rw [Real.sin_three_mul] at hs3
  nlinarith only [hH, hid, hsa, hsb, hs3]

lemma tan_half_min {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hab : a + b < Real.pi / 2) :
    Real.tan (min a b / 2) = min (Real.tan (a / 2)) (Real.tan (b / 2)) := by
  have haI : a / 2 ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hbI : b / 2 ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  rcases le_total a b with h | h
  · have ht : Real.tan (a / 2) ≤ Real.tan (b / 2) :=
      Real.strictMonoOn_tan.monotoneOn haI hbI (by linarith)
    rw [min_eq_left h, min_eq_left ht]
  · have ht : Real.tan (b / 2) ≤ Real.tan (a / 2) :=
      Real.strictMonoOn_tan.monotoneOn hbI haI (by linarith)
    rw [min_eq_right h, min_eq_right ht]

lemma tan_half_min_lt_three_twenty_eighths {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hab : a + b < Real.pi / 2)
    (hH : 2 * Real.cos a * Real.sin (a + b) ≤ 1 - Real.sin a) :
    min (Real.tan (a / 2)) (Real.tan (b / 2)) < 3 / 28 := by
  have hk0 : 0 < min a b := lt_min ha hb
  have hkπ : min a b < Real.pi / 2 := by
    have hka := min_le_left a b
    linarith
  have ht0 : 0 < Real.tan (min a b / 2) := tan_half_pos hk0 (by linarith [Real.pi_pos])
  have ht1 : Real.tan (min a b / 2) < 1 := tan_half_lt_one hk0 hkπ
  have hs := sin_min_angle_certificate ha hb hab hH
  rw [Real.sin_eq_two_mul_tan_half_div_one_add_tan_half_sq] at hs
  have hQ := sin_certificate_Q_nonneg ht1 ht0 hs
  have ht := lt_three_twenty_eighths_of_Q_nonneg ht0 ht1 hQ
  rwa [tan_half_min ha hb hab] at ht

theorem angular_bounds {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hab : a + b < Real.pi / 2)
    (hH : 2 * Real.cos a * Real.sin (a + b) ≤ 1 - Real.sin a) :
    a + b < Real.pi / 6 ∧
      0 < Real.tan (a / 2) ∧
      0 < Real.tan (b / 2) ∧
      Real.tan (a / 2) + Real.tan (b / 2) < 2 / 7 ∧
      0 < min (Real.tan (a / 2)) (Real.tan (b / 2)) ∧
      min (Real.tan (a / 2)) (Real.tan (b / 2)) < 3 / 28 := by
  have ht := tan_half_pos ha (show a < Real.pi by linarith [Real.pi_pos])
  have hr := tan_half_pos hb (show b < Real.pi by linarith [Real.pi_pos])
  exact ⟨angle_sum_lt_pi_div_six ha hb hab hH, ht, hr,
    tan_half_sum_lt_two_sevenths ha hb hab hH, lt_min ht hr,
    tan_half_min_lt_three_twenty_eighths ha hb hab hH⟩

end Puzzling139335.PrefixCertificate
