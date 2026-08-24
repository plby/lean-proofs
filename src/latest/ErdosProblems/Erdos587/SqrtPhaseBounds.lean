import ErdosProblems.Erdos587.SqrtPhase

/-! Quantitative second and third derivatives of a square-root phase. -/

namespace Erdos587

lemma rpow_neg_three_halves {x : ℝ} (hx : 0 < x) :
    x ^ (-(3 / 2 : ℝ)) = 1 / (x * Real.sqrt x) := by
  rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_neg hx.le,
    Real.rpow_add hx, Real.rpow_one, ← Real.sqrt_eq_rpow, one_div]

lemma rpow_neg_five_halves {x : ℝ} (hx : 0 < x) :
    x ^ (-(5 / 2 : ℝ)) = 1 / (x ^ 2 * Real.sqrt x) := by
  rw [show (5 / 2 : ℝ) = 2 + 1 / 2 by norm_num, Real.rpow_neg hx.le,
    Real.rpow_add hx, Real.rpow_two, ← Real.sqrt_eq_rpow, one_div]

lemma sqrtAffinePhaseD2_eq_div {a b x : ℝ} (hx : 0 < a + b * x) :
    sqrtAffinePhaseD2 a b x = -(b ^ 2 / (4 * (a + b * x) * Real.sqrt (a + b * x))) := by
  rw [sqrtAffinePhaseD2, rpow_neg_three_halves hx]
  have hs : 0 < Real.sqrt (a + b * x) := Real.sqrt_pos.mpr hx
  field_simp

lemma sqrtAffinePhaseD3_eq_div {a b x : ℝ} (hx : 0 < a + b * x) :
    sqrtAffinePhaseD3 a b x = 3 * b ^ 3 / (8 * (a + b * x) ^ 2 * Real.sqrt (a + b * x)) := by
  rw [sqrtAffinePhaseD3, rpow_neg_five_halves hx]
  have hs : 0 < Real.sqrt (a + b * x) := Real.sqrt_pos.mpr hx
  field_simp

lemma sqrt_scale_bounds {S L A : ℝ} (hL : 0 < L) (hA : 1 ≤ A)
    (hlo : L ^ 2 / A ≤ S) (hhi : S ≤ L ^ 2) :
    0 < S ∧ L / A ≤ Real.sqrt S ∧ Real.sqrt S ≤ L := by
  have hApos : 0 < A := by linarith
  have hS : 0 < S := (div_pos (sq_pos_of_pos hL) hApos).trans_le hlo
  have hrootlo : (L / A) ^ 2 ≤ S := by
    have hh : L ^ 2 / A ^ 2 ≤ L ^ 2 / A :=
      div_le_div_of_nonneg_left (sq_nonneg L) hApos (by nlinarith)
    simpa only [div_pow] using hh.trans hlo
  refine ⟨hS, ?_, Real.sqrt_le_iff.mpr ⟨hL.le, hhi⟩⟩
  have hh := Real.sqrt_le_sqrt hrootlo
  rwa [Real.sqrt_sq (div_nonneg hL.le hApos.le)] at hh

theorem square_root_second_magnitude_bounds {b S L n A : ℝ}
    (hL : 0 < L) (hn : 0 < n) (hA : 1 ≤ A)
    (hblo : L ^ 2 / (A * n) ≤ b) (hbhi : b ≤ L ^ 2 / n)
    (hSlo : L ^ 2 / A ≤ S) (hShi : S ≤ L ^ 2) :
    L / (4 * A ^ 2 * n ^ 2) ≤ b ^ 2 / (4 * S * Real.sqrt S) ∧
      b ^ 2 / (4 * S * Real.sqrt S) ≤ A ^ 2 * L / (4 * n ^ 2) := by
  have hApos : 0 < A := by linarith
  obtain ⟨hSpos, hrootlo, hroothi⟩ := sqrt_scale_bounds hL hA hSlo hShi
  have hbpos : 0 < b := (div_pos (sq_pos_of_pos hL) (mul_pos hApos hn)).trans_le hblo
  have hrootpos : 0 < Real.sqrt S := Real.sqrt_pos.mpr hSpos
  have hdenlo : 4 * (L ^ 2 / A) * (L / A) ≤ 4 * S * Real.sqrt S := by gcongr
  have hdenhi : 4 * S * Real.sqrt S ≤ 4 * L ^ 2 * L := by gcongr
  constructor
  · calc
      _ = (L ^ 2 / (A * n)) ^ 2 / (4 * L ^ 2 * L) := by field_simp
      _ ≤ b ^ 2 / (4 * S * Real.sqrt S) := by gcongr
  · calc
      _ ≤ (L ^ 2 / n) ^ 2 / (4 * (L ^ 2 / A) * (L / A)) := by gcongr
      _ = _ := by field_simp

theorem square_root_third_magnitude_bounds {b S L n A : ℝ}
    (hL : 0 < L) (hn : 0 < n) (hA : 1 ≤ A)
    (hblo : L ^ 2 / (A * n) ≤ b) (hbhi : b ≤ L ^ 2 / n)
    (hSlo : L ^ 2 / A ≤ S) (hShi : S ≤ L ^ 2) :
    3 * L / (8 * A ^ 3 * n ^ 3) ≤ 3 * b ^ 3 / (8 * S ^ 2 * Real.sqrt S) ∧
      3 * b ^ 3 / (8 * S ^ 2 * Real.sqrt S) ≤ 3 * A ^ 3 * L / (8 * n ^ 3) := by
  have hApos : 0 < A := by linarith
  obtain ⟨hSpos, hrootlo, hroothi⟩ := sqrt_scale_bounds hL hA hSlo hShi
  have hbpos : 0 < b := (div_pos (sq_pos_of_pos hL) (mul_pos hApos hn)).trans_le hblo
  have hrootpos : 0 < Real.sqrt S := Real.sqrt_pos.mpr hSpos
  have hdenlo : 8 * (L ^ 2 / A) ^ 2 * (L / A) ≤ 8 * S ^ 2 * Real.sqrt S := by gcongr
  have hdenhi : 8 * S ^ 2 * Real.sqrt S ≤ 8 * (L ^ 2) ^ 2 * L := by gcongr
  constructor
  · calc
      _ = 3 * (L ^ 2 / (A * n)) ^ 3 / (8 * (L ^ 2) ^ 2 * L) := by field_simp
      _ ≤ 3 * b ^ 3 / (8 * S ^ 2 * Real.sqrt S) := by gcongr
  · calc
      _ ≤ 3 * (L ^ 2 / n) ^ 3 / (8 * (L ^ 2 / A) ^ 2 * (L / A)) := by gcongr
      _ = _ := by field_simp

theorem sqrtAffinePhase_scaled_derivative_bounds {a b x L n A : ℝ}
    (hL : 0 < L) (hn : 0 < n) (hA : 1 ≤ A)
    (hblo : L ^ 2 / (A * n) ≤ b) (hbhi : b ≤ L ^ 2 / n)
    (hSlo : L ^ 2 / A ≤ a + b * x) (hShi : a + b * x ≤ L ^ 2) :
    -(A ^ 3 * L / n ^ 2) ≤ sqrtAffinePhaseD2 a b x ∧
      sqrtAffinePhaseD2 a b x ≤ -(L / (8 * A ^ 3 * n ^ 2)) ∧
      L / (8 * A ^ 3 * n ^ 3) ≤ sqrtAffinePhaseD3 a b x ∧
      sqrtAffinePhaseD3 a b x ≤ A ^ 3 * L / n ^ 3 := by
  have hApos : 0 < A := by linarith
  have hSpos := (sqrt_scale_bounds hL hA hSlo hShi).1
  obtain ⟨h₂lo, h₂hi⟩ := square_root_second_magnitude_bounds hL hn hA hblo hbhi hSlo hShi
  obtain ⟨h₃lo, h₃hi⟩ := square_root_third_magnitude_bounds hL hn hA hblo hbhi hSlo hShi
  have hA23 : A ^ 2 ≤ A ^ 3 := pow_le_pow_right₀ hA (by omega)
  have h₂lower : L / (8 * A ^ 3 * n ^ 2) ≤ L / (4 * A ^ 2 * n ^ 2) := by
    apply div_le_div_of_nonneg_left hL.le (by positivity)
    have hh : 4 * A ^ 2 ≤ 8 * A ^ 3 := by nlinarith [sq_nonneg A]
    exact mul_le_mul_of_nonneg_right hh (sq_nonneg n)
  have h₂upper : A ^ 2 * L / (4 * n ^ 2) ≤ A ^ 3 * L / n ^ 2 := by
    calc
      _ = (A ^ 2 / 4) * (L / n ^ 2) := by ring
      _ ≤ A ^ 3 * (L / n ^ 2) :=
        mul_le_mul_of_nonneg_right (by nlinarith [sq_nonneg A]) (by positivity)
      _ = _ := by ring
  have h₃lower : L / (8 * A ^ 3 * n ^ 3) ≤ 3 * L / (8 * A ^ 3 * n ^ 3) := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    linarith
  have h₃upper : 3 * A ^ 3 * L / (8 * n ^ 3) ≤ A ^ 3 * L / n ^ 3 := by
    calc
      _ = (3 / 8 : ℝ) * (A ^ 3 * L / n ^ 3) := by ring
      _ ≤ 1 * (A ^ 3 * L / n ^ 3) := mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
      _ = _ := one_mul _
  rw [sqrtAffinePhaseD2_eq_div hSpos, sqrtAffinePhaseD3_eq_div hSpos]
  exact ⟨neg_le_neg (h₂hi.trans h₂upper), neg_le_neg (h₂lower.trans h₂lo),
    h₃lower.trans h₃lo, h₃hi.trans h₃upper⟩

end Erdos587
