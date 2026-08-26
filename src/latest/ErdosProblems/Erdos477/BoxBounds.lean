/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Box and exponent calculations in Proposition 3.4 of
Liam Price (GPT Pro), Large Powers Tile the Integers, 26 June 2026.
Formal author: Codex.

These are numerical bounds, not assertions about how many integral points
lie on a surface or curve.
-/

import Mathlib

namespace Erdos477

/-- A rational upper bound for the inverse square root used below. -/
lemma inv_sqrt_six_bounds : 0 < 1 / Real.sqrt 6 ∧ 1 / Real.sqrt 6 < 5 / 12 := by
  have hs : 0 < Real.sqrt 6 := Real.sqrt_pos.mpr (by norm_num)
  constructor
  · positivity
  · apply (div_lt_iff₀ hs).mpr
    have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ 6 by norm_num)
    have hlow : (12 : ℝ) / 5 < Real.sqrt 6 := by nlinarith
    linarith

/-- A fixed choice `η = 1/100` leaves room to absorb the logarithmic losses. -/
lemma sixth_power_exponent_bounds :
    2 / Real.sqrt 6 < (9 : ℝ) / 10 ∧
    1 / Real.sqrt 6 + 3 / 7 + 1 / 100 < (9 : ℝ) / 10 ∧
    1 / Real.sqrt 6 + 3 / 100 < (9 : ℝ) / 10 ∧
    3 / 7 + 1 / 100 - 4 / (2 * Real.sqrt 6) < 0 := by
  obtain ⟨hpos, hupper⟩ := inv_sqrt_six_bounds
  have hs : 0 < Real.sqrt 6 := Real.sqrt_pos.mpr (by norm_num)
  have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ 6 by norm_num)
  have hlow : (1 : ℝ) / 3 < 1 / Real.sqrt 6 := by
    apply (lt_div_iff₀ hs).mpr
    have : Real.sqrt 6 < 3 := by nlinarith
    linarith
  have htwo : 2 / Real.sqrt 6 = 2 * (1 / Real.sqrt 6) := by ring
  have hfour : 4 / (2 * Real.sqrt 6) = 2 * (1 / Real.sqrt 6) := by ring
  rw [htwo, hfour]
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

/-- Equation (7), without asymptotic notation: in both ranges, `R H` is at
most `C U²`. The hypotheses are the two upper bounds in equation (6). -/
lemma box_area_bound {U R H C : ℝ} (hU : 0 ≤ U) (hR : 0 < R)
    (hH : 0 ≤ H) (hC : 0 ≤ C) (hsmall : H ≤ C * R)
    (hlarge : R ^ 5 * H ≤ C * U ^ 6) : R * H ≤ C * U ^ 2 := by
  by_cases hRU : R ≤ U
  · calc
      R * H ≤ R * (C * R) := mul_le_mul_of_nonneg_left hsmall hR.le
      _ = C * R ^ 2 := by ring
      _ ≤ C * U ^ 2 := by gcongr
  · have hUR : U ≤ R := le_of_not_ge hRU
    by_cases hU0 : U = 0
    · subst U
      have hH0 : H = 0 := by
        have hRp : 0 < R ^ 5 := pow_pos hR _
        nlinarith
      simp [hH0]
    · have hUp : 0 < U := lt_of_le_of_ne hU (Ne.symm hU0)
      have h4 : U ^ 4 ≤ R ^ 4 := by gcongr
      have hh : 0 ≤ R * H := mul_nonneg hR.le hH
      have hmul : U ^ 4 * (R * H) ≤ U ^ 4 * (C * U ^ 2) := by
        calc
          U ^ 4 * (R * H) ≤ R ^ 4 * (R * H) := mul_le_mul_of_nonneg_right h4 hh
          _ = R ^ 5 * H := by ring
          _ ≤ C * U ^ 6 := hlarge
          _ = U ^ 4 * (C * U ^ 2) := by ring
      exact (mul_le_mul_iff_right₀ (pow_pos hUp 4)).mp hmul

/-- Equation (8) follows directly from the area bound. -/
lemma box_volume_bound {U R H C : ℝ} (hU : 0 ≤ U) (hR : 0 < R)
    (hH : 0 ≤ H) (hC : 0 ≤ C) (hsmall : H ≤ C * R)
    (hlarge : R ^ 5 * H ≤ C * U ^ 6) : U * (2 * R) * H ≤ 2 * C * U ^ 3 := by
  have ha := box_area_bound hU hR hH hC hsmall hlarge
  calc
    U * (2 * R) * H = (2 * U) * (R * H) := by ring
    _ ≤ (2 * U) * (C * U ^ 2) := mul_le_mul_of_nonneg_left ha (by positivity)
    _ = 2 * C * U ^ 3 := by ring

/-- The final comparison in equation (12): the exponent of `R` is negative. -/
lemma large_range_rpow_bound {U R : ℝ} (hU : 0 < U) (hUR : U ≤ R) :
    U ^ (Real.sqrt 6 / 2) *
        R ^ ((3 : ℝ) / 7 + 1 / 100 - 4 / (2 * Real.sqrt 6)) ≤
      U ^ (1 / Real.sqrt 6 + 3 / 7 + 1 / 100) := by
  have he := sixth_power_exponent_bounds.2.2.2
  have hpow : R ^ ((3 : ℝ) / 7 + 1 / 100 - 4 / (2 * Real.sqrt 6)) ≤
      U ^ ((3 : ℝ) / 7 + 1 / 100 - 4 / (2 * Real.sqrt 6)) := by
    exact Real.rpow_le_rpow_of_nonpos hU hUR he.le
  have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ 6 by norm_num)
  have hs : Real.sqrt 6 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  have hexp : Real.sqrt 6 / 2 + (3 / 7 + 1 / 100 - 4 / (2 * Real.sqrt 6)) =
      1 / Real.sqrt 6 + 3 / 7 + 1 / 100 := by
    field_simp
    nlinarith
  calc
    _ ≤ U ^ (Real.sqrt 6 / 2) *
        U ^ ((3 : ℝ) / 7 + 1 / 100 - 4 / (2 * Real.sqrt 6)) :=
      mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg hU.le _)
    _ = U ^ (Real.sqrt 6 / 2 + (3 / 7 + 1 / 100 - 4 / (2 * Real.sqrt 6))) :=
      (Real.rpow_add hU _ _).symm
    _ = _ := by rw [hexp]

#print axioms box_area_bound
-- 'Erdos477.box_area_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
#print axioms large_range_rpow_bound
-- 'Erdos477.large_range_rpow_bound' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos477
