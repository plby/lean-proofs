import ErdosProblems.Erdos633b.BoundedAngleDenominator

/-! Exact local inventory inequalities near the small-angle limit.
Only integer nonnegativity is used; no limiting process or tiling oracle occurs. -/

namespace Erdos633b

theorem small_angle_local_counts (α β γ : ℝ) (hα : 0 < α)
    (hβ : 2 * Real.pi / 7 < β) (hγ : Real.pi / 2 < γ)
    (p q r k : ℕ) (hk : k ≤ 2)
    (he : (p : ℝ) * α + (q : ℝ) * β + (r : ℝ) * γ = (k : ℝ) * Real.pi) :
    q ≤ 6 ∧ r ≤ 3 := by
  have hb : 0 < β := by linarith [Real.pi_pos]
  have hg : 0 < γ := by linarith [Real.pi_pos]
  have hp := mul_nonneg (Nat.cast_nonneg p : (0 : ℝ) ≤ p) hα.le
  have hq := mul_nonneg (Nat.cast_nonneg q : (0 : ℝ) ≤ q) hb.le
  have hr := mul_nonneg (Nat.cast_nonneg r : (0 : ℝ) ≤ r) hg.le
  have hk' : (k : ℝ) ≤ 2 := by exact_mod_cast hk
  have hm := mul_le_mul_of_nonneg_right hk' Real.pi_pos.le
  constructor
  · by_contra hn
    have hq7 : (7 : ℝ) ≤ q := by exact_mod_cast (show 7 ≤ q by omega)
    have hmq := mul_le_mul_of_nonneg_right hq7 hb.le
    linarith
  · by_contra hn
    have hr4 : (4 : ℝ) ≤ r := by exact_mod_cast (show 4 ≤ r by omega)
    have hmr := mul_le_mul_of_nonneg_right hr4 hg.le
    linarith

theorem integer_nonnegative_of_small_angle (α L : ℝ) (hα : 0 < α)
    (hsmall : α < Real.pi / 21) (hL : -21 ≤ L) (J : ℤ)
    (he : L * α = (J : ℝ) * Real.pi) : 0 ≤ J := by
  have hm := mul_le_mul_of_nonneg_right hL hα.le
  by_contra hn
  have hJ : (J : ℝ) ≤ -1 := by exact_mod_cast (show J ≤ -1 by omega)
  have hmp := mul_le_mul_of_nonneg_right hJ Real.pi_pos.le
  linarith

theorem thirds_local_coefficient_lower (u : ℝ) (hu : -3 ≤ u) (hu' : u ≤ 1)
    (p q r : ℕ) (hq : q ≤ 6) (hr : r ≤ 3) :
    -21 ≤ 3 * (p : ℝ) - 3 * r + u * ((q : ℝ) - r) := by
  have hp : (0 : ℝ) ≤ p := Nat.cast_nonneg _
  have hq' : (q : ℝ) ≤ 6 := by exact_mod_cast hq
  have hr' : (r : ℝ) ≤ 3 := by exact_mod_cast hr
  by_cases hqr : (r : ℝ) ≤ q
  · have hm := mul_le_mul_of_nonneg_right hu (sub_nonneg.mpr hqr)
    nlinarith
  · have hm := mul_le_mul_of_nonpos_right hu' (sub_nonpos.mpr (le_of_not_ge hqr))
    have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg _
    nlinarith

theorem fifths_local_coefficient_lower (u : ℝ) (hu : -1 ≤ u) (hu' : u ≤ 0)
    (p q r : ℕ) (hq : q ≤ 6) (hr : r ≤ 3) :
    -21 ≤ 5 * (p : ℝ) - 5 * r + u * ((q : ℝ) - r) := by
  have hp : (0 : ℝ) ≤ p := Nat.cast_nonneg _
  have hq' : (q : ℝ) ≤ 6 := by exact_mod_cast hq
  have hr' : (r : ℝ) ≤ 3 := by exact_mod_cast hr
  by_cases hqr : (r : ℝ) ≤ q
  · have hm := mul_le_mul_of_nonneg_right hu (sub_nonneg.mpr hqr)
    nlinarith
  · have hm := mul_le_mul_of_nonpos_right hu' (sub_nonpos.mpr (le_of_not_ge hqr))
    nlinarith

theorem small_angle_thirds_local_bound (α β γ u : ℝ) (hα : 0 < α)
    (hsmall : α < Real.pi / 21) (hs : α + β + γ = Real.pi)
    (hu : -3 ≤ u) (hu' : u ≤ 1) (hb : 3 * β = Real.pi + u * α)
    (p q r k : ℕ) (hq : q ≤ 6) (hr : r ≤ 3)
    (he : (p : ℝ) * α + (q : ℝ) * β + (r : ℝ) * γ = (k : ℝ) * Real.pi) :
    q + 2 * r ≤ 3 * k := by
  have hh : (3 * (p : ℝ) - 3 * r + u * ((q : ℝ) - r)) * α =
      ((3 * (k : ℤ) - q - 2 * r : ℤ) : ℝ) * Real.pi := by
    push_cast
    linear_combination 3 * he - 3 * (r : ℝ) * hs - ((q : ℝ) - r) * hb
  have hJ := integer_nonnegative_of_small_angle α _ hα hsmall
    (thirds_local_coefficient_lower u hu hu' p q r hq hr) _ hh
  omega

theorem small_angle_fifths_local_bound (α β γ u : ℝ) (hα : 0 < α)
    (hsmall : α < Real.pi / 21) (hs : α + β + γ = Real.pi)
    (hu : -1 ≤ u) (hu' : u ≤ 0) (hb : 5 * β = 2 * Real.pi + u * α)
    (p q r k : ℕ) (hq : q ≤ 6) (hr : r ≤ 3)
    (he : (p : ℝ) * α + (q : ℝ) * β + (r : ℝ) * γ = (k : ℝ) * Real.pi) :
    2 * q + 3 * r ≤ 5 * k := by
  have hh : (5 * (p : ℝ) - 5 * r + u * ((q : ℝ) - r)) * α =
      ((5 * (k : ℤ) - 2 * q - 3 * r : ℤ) : ℝ) * Real.pi := by
    push_cast
    linear_combination 5 * he - 5 * (r : ℝ) * hs - ((q : ℝ) - r) * hb
  have hJ := integer_nonnegative_of_small_angle α _ hα hsmall
    (fifths_local_coefficient_lower u hu hu' p q r hq hr) _ hh
  omega

end Erdos633b
