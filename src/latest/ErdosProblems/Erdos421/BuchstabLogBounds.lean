import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Complex.Exponential

/-! # Rational logarithmic bounds for the Buchstab positivity calculation -/

namespace Erdos421

theorem log_lower_cubic {x : ℝ} (hx : 1 ≤ x) :
    2 * ((x - 1) / (x + 1)) + (2 / 3 : ℝ) * ((x - 1) / (x + 1)) ^ 3 ≤ Real.log x := by
  let f := fun x : ℝ ↦ Real.log x - 2 * ((x - 1) / (x + 1)) -
    (2 / 3 : ℝ) * ((x - 1) / (x + 1)) ^ 3
  have hd : ∀ x : ℝ, 1 ≤ x →
      HasDerivAt f ((x - 1) ^ 4 / (x * (x + 1) ^ 4)) x := by
    intro x hx
    have hxp : 0 < x := by linarith
    have hx1 : x + 1 ≠ 0 := by linarith
    have ht := ((hasDerivAt_id x).sub_const 1).div ((hasDerivAt_id x).add_const 1) hx1
    have hraw := ((Real.hasDerivAt_log hxp.ne').sub (ht.const_mul 2)).sub
      ((ht.pow 3).const_mul (2 / 3 : ℝ))
    dsimp only [id_eq, Pi.div_apply, Pi.sub_apply, Pi.add_apply, Pi.pow_apply, Pi.mul_apply] at hraw
    norm_num only [Nat.reduceSub, Nat.cast_ofNat, one_mul, mul_one] at hraw
    convert hraw using 1 <;>
      first | rfl | (field_simp [hxp.ne', hx1]; ring)
  have hm : MonotoneOn f (Set.Ici 1) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 1)
      (fun x hx ↦ (hd x hx).continuousAt.continuousWithinAt)
      (fun x hx ↦ (hd x (interior_subset hx)).hasDerivWithinAt)
      (fun x hx ↦ by
        have hx1 : 1 ≤ x := interior_subset hx
        positivity)
  have h := hm (by simp : (1 : ℝ) ∈ Set.Ici 1) (Set.mem_Ici.mpr hx) hx
  norm_num [f] at h
  linarith

theorem log_lower_fraction {x : ℝ} (hx : 1 ≤ x) :
    2 * (x - 1) / (x + 1) ≤ Real.log x := by
  have h := log_lower_cubic hx
  have ht : 0 ≤ (x - 1) / (x + 1) := div_nonneg (by linarith) (by linarith)
  have hp := pow_nonneg ht 3
  rw [show 2 * (x - 1) / (x + 1) = 2 * ((x - 1) / (x + 1)) by ring]
  nlinarith

theorem log_two_ge_sixty_nine : (69 / 100 : ℝ) ≤ Real.log 2 := by
  have h := log_lower_cubic (by norm_num : (1 : ℝ) ≤ 2)
  norm_num at h
  linarith

theorem log_seven_fourths_le : Real.log (7 / 4 : ℝ) ≤ 14 / 25 := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 14 / 25) 5
  norm_num [Finset.sum_range_succ] at h
  apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 7 / 4)).mpr
  linarith

theorem log_hundred_over_thirty_nine_le : Real.log (100 / 39 : ℝ) ≤ 19 / 20 := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 19 / 20) 5
  norm_num [Finset.sum_range_succ] at h
  apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 100 / 39)).mpr
  linarith

theorem buchstab_initial_formula_upper {u : ℝ} (hu : 2 ≤ u) :
    (1 + Real.log (u - 1)) / u ≤ 23 / 40 := by
  have hu0 : 0 < u := by linarith
  have hv : 0 < u - 1 := by linarith
  have h := Real.log_le_sub_one_of_pos (show 0 < (u - 1) / (7 / 4 : ℝ) by positivity)
  rw [Real.log_div hv.ne' (by norm_num : (7 / 4 : ℝ) ≠ 0)] at h
  have hb := log_seven_fourths_le
  apply (div_le_iff₀ hu0).mpr
  norm_num at h
  linarith

theorem buchstab_initial_formula_lower_half {u : ℝ} (hu : u ∈ Set.Icc (2 : ℝ) 3) :
    (1 / 2 : ℝ) ≤ (1 + Real.log (u - 1)) / u := by
  have hu0 : 0 < u := by linarith [hu.1]
  have h := log_lower_fraction (show 1 ≤ u - 1 by linarith [hu.1])
  have hprod := (div_le_iff₀ (show 0 < (u - 1) + 1 by linarith)).mp h
  apply (le_div_iff₀ hu0).mpr
  have hquad := mul_nonneg (sub_nonneg.mpr hu.1) (sub_nonneg.mpr hu.2)
  have hb : (1 / 2 : ℝ) * u ^ 2 ≤ u * (1 + Real.log (u - 1)) := by
    nlinarith [hu.1]
  nlinarith [mul_pos hu0 (show 0 < u by exact hu0)]

theorem buchstab_initial_formula_lower {u : ℝ} (hu : u ∈ Set.Icc (5 / 2 : ℝ) 3) :
    (11 / 20 : ℝ) ≤ (1 + Real.log (u - 1)) / u := by
  have hu0 : 0 < u := by linarith [hu.1]
  have h := log_lower_fraction (show 1 ≤ u - 1 by linarith [hu.1])
  have hprod := (div_le_iff₀ (show 0 < (u - 1) + 1 by linarith)).mp h
  apply (le_div_iff₀ hu0).mpr
  have hquad := mul_nonneg (sub_nonneg.mpr hu.1) (sub_nonneg.mpr hu.2)
  have hb : (11 / 20 : ℝ) * u ^ 2 ≤ u * (1 + Real.log (u - 1)) := by
    nlinarith [hu.2]
  nlinarith [mul_pos hu0 (show 0 < u by exact hu0)]

end Erdos421
