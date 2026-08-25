import ErdosProblems.Erdos964.ScalarKernelFacePrimitive

/-!
# Uniform endpoint sensitivity of the two face primitives
-/

namespace Erdos964

open MeasureTheory

theorem norm_large_face_integrand_le (v : ℝ) (hv : v ∈ Set.Icc (0 : ℝ) 1) :
    ‖v * scalarLargeKernelPolynomial v‖ ≤ 16 := by
  have hv2 : v ^ 2 ≤ v := by nlinarith [mul_le_mul_of_nonneg_left hv.2 hv.1]
  have hg0 : 0 ≤ 4 - 7 * v + 3 * v ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hv.2) (show 0 ≤ 4 - 3 * v by linarith [hv.2])]
  have hg4 : 4 - 7 * v + 3 * v ^ 2 ≤ 4 := by nlinarith [hv.1, hv2]
  have hsq : (4 - 7 * v + 3 * v ^ 2) ^ 2 ≤ 16 := by
    have h := pow_le_pow_left₀ hg0 hg4 2
    norm_num at h
    exact h
  unfold scalarLargeKernelPolynomial
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hv.1 (sq_nonneg _))]
  calc
    _ ≤ 1 * (4 - 7 * v + 3 * v ^ 2) ^ 2 := mul_le_mul_of_nonneg_right hv.2 (sq_nonneg _)
    _ ≤ 16 := by simpa only [one_mul] using hsq

theorem norm_small_face_integrand_le (z v : ℝ) (hz : z ∈ Set.Icc (0 : ℝ) 1)
    (hv : v ∈ Set.Icc (0 : ℝ) 1) : ‖v * scalarSmallKernelPolynomial z v‖ ≤ 100 := by
  have hc0 : 0 ≤ 7 - 6 * v := by linarith [hv.2]
  have hc7 : 7 - 6 * v ≤ 7 := by linarith [hv.1]
  have hprod0 := mul_nonneg hc0 hz.1
  have hprod7 : (7 - 6 * v) * z ≤ 7 := by
    simpa only [mul_one] using mul_le_mul hc7 hz.2 hz.1 (by norm_num : (0 : ℝ) ≤ 7)
  have hz2 := pow_le_one₀ hz.1 hz.2 (n := 2)
  have hu : |(7 - 6 * v) * z - 3 * z ^ 2| ≤ 10 := by
    apply abs_le.mpr
    constructor <;> nlinarith [sq_nonneg z]
  have hsq : ((7 - 6 * v) * z - 3 * z ^ 2) ^ 2 ≤ 100 := by
    have h := pow_le_pow_left₀ (abs_nonneg _) hu 2
    simpa only [sq_abs, show (10 : ℝ) ^ 2 = 100 by norm_num] using h
  unfold scalarSmallKernelPolynomial
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hv.1 (sq_nonneg _))]
  calc
    _ ≤ 1 * ((7 - 6 * v) * z - 3 * z ^ 2) ^ 2 := mul_le_mul_of_nonneg_right hv.2 (sq_nonneg _)
    _ ≤ 100 := by simpa only [one_mul] using hsq

theorem abs_integral_primitive_sub_le_on_unit (f F : ℝ → ℝ) (hf : Continuous f)
    (hF : ∀ q : ℝ, (∫ v in (0 : ℝ)..q, f v) = F q) (C : ℝ)
    (hbound : ∀ v ∈ Set.Icc (0 : ℝ) 1, ‖f v‖ ≤ C)
    (x y : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    |F x - F y| ≤ C * |x - y| := by
  have h0y : IntervalIntegrable f volume 0 y := hf.intervalIntegrable 0 y
  have hyx : IntervalIntegrable f volume y x := hf.intervalIntegrable y x
  have hsplit := intervalIntegral.integral_add_adjacent_intervals h0y hyx
  rw [hF y, hF x] at hsplit
  have heq : (∫ v in y..x, f v) = F x - F y := by linarith
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := y) (b := x)
    (f := f) (C := C) (fun v hv => by
      change min y x < v ∧ v ≤ max y x at hv
      exact hbound v ⟨(le_min hy.1 hx.1).trans hv.1.le, hv.2.trans (max_le hy.2 hx.2)⟩)
  simpa only [heq, Real.norm_eq_abs] using h

theorem scalarLargeFacePrimitive_lipschitz (x y : ℝ)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    |scalarLargeFacePrimitive x - scalarLargeFacePrimitive y| ≤ 16 * |x - y| :=
  abs_integral_primitive_sub_le_on_unit _ _ (by unfold scalarLargeKernelPolynomial; fun_prop)
    scalarLargeFacePrimitive_integral 16 norm_large_face_integrand_le x y hx hy

theorem scalarSmallFacePrimitive_lipschitz (z x y : ℝ) (hz : z ∈ Set.Icc (0 : ℝ) 1)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    |scalarSmallFacePrimitive z x - scalarSmallFacePrimitive z y| ≤ 100 * |x - y| :=
  abs_integral_primitive_sub_le_on_unit _ _ (by unfold scalarSmallKernelPolynomial; fun_prop)
    (scalarSmallFacePrimitive_integral z) 100 (norm_small_face_integrand_le z · hz) x y hx hy

end Erdos964
