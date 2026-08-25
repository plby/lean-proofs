import ErdosProblems.Erdos964.ScalarKernelFaces

/-!
# Polynomial primitives for the two scalar faces
-/

namespace Erdos964

noncomputable def scalarLargeFacePrimitive (q : ℝ) : ℝ :=
  3 / 2 * q ^ 6 - 42 / 5 * q ^ 5 + 73 / 4 * q ^ 4 - 56 / 3 * q ^ 3 + 8 * q ^ 2

noncomputable def scalarSmallFacePrimitive (z q : ℝ) : ℝ :=
  9 * z ^ 2 * q ^ 4 + (12 * z ^ 3 - 28 * z ^ 2) * q ^ 3 +
    (9 / 2 * z ^ 4 - 21 * z ^ 3 + 49 / 2 * z ^ 2) * q ^ 2

theorem scalarLargeFacePrimitive_one : scalarLargeFacePrimitive 1 = 41 / 60 := by
  norm_num [scalarLargeFacePrimitive]

theorem scalarFacePrimitive_eq_truncatedSieveFace (z : ℝ) :
    scalarLargeFacePrimitive 1 + scalarSmallFacePrimitive z (1 - z) -
      scalarLargeFacePrimitive (1 - z) = truncatedSieveFace z := by
  rw [truncatedSieveFace_eq]
  unfold scalarLargeFacePrimitive scalarSmallFacePrimitive sieveFaceKernel
  ring

theorem scalarLargeFacePrimitive_integral (q : ℝ) :
    (∫ v in (0 : ℝ)..q, v * scalarLargeKernelPolynomial v) = scalarLargeFacePrimitive q := by
  have hpoly : (fun v : ℝ => v * scalarLargeKernelPolynomial v) =
      (fun v => 9 * v ^ 5 - 42 * v ^ 4 + 73 * v ^ 3 - 56 * v ^ 2 + 16 * v ^ 1) := by
    funext v
    rw [scalarLargeKernelPolynomial_expand]
    ring
  rw [hpoly]
  simp (disch := (apply Continuous.intervalIntegrable; fun_prop)) only
    [intervalIntegral.integral_add, intervalIntegral.integral_sub,
      intervalIntegral.integral_const_mul, integral_pow]
  unfold scalarLargeFacePrimitive
  norm_num
  ring

theorem scalarSmallFacePrimitive_integral (z q : ℝ) :
    (∫ v in (0 : ℝ)..q, v * scalarSmallKernelPolynomial z v) = scalarSmallFacePrimitive z q := by
  have hpoly : (fun v : ℝ => v * scalarSmallKernelPolynomial z v) =
      (fun v => (36 * z ^ 2) * v ^ 3 + (36 * z ^ 3 - 84 * z ^ 2) * v ^ 2 +
        (9 * z ^ 4 - 42 * z ^ 3 + 49 * z ^ 2) * v ^ 1) := by
    funext v
    rw [scalarSmallKernelPolynomial_expand]
    ring
  rw [hpoly]
  simp (disch := (apply Continuous.intervalIntegrable; fun_prop)) only
    [intervalIntegral.integral_add, intervalIntegral.integral_const_mul, integral_pow]
  unfold scalarSmallFacePrimitive
  norm_num
  ring

end Erdos964
