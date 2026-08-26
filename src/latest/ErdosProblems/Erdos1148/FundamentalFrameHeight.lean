import ErdosProblems.Erdos1148.FrameVectorLengths
import ErdosProblems.Erdos1148.ModularCompactCore

/-! # In a fundamental frame, the intrinsic cusp height is the square root of im(z) -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups

lemma one_le_intCast_sq {v : ℤ} (hv : v ≠ 0) : (1 : ℝ) ≤ (v : ℝ) ^ 2 := by
  have h : (1 : ℤ) ≤ v ^ 2 := by have := sq_pos_of_ne_zero hv; omega
  exact_mod_cast h

theorem im_gt_height_sq_of_frame_mem_cusp {z : UpperHalfPlane} (hz : z ∈ ModularGroup.fd)
    (θ : ℝ) {H : ℝ} (hH : 2 ≤ H)
    (hcusp : modularMk (z.toSL2R * rotationFrame θ) ∈ modularCusp H) : H ^ 2 < z.im := by
  have hH0 : 0 < H := by linarith
  have him : (1 / 2 : ℝ) < z.im := by
    nlinarith [ModularGroup.three_le_four_mul_im_sq_of_mem_fd hz, z.im_pos]
  obtain ⟨u, v, huv, hshort⟩ := (mem_modularCusp_iff_representative _ H).mp hcusp
  rw [upperHalfPlane_toSL2R_eq_frame z] at hshort
  change modularVectorLengthSq
    (cuspFrame z.re (Real.sqrt z.im) θ (Real.sqrt_ne_zero'.mpr z.im_pos)) u v < (H ^ 2)⁻¹ at hshort
  rw [modularVectorLengthSq_cuspFrame, Real.sq_sqrt z.im_pos.le] at hshort
  have hcap : (H ^ 2)⁻¹ ≤ 1 / 4 := by
    rw [inv_eq_one_div]
    apply (div_le_iff₀ (sq_pos_of_pos hH0)).mpr
    nlinarith
  have hv : v = 0 := by
    by_contra hv
    have hsq := mul_le_mul_of_nonneg_left (one_le_intCast_sq hv) z.im_pos.le
    have hpos := div_nonneg (sq_nonneg ((u : ℝ) - z.re * v)) z.im_pos.le
    nlinarith
  have hu : u ≠ 0 := huv.resolve_right (not_not.mpr hv)
  rw [hv] at hshort
  simp only [Int.cast_zero, mul_zero, sub_zero, zero_pow (by norm_num : 2 ≠ 0), add_zero] at hshort
  have hless : 1 / z.im < 1 / H ^ 2 :=
    (div_le_div_of_nonneg_right (one_le_intCast_sq hu) z.im_pos.le).trans_lt
      (by simpa only [one_div] using hshort)
  exact (one_div_lt_one_div z.im_pos (sq_pos_of_pos hH0)).mp hless

theorem sqrt_im_gt_height_of_frame_mem_cusp {z : UpperHalfPlane} (hz : z ∈ ModularGroup.fd)
    (θ : ℝ) {H : ℝ} (hH : 2 ≤ H)
    (hcusp : modularMk (z.toSL2R * rotationFrame θ) ∈ modularCusp H) : H < Real.sqrt z.im := by
  have h := Real.sqrt_lt_sqrt (sq_nonneg H) (im_gt_height_sq_of_frame_mem_cusp hz θ hH hcusp)
  simpa only [Real.sqrt_sq (by linarith : 0 ≤ H)] using h

theorem frame_im_le_height_sq_of_not_mem_cusp (z : UpperHalfPlane) (θ : ℝ) {Y : ℝ}
    (hY : 0 < Y) (hy : modularMk (z.toSL2R * rotationFrame θ) ∉ modularCusp Y) : z.im ≤ Y ^ 2 := by
  have hvec : (Y ^ 2)⁻¹ ≤ modularVectorLengthSq (z.toSL2R * rotationFrame θ) 1 0 := by
    by_contra h
    apply hy
    exact (mem_modularCusp_iff_representative _ _).mpr
      ⟨1, 0, Or.inl (by norm_num), lt_of_not_ge h⟩
  rw [upperHalfPlane_toSL2R_eq_frame z] at hvec
  change (Y ^ 2)⁻¹ ≤ modularVectorLengthSq
    (cuspFrame z.re (Real.sqrt z.im) θ (Real.sqrt_ne_zero'.mpr z.im_pos)) 1 0 at hvec
  rw [modularVectorLengthSq_cuspFrame, Real.sq_sqrt z.im_pos.le] at hvec
  norm_num only [Int.cast_one, Int.cast_zero, mul_zero, sub_zero, one_pow, zero_pow,
    add_zero] at hvec
  exact (one_div_le_one_div (sq_pos_of_pos hY) z.im_pos).mp (by simpa only [one_div] using hvec)

end Erdos1148.DukeArithmetic
