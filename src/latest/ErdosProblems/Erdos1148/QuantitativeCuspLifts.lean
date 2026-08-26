import ErdosProblems.Erdos1148.FundamentalFrameHeight
import ErdosProblems.Erdos1148.IwasawaFrames
import ErdosProblems.Erdos1148.RotationEntryBounds

/-! # Explicit entry bounds for representatives outside a cusp -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups

lemma upperTriangularFrame_height_entry_bound {x h Y : ℝ} (hY : 0 < Y)
    (hx : |x| ≤ 1 / 2) (hh : 1 / 2 ≤ h) (hhY : h ≤ Y) (i j : Fin 2) :
    |upperTriangularFrame x h (by linarith : h ≠ 0) i j| ≤ Y + 2 := by
  have hhpos : 0 < h := by linarith
  fin_cases i <;> fin_cases j
  · change |h| ≤ Y + 2
    rw [abs_of_pos hhpos]
    linarith
  · change |x / h| ≤ Y + 2
    rw [abs_div, abs_of_pos hhpos]
    have hratio : |x| / h ≤ 1 := (div_le_one hhpos).mpr (by linarith)
    linarith
  · change |(0 : ℝ)| ≤ Y + 2
    rw [abs_zero]
    positivity
  · change |h⁻¹| ≤ Y + 2
    rw [abs_inv, abs_of_pos hhpos]
    have hinv : h⁻¹ ≤ 2 := by
      rw [← one_div]
      exact (div_le_iff₀ hhpos).mpr (by linarith)
    linarith

theorem fundamental_frame_entries_le_of_not_cusp {z : UpperHalfPlane}
    (hz : z ∈ ModularGroup.fd) (θ : ℝ) {Y : ℝ} (hY : 0 < Y)
    (hy : modularMk (z.toSL2R * rotationFrame θ) ∉ modularCusp Y) (i j : Fin 2) :
    |(z.toSL2R * rotationFrame θ) i j| ≤ 2 * (Y + 2) := by
  have himY := frame_im_le_height_sq_of_not_mem_cusp z θ hY hy
  have him : (1 / 2 : ℝ) < z.im := by
    nlinarith [ModularGroup.three_le_four_mul_im_sq_of_mem_fd hz, z.im_pos]
  have hh : (1 / 2 : ℝ) ≤ Real.sqrt z.im := by
    nlinarith [Real.sq_sqrt z.im_pos.le, Real.sqrt_nonneg z.im]
  have hhY : Real.sqrt z.im ≤ Y := by
    simpa only [Real.sqrt_sq hY.le] using Real.sqrt_le_sqrt himY
  rw [upperHalfPlane_toSL2R_eq_frame]
  calc
    _ ≤ 2 * (Y + 2) * 1 := matrix_two_mul_entry_bound
      (upperTriangularFrame z.re (Real.sqrt z.im) _) (rotationFrame θ)
      (by positivity) zero_le_one
      (upperTriangularFrame_height_entry_bound hY hz.2 hh hhY)
      (rotationFrame_abs_entries_le_one θ) i j
    _ = _ := by ring

theorem exists_bounded_lift_of_not_cusp {Y : ℝ} (hY : 0 < Y) (x : ModularOrbitSpace)
    (hx : x ∉ modularCusp Y) :
    ∃ g : SL(2, ℝ), modularMk g = x ∧ ∀ i j : Fin 2, |g i j| ≤ 2 * (Y + 2) := by
  obtain ⟨z, θ, hz, _, hmk⟩ := exists_modular_fundamental_frame x
  have hy : modularMk (z.toSL2R * rotationFrame θ) ∉ modularCusp Y := by rwa [hmk]
  exact ⟨z.toSL2R * rotationFrame θ, hmk, fundamental_frame_entries_le_of_not_cusp hz θ hY hy⟩

theorem exists_integral_bounded_lift_of_not_cusp {Y : ℝ} (hY : 0 < Y) (g : SL(2, ℝ))
    (hg : modularMk g ∉ modularCusp Y) :
    ∃ γ : SL(2, ℤ), ∀ i j : Fin 2, |((γ : SL(2, ℝ)) * g) i j| ≤ 2 * (Y + 2) := by
  obtain ⟨h, hmk, hh⟩ := exists_bounded_lift_of_not_cusp hY (modularMk g) hg
  obtain ⟨γ, hγ⟩ := (modularMk_eq_iff g h).mp hmk.symm
  exact ⟨γ, by simpa only [hγ] using hh⟩

end Erdos1148.DukeArithmetic
