import ErdosProblems.Erdos633b.CubicConicLifts
import ErdosProblems.Erdos633b.CaseFiveMetric

/-! Exact exponential coordinates for the normalized side conic of a
triangle with a 120-degree angle. -/

namespace Erdos633b

noncomputable def sixthRootCoordinate : ℂ := (1 + (Real.sqrt 3 : ℂ) * Complex.I) / 2

theorem sixthRootCoordinate_quadratic :
    sixthRootCoordinate ^ 2 - sixthRootCoordinate + 1 = 0 := by
  have hs : (Real.sqrt 3 : ℂ) ^ 2 = 3 := by
    exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  unfold sixthRootCoordinate
  ring_nf
  rw [Complex.I_sq, hs]
  ring

theorem conic_exponential_linear_coordinates (α : ℝ) :
    (2 * sixthRootCoordinate - 1) * ((2 * Real.sin α / Real.sqrt 3 : ℝ) : ℂ) =
      Complex.exp ((α : ℂ) * Complex.I) - (Complex.exp ((α : ℂ) * Complex.I))⁻¹ ∧
    (2 * sixthRootCoordinate - 1) *
        ((Real.cos α - Real.sin α / Real.sqrt 3 : ℝ) : ℂ) =
      sixthRootCoordinate * (Complex.exp ((α : ℂ) * Complex.I))⁻¹ -
        (1 - sixthRootCoordinate) * Complex.exp ((α : ℂ) * Complex.I) := by
  have hs : (Real.sqrt 3 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)).ne'
  rw [← Complex.exp_neg]
  have hn : -((α : ℂ) * Complex.I) = (-α : ℂ) * Complex.I := by ring
  rw [hn, Complex.exp_mul_I, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg]
  unfold sixthRootCoordinate
  push_cast
  constructor <;> field_simp [hs] <;> ring

theorem conic_exponential_coordinates (α : ℝ) :
    let z := Complex.exp ((α : ℂ) * Complex.I)
    (2 * sixthRootCoordinate - 1) * z * ((2 * Real.sin α / Real.sqrt 3 : ℝ) : ℂ) =
        z ^ 2 - 1 ∧
      (2 * sixthRootCoordinate - 1) * z *
          ((Real.cos α - Real.sin α / Real.sqrt 3 : ℝ) : ℂ) =
        sixthRootCoordinate * (1 + z ^ 2) - z ^ 2 := by
  let z := Complex.exp ((α : ℂ) * Complex.I)
  have hz : z ≠ 0 := Complex.exp_ne_zero _
  obtain ⟨hx, hy⟩ := conic_exponential_linear_coordinates α
  change (2 * sixthRootCoordinate - 1) * _ = z - z⁻¹ at hx
  change (2 * sixthRootCoordinate - 1) * _ =
    sixthRootCoordinate * z⁻¹ - (1 - sixthRootCoordinate) * z at hy
  change (2 * sixthRootCoordinate - 1) * z * _ = z ^ 2 - 1 ∧ _
  constructor
  · calc
      _ = z * ((2 * sixthRootCoordinate - 1) *
          ((2 * Real.sin α / Real.sqrt 3 : ℝ) : ℂ)) := by ring
      _ = z * (z - z⁻¹) := by rw [hx]
      _ = _ := by field_simp [hz]
  · calc
      _ = z * ((2 * sixthRootCoordinate - 1) *
          ((Real.cos α - Real.sin α / Real.sqrt 3 : ℝ) : ℂ)) := by ring
      _ = z * (sixthRootCoordinate * z⁻¹ - (1 - sixthRootCoordinate) * z) := by rw [hy]
      _ = _ := by field_simp [hz]; ring

namespace Triangle

theorem groupTwo_real_sine_coordinates (S : Triangle) (hg : S.angle 2 = 2 * Real.pi / 3) :
    S.side 0 / S.side 2 = 2 * Real.sin (S.angle 0) / Real.sqrt 3 ∧
    S.side 1 / S.side 2 = Real.cos (S.angle 0) - Real.sin (S.angle 0) / Real.sqrt 3 := by
  have hβ : S.angle 1 = Real.pi / 3 - S.angle 0 := by linarith [S.angle_sum]
  have hγ : S.angle 2 = Real.pi - Real.pi / 3 := by linarith
  have hs : Real.sqrt 3 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)).ne'
  constructor
  · rw [S.side_ratio_eq_sine_ratio, hγ, Real.sin_pi_sub, Real.sin_pi_div_three]
    field_simp [hs]
  · rw [S.side_ratio_eq_sine_ratio, hβ, hγ, Real.sin_pi_sub, Real.sin_sub,
      Real.sin_pi_div_three, Real.cos_pi_div_three]
    field_simp [hs]

theorem groupTwo_exponential_coordinates (S : Triangle) (hg : S.angle 2 = 2 * Real.pi / 3) :
    let z := Complex.exp ((S.angle 0 : ℂ) * Complex.I)
    (2 * sixthRootCoordinate - 1) * z * ((S.side 0 / S.side 2 : ℝ) : ℂ) = z ^ 2 - 1 ∧
      (2 * sixthRootCoordinate - 1) * z * ((S.side 1 / S.side 2 : ℝ) : ℂ) =
        sixthRootCoordinate * (1 + z ^ 2) - z ^ 2 := by
  obtain ⟨hx, hy⟩ := S.groupTwo_real_sine_coordinates hg
  rw [hx, hy]
  exact conic_exponential_coordinates (S.angle 0)

end Triangle
end Erdos633b
