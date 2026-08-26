import ErdosProblems.Erdos421.ZetaPolynomialEnvelope

/-! # Zero exclusion from the proved polynomial-degree growth bound -/

namespace Erdos421

open Complex

theorem exists_riemannZeta_polynomial_zero_criterion :
    ∃ B > 0, ∃ r₀ > 0, ∀ K : ℕ, 12 ≤ K →
      ∀ R A t β : ℝ, 0 < R → R ≤ polynomialLogarithmicExponent K / 2 → 0 < A →
        (2 : ℝ) ^ K + R ≤ |t| →
        let u := R / (100 * (A + B * R + 1))
        u < r₀ → polynomialZetaEnvelope K R (2 * |t| + R) * (1 + 1 / u) ≤ Real.exp A →
          1 - u / 10 ≤ β → riemannZeta ((β : ℂ) + t * I) ≠ 0 := by
  obtain ⟨B, hB, r₀, hr₀, hpole⟩ := exists_riemannZeta_logDeriv_pole_bound
  refine ⟨B, hB, r₀, hr₀, ?_⟩
  intro K hK R A t β hR hRD hA hlo
  let u := R / (100 * (A + B * R + 1))
  change u < r₀ → _
  intro hur hexp hβ
  obtain ⟨hu, huR, he⟩ := zeta_zero_detection_scale hR hA hB.le
  have hpu : -(logDeriv riemannZeta ((1 + u : ℝ) : ℂ)).re ≤ 1 / u + B := by
    simpa only [add_sub_cancel_left] using
      hpole (1 + u) (by linarith : 1 < 1 + u) (by linarith : 1 + u < 1 + r₀)
  have ht : R < |t| := by
    have hpos : (0 : ℝ) < 2 ^ K := by positivity
    linarith only [hlo, hpos]
  apply riemannZeta_ne_zero_of_disk_norm_bounds hu huR hA ht hpu he
  · exact riemannZeta_polynomial_two_disks_bound hK hR hRD hu hlo le_rfl
      (by linarith [abs_nonneg t]) hexp
  · exact riemannZeta_polynomial_two_disks_bound hK hR hRD hu hlo
      (by rw [abs_mul]; norm_num; linarith [abs_nonneg t])
      (by rw [abs_mul]; norm_num) hexp
  · exact hβ

end Erdos421
