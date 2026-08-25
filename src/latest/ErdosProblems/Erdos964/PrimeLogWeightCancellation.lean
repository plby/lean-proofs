import ErdosProblems.Erdos964.ScalarPrimeIntegrand

/-!
# Cancelling the logarithmic weight in the prime quadrature
-/

namespace Erdos964

theorem log_weight_cancel (l L p F d : ℝ) (hl : l ≠ 0) (hL : L ≠ 0) :
    (l / p) * (F / ((l / L) * d)) / L = F / (p * d) := by
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
  calc
    _ = (l * l⁻¹) * (L * L⁻¹) * (F * d⁻¹ * p⁻¹) := by ring
    _ = _ := by simp only [mul_inv_cancel₀ hl, mul_inv_cancel₀ hL, one_mul]; ring

theorem primeLogWeight_scalarPrimeIntegrand_eq (L a : ℝ) (p : ℕ)
    (hL : L ≠ 0) (hp : p.Prime) :
    (Real.log p / (p : ℝ)) * scalarPrimeIntegrand a (Real.log p / L) / L =
      scalarSieveFace (Real.log p / L) / ((p : ℝ) * (1 - a * (Real.log p / L))) := by
  unfold scalarPrimeIntegrand
  exact log_weight_cancel (Real.log p) L p _ _
    (Real.log_pos (by exact_mod_cast hp.one_lt)).ne' hL

theorem reference_log_weight_cancel (l L N p F : ℝ) (hL : L ≠ 0) (hN : N ≠ 0) :
    F / (p * (1 - (L / N) * (l / L))) = N * (F / (p * (N - l))) := by
  have hid : 1 - (L / N) * (l / L) = (N - l) / N := by field_simp
  rw [hid]
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
  ring

end Erdos964
