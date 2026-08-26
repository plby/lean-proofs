import ErdosProblems.Erdos1148.CommonCuspVector
import ErdosProblems.Erdos1148.FlowTimeBounds

/-! # A common excursion vector stays bounded at logarithmically extended endpoints -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups

lemma exp_two_log_mul_inv_sq {H : ℝ} (hH : 0 < H) :
    Real.exp (2 * Real.log H) * (H ^ 2)⁻¹ = 1 := by
  have hlog : Real.log (H ^ 2) = 2 * Real.log H := by rw [Real.log_pow]; norm_num
  rw [← hlog, Real.exp_log (pow_pos hH 2), mul_inv_cancel₀ (pow_ne_zero 2 hH.ne')]

theorem exists_buffered_primitive_cusp_vector (g : SL(2, ℝ)) {H a b : ℝ}
    (hH : 1 ≤ H) (hab : a ≤ b)
    (hcusp : ∀ t ∈ Set.Icc a b, modularMk (g * diagonalFlow t) ∈ modularCusp H) :
    ∃ u v : ℤ, IsCoprime u v ∧
      (∀ t ∈ Set.Icc a b, modularVectorLengthSq (g * diagonalFlow t) u v < (H ^ 2)⁻¹) ∧
      modularVectorLengthSq (g * diagonalFlow (a - 2 * Real.log H)) u v < 1 ∧
      modularVectorLengthSq (g * diagonalFlow (b + 2 * Real.log H)) u v < 1 := by
  obtain ⟨u, v, huv, hshort⟩ := exists_common_primitive_cusp_vector g hH hab hcusp
  have hHpos : 0 < H := by linarith
  have hlog : 0 ≤ Real.log H := Real.log_nonneg hH
  refine ⟨u, v, huv, hshort, ?_, ?_⟩
  · have hscale : Real.exp |a - 2 * Real.log H - a| * (H ^ 2)⁻¹ ≤ (1 : ℝ) ^ 2 := by
      rw [show a - 2 * Real.log H - a = -(2 * Real.log H) by ring,
        abs_neg, abs_of_nonneg (by positivity : 0 ≤ 2 * Real.log H), exp_two_log_mul_inv_sq hHpos]
      norm_num
    simpa only [one_pow] using modularVectorLengthSq_of_short_time g a
      (a - 2 * Real.log H) H 1 u v (hshort a ⟨le_rfl, hab⟩) hscale
  · have hscale : Real.exp |b + 2 * Real.log H - b| * (H ^ 2)⁻¹ ≤ (1 : ℝ) ^ 2 := by
      rw [show b + 2 * Real.log H - b = 2 * Real.log H by ring,
        abs_of_nonneg (by positivity : 0 ≤ 2 * Real.log H), exp_two_log_mul_inv_sq hHpos]
      norm_num
    simpa only [one_pow] using modularVectorLengthSq_of_short_time g b
      (b + 2 * Real.log H) H 1 u v (hshort b ⟨hab, le_rfl⟩) hscale

end Erdos1148.DukeArithmetic
