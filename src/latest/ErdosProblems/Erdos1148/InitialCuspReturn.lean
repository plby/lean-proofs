import ErdosProblems.Erdos1148.HeightReturningRefinement
import ErdosProblems.Erdos1148.BufferedCuspVector
import ErdosProblems.Erdos1148.CuspFlowDistortion

/-! # Returning covers for the cusp run truncated at the initial observation time -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups

theorem not_cusp_before_log_buffer (g : SL(2, ℝ)) {H Y : ℝ} (hH : 1 ≤ H)
    (hentry : modularMk (g * diagonalFlow (2 * Real.log H)) ∉ modularCusp Y) :
    modularMk g ∉ modularCusp (Y * H) := by
  have hHpos : 0 < H := by linarith
  have hscale : Real.exp |2 * Real.log H| * ((Y * H) ^ 2)⁻¹ ≤ (Y ^ 2)⁻¹ := by
    rw [abs_of_nonneg (mul_nonneg (by norm_num) (Real.log_nonneg hH)), mul_pow,
      mul_inv_rev, ← mul_assoc, exp_two_log_mul_inv_sq hHpos, one_mul]
  intro hg
  exact hentry (modularRightTranslate_mem_cusp_of_scale hscale hg)

theorem initial_buffered_cusp_hasReturningVector (g : SL(2, ℝ)) {H Y L : ℝ}
    (hH : 1 ≤ H) (hL : 0 ≤ L)
    (hentry : modularMk (g * diagonalFlow (2 * Real.log H)) ∉ modularCusp Y)
    (hcusp : ∀ t ∈ Set.Icc 0 L,
      modularMk ((g * diagonalFlow (2 * Real.log H)) * diagonalFlow t) ∈ modularCusp H) :
    HasReturningVector (L + 4 * Real.log H) (((Y * H) ^ 2)⁻¹) g := by
  obtain ⟨u, v, huv, _, hleft, hright⟩ := exists_buffered_primitive_cusp_vector
    (g * diagonalFlow (2 * Real.log H)) hH hL hcusp
  have hnot := not_cusp_before_log_buffer g hH hentry
  have hstart : modularVectorLengthSq g u v ≤ 1 := by
    simpa only [zero_sub, mul_assoc, ← diagonalFlow_add, add_neg_cancel,
      diagonalFlow_zero, mul_one] using hleft.le
  have hend : modularVectorLengthSq (g * diagonalFlow (L + 4 * Real.log H)) u v ≤ 1 := by
    have heq : 2 * Real.log H + (L + 2 * Real.log H) = L + 4 * Real.log H := by ring
    simpa only [mul_assoc, ← diagonalFlow_add, heq] using hright.le
  refine ⟨(u, v), ?_, hstart, hend⟩
  apply le_of_not_gt
  intro h
  exact hnot ((mem_modularCusp_iff_primitive _ _).mpr ⟨u, v, huv, h⟩)

theorem exists_initial_cusp_run_lift_refinement {η : ℝ} (hηpos : 0 < η) (hη : η ≤ 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (H Y L : ℝ), 1 ≤ H → 1 ≤ Y → 0 ≤ L →
      ∀ E : Set SL(2, ℝ), LiftForwardClose η 0 E →
      (∀ g ∈ E, modularMk (g * diagonalFlow (2 * Real.log H)) ∉ modularCusp Y) →
      (∀ g ∈ E, ∀ t ∈ Set.Icc 0 L,
        modularMk ((g * diagonalFlow (2 * Real.log H)) * diagonalFlow t) ∈ modularCusp H) →
      LiftCoverBound η (L + 4 * Real.log H) E
        (C * (Y * H + 1) ^ 3 * Real.exp ((L + 4 * Real.log H) / 2)) := by
  obtain ⟨C, hC, hrefine⟩ := exists_height_returning_lift_refinement hηpos hη
  refine ⟨C, hC, ?_⟩
  intro H Y L hH hY hL E hE hentry hcusp
  have hYH : 1 ≤ Y * H := by nlinarith
  have hT : 0 ≤ L + 4 * Real.log H := by linarith [Real.log_nonneg hH]
  have hheight : ∀ g ∈ E, modularMk (g * diagonalFlow 0) ∉ modularCusp (Y * H) := by
    intro g hg
    simpa only [diagonalFlow_zero, mul_one] using not_cusp_before_log_buffer g hH (hentry g hg)
  have hreturn : ∀ g ∈ E,
      HasReturningVector (L + 4 * Real.log H) (((Y * H) ^ 2)⁻¹) (g * diagonalFlow 0) := by
    intro g hg
    simpa only [diagonalFlow_zero, mul_one] using
      initial_buffered_cusp_hasReturningVector g hH hL (hentry g hg) (hcusp g hg)
  have h := hrefine (Y * H) 0 (L + 4 * Real.log H) hYH le_rfl hT E hE hheight hreturn
  simpa only [zero_add] using h

end Erdos1148.DukeArithmetic
