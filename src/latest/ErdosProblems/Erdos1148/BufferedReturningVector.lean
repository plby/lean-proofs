import ErdosProblems.Erdos1148.BufferedExcursionCompact
import ErdosProblems.Erdos1148.ReturningVectors

/-! # The returning vector associated with an extended cusp excursion -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups

theorem buffered_excursion_hasReturningVector (g : SL(2, ℝ)) {H L : ℝ}
    (hH : 1 ≤ H) (hL : 1 ≤ L)
    (hcusp : ∀ t ∈ Set.Icc 0 L, modularMk (g * diagonalFlow t) ∈ modularCusp H)
    (hbefore : modularMk (g * diagonalFlow (-1)) ∉ modularCusp H) :
    HasReturningVector (L + 4 * Real.log H) cuspEndpointLengthSqLower
      (g * diagonalFlow (-(2 * Real.log H))) := by
  obtain ⟨u, v, huv, hshort, hleft, hright⟩ :=
    exists_buffered_primitive_cusp_vector g hH (by linarith : (0 : ℝ) ≤ L) hcusp
  have hHpos : 0 < H := by linarith
  have hprev : (H ^ 2)⁻¹ ≤ modularVectorLengthSq (g * diagonalFlow (-1)) u v := by
    apply le_of_not_gt
    intro h
    exact hbefore ((mem_modularCusp_iff_primitive _ H).mpr ⟨u, v, huv, h⟩)
  have hlower := buffered_initial_vector_lengthSq_lower g hHpos hL u v hprev
    (hshort L ⟨by linarith, le_rfl⟩).le
  refine ⟨(u, v), hlower, ?_, ?_⟩
  · simpa only [zero_sub] using hleft.le
  · rw [mul_assoc, ← diagonalFlow_add,
      show -(2 * Real.log H) + (L + 4 * Real.log H) = L + 2 * Real.log H by ring]
    exact hright.le

end Erdos1148.DukeArithmetic
