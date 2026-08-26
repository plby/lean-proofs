import ErdosProblems.Erdos1148.BufferedVectorLowerBounds
import ErdosProblems.Erdos1148.PrimitiveVectorCuspBound
import ErdosProblems.Erdos1148.ModularCompactCore

/-! # Logarithmically extended cusp excursions have endpoints in one fixed compact core -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups

noncomputable def cuspEndpointHeight : ℝ := (Real.sqrt cuspEndpointLengthSqLower)⁻¹

lemma cuspEndpointHeight_pos : 0 < cuspEndpointHeight :=
  inv_pos.mpr (Real.sqrt_pos.mpr cuspEndpointLengthSqLower_pos)

lemma cuspEndpointHeight_inv_sq : (cuspEndpointHeight ^ 2)⁻¹ = cuspEndpointLengthSqLower := by
  rw [cuspEndpointHeight, inv_pow, inv_inv, Real.sq_sqrt cuspEndpointLengthSqLower_pos.le]

theorem buffered_excursion_endpoints_not_cusp (g : SL(2, ℝ)) {H L : ℝ}
    (hH : 1 ≤ H) (hL : 1 ≤ L)
    (hcusp : ∀ t ∈ Set.Icc 0 L, modularMk (g * diagonalFlow t) ∈ modularCusp H)
    (hbefore : modularMk (g * diagonalFlow (-1)) ∉ modularCusp H)
    (hafter : modularMk (g * diagonalFlow (L + 1)) ∉ modularCusp H) :
    modularMk (g * diagonalFlow (-(2 * Real.log H))) ∉ modularCusp cuspEndpointHeight ∧
      modularMk (g * diagonalFlow (L + 2 * Real.log H)) ∉ modularCusp cuspEndpointHeight := by
  obtain ⟨u, v, huv, hshort, hleft, hright⟩ :=
    exists_buffered_primitive_cusp_vector g hH (by linarith : (0 : ℝ) ≤ L) hcusp
  have hHpos : 0 < H := by linarith
  have hprev : (H ^ 2)⁻¹ ≤ modularVectorLengthSq (g * diagonalFlow (-1)) u v := by
    apply le_of_not_gt
    intro h
    exact hbefore ((mem_modularCusp_iff_primitive _ H).mpr ⟨u, v, huv, h⟩)
  have hnext : (H ^ 2)⁻¹ ≤ modularVectorLengthSq (g * diagonalFlow (L + 1)) u v := by
    apply le_of_not_gt
    intro h
    exact hafter ((mem_modularCusp_iff_primitive _ H).mpr ⟨u, v, huv, h⟩)
  have hleftLower := buffered_initial_vector_lengthSq_lower g hHpos hL u v hprev
    (hshort L ⟨by linarith, le_rfl⟩).le
  have hrightLower : cuspEndpointLengthSqLower ≤
      modularVectorLengthSq (g * diagonalFlow (L + 2 * Real.log H)) u v := by
    have hnext' : (H ^ 2)⁻¹ ≤ modularVectorLengthSq ((g * diagonalFlow L) * diagonalFlow 1) u v := by
      rwa [mul_assoc, ← diagonalFlow_add]
    have hzero : modularVectorLengthSq ((g * diagonalFlow L) * diagonalFlow (-L)) u v ≤
        (H ^ 2)⁻¹ := by
      simpa only [mul_assoc, ← diagonalFlow_add, add_neg_cancel] using (hshort 0 ⟨le_rfl, by linarith⟩).le
    have h := buffered_terminal_vector_lengthSq_lower (g * diagonalFlow L) hHpos hL u v hnext' hzero
    simpa only [mul_assoc, ← diagonalFlow_add] using h
  constructor
  · apply not_mem_cusp_of_primitive_lengthSq_bounds _ huv hleftLower
      (by simpa only [zero_sub] using hleft.le)
    exact cuspEndpointHeight_inv_sq.le
  · exact not_mem_cusp_of_primitive_lengthSq_bounds _ huv hrightLower hright.le
      cuspEndpointHeight_inv_sq.le

theorem buffered_excursion_endpoints_mem_compactCore (g : SL(2, ℝ)) {H L : ℝ}
    (hH : 1 ≤ H) (hL : 1 ≤ L)
    (hcusp : ∀ t ∈ Set.Icc 0 L, modularMk (g * diagonalFlow t) ∈ modularCusp H)
    (hbefore : modularMk (g * diagonalFlow (-1)) ∉ modularCusp H)
    (hafter : modularMk (g * diagonalFlow (L + 1)) ∉ modularCusp H) :
    modularMk (g * diagonalFlow (-(2 * Real.log H))) ∈ modularCompactCore cuspEndpointHeight ∧
      modularMk (g * diagonalFlow (L + 2 * Real.log H)) ∈ modularCompactCore cuspEndpointHeight := by
  have h := buffered_excursion_endpoints_not_cusp g hH hL hcusp hbefore hafter
  exact ⟨modularCusp_compl_subset_compactCore cuspEndpointHeight_pos h.1,
    modularCusp_compl_subset_compactCore cuspEndpointHeight_pos h.2⟩

end Erdos1148.DukeArithmetic
