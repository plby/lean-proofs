import ErdosProblems.Erdos1148.BufferedReturningVector
import ErdosProblems.Erdos1148.ReturningLiftRefinement

/-! # Only the entry side of an excursion is needed for uniform returning covers -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups

theorem buffered_excursion_initial_not_cusp (g : SL(2, ℝ)) {H L : ℝ}
    (hH : 1 ≤ H) (hL : 1 ≤ L)
    (hcusp : ∀ t ∈ Set.Icc 0 L, modularMk (g * diagonalFlow t) ∈ modularCusp H)
    (hbefore : modularMk (g * diagonalFlow (-1)) ∉ modularCusp H) :
    modularMk (g * diagonalFlow (-(2 * Real.log H))) ∉ modularCusp cuspEndpointHeight := by
  obtain ⟨u, v, huv, hshort, hleft, _⟩ :=
    exists_buffered_primitive_cusp_vector g hH (by linarith : (0 : ℝ) ≤ L) hcusp
  have hprev : (H ^ 2)⁻¹ ≤ modularVectorLengthSq (g * diagonalFlow (-1)) u v := by
    apply le_of_not_gt
    intro h
    exact hbefore ((mem_modularCusp_iff_primitive _ H).mpr ⟨u, v, huv, h⟩)
  have hlower := buffered_initial_vector_lengthSq_lower g (by linarith : 0 < H) hL u v hprev
    (hshort L ⟨by linarith, le_rfl⟩).le
  exact not_mem_cusp_of_primitive_lengthSq_bounds _ huv hlower
    (by simpa only [zero_sub] using hleft.le) cuspEndpointHeight_inv_sq.le

def BufferedCuspEntry (H L : ℝ) (g : SL(2, ℝ)) : Prop :=
  let entry := g * diagonalFlow (2 * Real.log H)
  (∀ t ∈ Set.Icc 0 L, modularMk (entry * diagonalFlow t) ∈ modularCusp H) ∧
    modularMk (entry * diagonalFlow (-1)) ∉ modularCusp H

theorem BufferedCuspEntry.mem_compactCore {H L : ℝ} {g : SL(2, ℝ)}
    (hg : BufferedCuspEntry H L g) (hH : 1 ≤ H) (hL : 1 ≤ L) :
    modularMk g ∈ modularCompactCore cuspEndpointHeight := by
  apply modularCusp_compl_subset_compactCore cuspEndpointHeight_pos
  change modularMk g ∉ modularCusp cuspEndpointHeight
  have h := buffered_excursion_initial_not_cusp
    (g * diagonalFlow (2 * Real.log H)) hH hL hg.1 hg.2
  simpa only [mul_assoc, ← diagonalFlow_add, add_neg_cancel, diagonalFlow_zero, mul_one] using h

theorem BufferedCuspEntry.hasReturningVector {H L : ℝ} {g : SL(2, ℝ)}
    (hg : BufferedCuspEntry H L g) (hH : 1 ≤ H) (hL : 1 ≤ L) :
    HasReturningVector (L + 4 * Real.log H) cuspEndpointLengthSqLower g := by
  have h := buffered_excursion_hasReturningVector
    (g * diagonalFlow (2 * Real.log H)) hH hL hg.1 hg.2
  simpa only [mul_assoc, ← diagonalFlow_add, add_neg_cancel, diagonalFlow_zero, mul_one] using h

theorem exists_buffered_cusp_entry_lift_refinement {η : ℝ}
    (hηpos : 0 < η) (hη : η ≤ 1 / 2) :
    ∃ K : ℝ, 0 < K ∧ ∀ {S H L : ℝ}, 0 ≤ S → 1 ≤ H → 1 ≤ L →
      96 * Real.exp (-(L + 4 * Real.log H)) ≤ cuspEndpointLengthSqLower →
      ∀ E : Set SL(2, ℝ), LiftForwardClose η S E →
      (∀ g ∈ E, BufferedCuspEntry H L (g * diagonalFlow S)) →
      ∃ (N : ℕ) (C : Fin N → Set SL(2, ℝ)),
        (N : ℝ) ≤ K * Real.exp ((L + 4 * Real.log H) / 2) ∧ (⋃ i, C i) = E ∧
        ∀ i, LiftForwardClose η (S + (L + 4 * Real.log H)) (C i) := by
  obtain ⟨K, hK, hrefine⟩ := exists_returning_lift_refinement cuspEndpointHeight
    cuspEndpointLengthSqLower_pos hηpos hη
  refine ⟨K, hK, ?_⟩
  intro S H L hS hH hL hsmall E hE hexc
  have hT : 0 ≤ L + 4 * Real.log H := by linarith [Real.log_nonneg hH]
  exact hrefine hS hT hsmall E hE
    (fun g hg => (hexc g hg).mem_compactCore hH hL)
    (fun g hg => (hexc g hg).hasReturningVector hH hL)

end Erdos1148.DukeArithmetic
