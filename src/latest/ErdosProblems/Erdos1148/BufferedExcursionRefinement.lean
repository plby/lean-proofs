import ErdosProblems.Erdos1148.BufferedReturningVector
import ErdosProblems.Erdos1148.ReturningLiftRefinement

/-! # Uniform coherent refinements through logarithmically extended cusp excursions -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups

def BufferedCuspExcursion (H L : ℝ) (g : SL(2, ℝ)) : Prop :=
  let entry := g * diagonalFlow (2 * Real.log H)
  (∀ t ∈ Set.Icc 0 L, modularMk (entry * diagonalFlow t) ∈ modularCusp H) ∧
    modularMk (entry * diagonalFlow (-1)) ∉ modularCusp H ∧
    modularMk (entry * diagonalFlow (L + 1)) ∉ modularCusp H

theorem BufferedCuspExcursion.mem_compactCore {H L : ℝ} {g : SL(2, ℝ)}
    (hg : BufferedCuspExcursion H L g) (hH : 1 ≤ H) (hL : 1 ≤ L) :
    modularMk g ∈ modularCompactCore cuspEndpointHeight := by
  have h := (buffered_excursion_endpoints_mem_compactCore
    (g * diagonalFlow (2 * Real.log H)) hH hL hg.1 hg.2.1 hg.2.2).1
  simpa only [mul_assoc, ← diagonalFlow_add, add_neg_cancel, diagonalFlow_zero, mul_one] using h

theorem BufferedCuspExcursion.hasReturningVector {H L : ℝ} {g : SL(2, ℝ)}
    (hg : BufferedCuspExcursion H L g) (hH : 1 ≤ H) (hL : 1 ≤ L) :
    HasReturningVector (L + 4 * Real.log H) cuspEndpointLengthSqLower g := by
  have h := buffered_excursion_hasReturningVector
    (g * diagonalFlow (2 * Real.log H)) hH hL hg.1 hg.2.1
  simpa only [mul_assoc, ← diagonalFlow_add, add_neg_cancel, diagonalFlow_zero, mul_one] using h

theorem exists_buffered_excursion_lift_refinement {η : ℝ}
    (hηpos : 0 < η) (hη : η ≤ 1 / 2) :
    ∃ K : ℝ, 0 < K ∧ ∀ {S H L : ℝ}, 0 ≤ S → 1 ≤ H → 1 ≤ L →
      96 * Real.exp (-(L + 4 * Real.log H)) ≤ cuspEndpointLengthSqLower →
      ∀ E : Set SL(2, ℝ), LiftForwardClose η S E →
      (∀ g ∈ E, BufferedCuspExcursion H L (g * diagonalFlow S)) →
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
