import StackExchange.Puzzling139335.Definitions
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Order.UpperLower

/-!
# Euclidean measure of the unit square

The coordinate map from the Euclidean plane to `Fin 2 → ℝ` is both a
homeomorphism and volume preserving.  Thus the product-measure calculation
below computes the actual Euclidean volume of the square.
-/

open Set MeasureTheory

namespace Puzzling139335

theorem isClosed_unitSquare : IsClosed unitSquare := by
  exact (isClosed_Icc.preimage (PiLp.continuous_apply 2 _ 0)).inter
    (isClosed_Icc.preimage (PiLp.continuous_apply 2 _ 1))

theorem measurableSet_unitSquare : MeasurableSet unitSquare :=
  isClosed_unitSquare.measurableSet

private theorem unitSquare_eq_preimage_Icc :
    unitSquare = (PiLp.homeomorph 2 (fun _ : Fin 2 => ℝ)) ⁻¹'
      Icc (0 : Fin 2 → ℝ) 1 := by
  ext p
  change ((0 ≤ p 0 ∧ p 0 ≤ 1) ∧ (0 ≤ p 1 ∧ p 1 ≤ 1)) ↔
    ((∀ i, 0 ≤ p i) ∧ (∀ i, p i ≤ 1))
  simp only [Fin.forall_fin_two]
  tauto

/-- The closed unit square has unit Euclidean area. -/
theorem volume_unitSquare : volume unitSquare = 1 := by
  rw [unitSquare_eq_preimage_Icc]
  change volume (WithLp.ofLp ⁻¹' Icc (0 : Fin 2 → ℝ) 1) = 1
  rw [(PiLp.volume_preserving_ofLp (Fin 2)).measure_preimage
    measurableSet_Icc.nullMeasurableSet]
  simp [Real.volume_Icc_pi]

/-- The four sides of the square have zero Euclidean area. -/
theorem volume_frontier_unitSquare : volume (frontier unitSquare) = 0 := by
  rw [unitSquare_eq_preimage_Icc,
    ← (PiLp.homeomorph 2 (fun _ : Fin 2 => ℝ)).preimage_frontier]
  change volume (WithLp.ofLp ⁻¹' frontier (Icc (0 : Fin 2 → ℝ) 1)) = 0
  rw [(PiLp.volume_preserving_ofLp (Fin 2)).measure_preimage
    isClosed_frontier.measurableSet.nullMeasurableSet]
  exact ordConnected_Icc.null_frontier

end Puzzling139335
