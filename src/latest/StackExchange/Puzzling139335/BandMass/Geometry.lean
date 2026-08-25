import StackExchange.Puzzling139335.Definitions
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Order.UpperLower

/-!
# Horizontal bands in the Euclidean unit square

The geometric and measure computations are transferred through the
volume-preserving coordinate homeomorphism of the Euclidean plane.
-/

open Set MeasureTheory

namespace Puzzling139335

/-- The closed horizontal band of width one between heights `a` and `b`. -/
def horizontalBand (a b : ℝ) : Set Plane :=
  {p | p 0 ∈ Icc (0 : ℝ) 1 ∧ p 1 ∈ Icc a b}

theorem isClosed_horizontalBand (a b : ℝ) : IsClosed (horizontalBand a b) := by
  exact (isClosed_Icc.preimage (PiLp.continuous_apply 2 _ 0)).inter
    (isClosed_Icc.preimage (PiLp.continuous_apply 2 _ 1))

theorem measurableSet_horizontalBand (a b : ℝ) : MeasurableSet (horizontalBand a b) :=
  (isClosed_horizontalBand a b).measurableSet

private theorem horizontalBand_eq_preimage_Icc (a b : ℝ) :
    horizontalBand a b = (PiLp.homeomorph 2 (fun _ : Fin 2 => ℝ)) ⁻¹'
      Icc ![0, a] ![1, b] := by
  ext p
  change ((0 ≤ p 0 ∧ p 0 ≤ 1) ∧ (a ≤ p 1 ∧ p 1 ≤ b)) ↔
    ((∀ i, ![0, a] i ≤ p i) ∧ (∀ i, p i ≤ ![1, b] i))
  simp only [Fin.forall_fin_two]
  tauto

/-- The formula also covers empty or degenerate bands. -/
theorem volume_horizontalBand (a b : ℝ) :
    volume (horizontalBand a b) = ENNReal.ofReal (b - a) := by
  rw [horizontalBand_eq_preimage_Icc]
  change volume (WithLp.ofLp ⁻¹' Icc (![0, a] : Fin 2 → ℝ) ![1, b]) = _
  rw [(PiLp.volume_preserving_ofLp (Fin 2)).measure_preimage
    measurableSet_Icc.nullMeasurableSet]
  simp [Real.volume_Icc_pi, Fin.prod_univ_two]

theorem volume_frontier_horizontalBand (a b : ℝ) :
    volume (frontier (horizontalBand a b)) = 0 := by
  rw [horizontalBand_eq_preimage_Icc,
    ← (PiLp.homeomorph 2 (fun _ : Fin 2 => ℝ)).preimage_frontier]
  change volume (WithLp.ofLp ⁻¹' frontier (Icc (![0, a] : Fin 2 → ℝ) ![1, b])) = 0
  rw [(PiLp.volume_preserving_ofLp (Fin 2)).measure_preimage
    isClosed_frontier.measurableSet.nullMeasurableSet]
  exact ordConnected_Icc.null_frontier

/-- A point is interior to the band exactly when both coordinate inequalities
are strict.  This equivalence requires no ordering hypothesis on `a` and `b`. -/
theorem mem_interior_horizontalBand_iff (a b : ℝ) (p : Plane) :
    p ∈ interior (horizontalBand a b) ↔
      p 0 ∈ Ioo (0 : ℝ) 1 ∧ p 1 ∈ Ioo a b := by
  rw [horizontalBand_eq_preimage_Icc,
    ← (PiLp.homeomorph 2 (fun _ : Fin 2 => ℝ)).preimage_interior,
    ← pi_univ_Icc, interior_pi_set Set.finite_univ]
  simp only [mem_preimage, mem_pi, mem_univ, true_implies, interior_Icc, mem_Ioo,
    Fin.forall_fin_two]
  rfl

/-- A band of positive height is regular closed. -/
theorem closure_interior_horizontalBand {a b : ℝ} (hab : a < b) :
    closure (interior (horizontalBand a b)) = horizontalBand a b := by
  rw [horizontalBand_eq_preimage_Icc,
    ← (PiLp.homeomorph 2 (fun _ : Fin 2 => ℝ)).preimage_interior,
    ← (PiLp.homeomorph 2 (fun _ : Fin 2 => ℝ)).preimage_closure]
  congr 1
  rw [← pi_univ_Icc, interior_pi_set Set.finite_univ, closure_pi_set]
  apply Set.pi_congr rfl
  intro i hi
  fin_cases i <;> simp [interior_Icc, closure_Ioo, ne_of_lt hab]

theorem horizontalBand_subset_unitSquare {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) :
    horizontalBand a b ⊆ unitSquare := by
  intro p hp
  exact ⟨hp.1, ha.trans hp.2.1, hp.2.2.trans hb⟩

end Puzzling139335
