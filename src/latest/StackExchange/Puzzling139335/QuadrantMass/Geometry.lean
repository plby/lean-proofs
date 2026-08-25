import StackExchange.Puzzling139335.Definitions
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Order.UpperLower

/-!
# Geometry and measure of the upper-left quarter

The quarter and the horizontal split through the center are defined using
Euclidean coordinates.  Product-volume calculations are transferred through
the volume-preserving coordinate homeomorphism.
-/

open Set MeasureTheory
open scoped ENNReal

namespace Puzzling139335

/-- The closed upper-left quarter of the unit square. -/
def upperLeftQuarter : Set Plane :=
  {p | p 0 ∈ Icc (0 : ℝ) (1 / 2) ∧ p 1 ∈ Icc (1 / 2 : ℝ) 1}

theorem isClosed_upperLeftQuarter : IsClosed upperLeftQuarter := by
  exact (isClosed_Icc.preimage (PiLp.continuous_apply 2 _ 0)).inter
    (isClosed_Icc.preimage (PiLp.continuous_apply 2 _ 1))

theorem measurableSet_upperLeftQuarter : MeasurableSet upperLeftQuarter :=
  isClosed_upperLeftQuarter.measurableSet

private theorem upperLeftQuarter_eq_preimage_Icc :
    upperLeftQuarter = (PiLp.homeomorph 2 (fun _ : Fin 2 => ℝ)) ⁻¹'
      Icc ![0, 1 / 2] ![1 / 2, 1] := by
  ext p
  change ((0 ≤ p 0 ∧ p 0 ≤ 1 / 2) ∧ (1 / 2 ≤ p 1 ∧ p 1 ≤ 1)) ↔
    ((∀ i, ![0, (1 / 2 : ℝ)] i ≤ p i) ∧
      (∀ i, p i ≤ ![(1 / 2 : ℝ), 1] i))
  simp only [Fin.forall_fin_two]
  tauto

theorem volume_upperLeftQuarter : volume upperLeftQuarter = (1 / 4 : ℝ≥0∞) := by
  rw [upperLeftQuarter_eq_preimage_Icc]
  change volume (WithLp.ofLp ⁻¹' Icc (![0, 1 / 2] : Fin 2 → ℝ) ![1 / 2, 1]) = _
  rw [(PiLp.volume_preserving_ofLp (Fin 2)).measure_preimage
    measurableSet_Icc.nullMeasurableSet]
  norm_num [Real.volume_Icc_pi, Fin.prod_univ_two,
    ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
  rw [← ENNReal.mul_inv (a := 2) (b := 2) (by simp) (by simp)]
  norm_num

theorem volume_upperLeftQuarter_ofReal :
    volume upperLeftQuarter = ENNReal.ofReal (1 / 4 : ℝ) := by
  rw [volume_upperLeftQuarter]
  norm_num [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 4)]

theorem volume_frontier_upperLeftQuarter : volume (frontier upperLeftQuarter) = 0 := by
  rw [upperLeftQuarter_eq_preimage_Icc,
    ← (PiLp.homeomorph 2 (fun _ : Fin 2 => ℝ)).preimage_frontier]
  change volume (WithLp.ofLp ⁻¹'
    frontier (Icc (![0, 1 / 2] : Fin 2 → ℝ) ![1 / 2, 1])) = 0
  rw [(PiLp.volume_preserving_ofLp (Fin 2)).measure_preimage
    isClosed_frontier.measurableSet.nullMeasurableSet]
  exact ordConnected_Icc.null_frontier

theorem mem_interior_upperLeftQuarter_iff (p : Plane) :
    p ∈ interior upperLeftQuarter ↔
      p 0 ∈ Ioo (0 : ℝ) (1 / 2) ∧ p 1 ∈ Ioo (1 / 2 : ℝ) 1 := by
  rw [upperLeftQuarter_eq_preimage_Icc,
    ← (PiLp.homeomorph 2 (fun _ : Fin 2 => ℝ)).preimage_interior,
    ← pi_univ_Icc, interior_pi_set Set.finite_univ]
  simp only [mem_preimage, mem_pi, mem_univ, true_implies, interior_Icc, mem_Ioo,
    Fin.forall_fin_two]
  rfl

theorem closure_interior_upperLeftQuarter :
    closure (interior upperLeftQuarter) = upperLeftQuarter := by
  rw [upperLeftQuarter_eq_preimage_Icc,
    ← (PiLp.homeomorph 2 (fun _ : Fin 2 => ℝ)).preimage_interior,
    ← (PiLp.homeomorph 2 (fun _ : Fin 2 => ℝ)).preimage_closure]
  congr 1
  rw [← pi_univ_Icc, interior_pi_set Set.finite_univ, closure_pi_set]
  apply Set.pi_congr rfl
  intro i hi
  fin_cases i <;> norm_num [interior_Icc, closure_Ioo]

theorem squareCenter_mem_upperLeftQuarter : squareCenter ∈ upperLeftQuarter := by
  norm_num [upperLeftQuarter, squareCenter]

theorem squareCenter_mem_closure_interior_upperLeftQuarter :
    squareCenter ∈ closure (interior upperLeftQuarter) := by
  rw [closure_interior_upperLeftQuarter]
  exact squareCenter_mem_upperLeftQuarter

theorem upperLeftQuarter_subset_unitSquare : upperLeftQuarter ⊆ unitSquare := by
  intro p hp
  exact ⟨⟨hp.1.1, hp.1.2.trans (by norm_num)⟩,
    ⟨(by norm_num : (0 : ℝ) ≤ 1 / 2).trans hp.2.1, hp.2.2⟩⟩

/-- The closed half-plane at or above the horizontal midline. -/
def upperHalfPlane : Set Plane := {p | (1 / 2 : ℝ) ≤ p 1}

/-- The open half-plane strictly below the horizontal midline. -/
def lowerHalfPlane : Set Plane := {p | p 1 < (1 / 2 : ℝ)}

theorem isClosed_upperHalfPlane : IsClosed upperHalfPlane :=
  isClosed_le continuous_const (PiLp.continuous_apply 2 _ 1)

theorem isOpen_lowerHalfPlane : IsOpen lowerHalfPlane :=
  isOpen_lt (PiLp.continuous_apply 2 _ 1) continuous_const

theorem measurableSet_upperHalfPlane : MeasurableSet upperHalfPlane :=
  isClosed_upperHalfPlane.measurableSet

theorem measurableSet_lowerHalfPlane : MeasurableSet lowerHalfPlane :=
  isOpen_lowerHalfPlane.measurableSet

theorem upperHalfPlane_compl : upperHalfPlaneᶜ = lowerHalfPlane := by
  ext p
  simp [upperHalfPlane, lowerHalfPlane]

/-- Every full horizontal line has zero Euclidean area. -/
theorem volume_horizontalLine (c : ℝ) : volume {p : Plane | p 1 = c} = 0 := by
  let A : Set (Fin 2 → ℝ) := univ.pi (fun i => if i = 0 then univ else {c})
  have hA : MeasurableSet A := by
    apply MeasurableSet.univ_pi
    intro i
    by_cases hi : i = 0 <;> simp [hi]
  have hline : {p : Plane | p 1 = c} = WithLp.ofLp ⁻¹' A := by
    ext p
    simp [A, Fin.forall_fin_two]
  rw [hline, (PiLp.volume_preserving_ofLp (Fin 2)).measure_preimage hA.nullMeasurableSet]
  simp [A, volume_pi_pi, Fin.prod_univ_two]

end Puzzling139335
