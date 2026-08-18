/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.ConvexDensity.GraphWindowVolume
import ErdosProblems.Erdos186.PZ.ConvexDensity.Thickening

/-! # Uniform thickening cost for one normalized graph cell -/

open Set MeasureTheory
open scoped ENNReal BigOperators

namespace Erdos186.PZ.ConvexDensity

set_option autoImplicit false
noncomputable section

/-- Real upper cost after thickening a graph slab over one side-`1/m`
cell and multiplying by the physical graph-window reference volume. -/
def graphThickeningCost (n : ℕ)
    (q outer m epsilon r slope : ℝ) : ℝ :=
  (3 / m) ^ n *
    (2 * (epsilon + r * (1 + (n : ℝ) * slope))) *
    ((2 * q) ^ n * outer)

theorem graphThickeningCost_nonneg {n : ℕ}
    {q outer m epsilon r slope : ℝ}
    (hq : 0 ≤ q) (houter : 0 ≤ outer) (hm : 0 < m)
    (hepsilon : 0 ≤ epsilon) (hr : 0 ≤ r) (hslope : 0 ≤ slope) :
    0 ≤ graphThickeningCost n q outer m epsilon r slope := by
  simp only [graphThickeningCost]
  positivity

/-- Product-form thickening estimate specialized to a genuine unit grid
cell.  The coefficient bound is uniform in every coordinate. -/
theorem volume_graphCell_thickening_mul_reference_le
    {n : ℕ} {q outer m epsilon r slope : ℝ}
    (hq : 0 ≤ q) (houter : 0 ≤ outer) (hm : 0 < m)
    (hepsilon : 0 ≤ epsilon) (hr : 0 ≤ r) (hslope : 0 ≤ slope)
    (hrcell : r ≤ 1 / m)
    (lower : Fin n → ℝ)
    (L : EuclideanPoint n →ᵃ[ℝ] ℝ)
    (hcoeff : ∀ i, |affineCoordinateCoefficient L i| ≤ slope) :
    volume (minkowskiClosedBall
        (affineGraphSlab
          (closedAxisBox lower (fun i ↦ lower i + 1 / m)) L epsilon) r) *
        ENNReal.ofReal ((2 * q) ^ n * outer) ≤
      ENNReal.ofReal (graphThickeningCost n q outer m epsilon r slope) := by
  let upper : Fin n → ℝ := fun i ↦ lower i + 1 / m
  let slopes : Fin n → ℝ := fun _ ↦ slope
  have hordered : lower ≤ upper := by
    intro i
    dsimp only [upper]
    linarith [one_div_pos.mpr hm]
  have hcontrol : ∀ i, r ≤ (1 : ℝ) * (upper i - lower i) := by
    intro i
    dsimp only [upper]
    simpa using hrcell
  have hslopes : ∀ i, 0 ≤ slopes i := fun _ ↦ hslope
  have hcoeff' : ∀ i, |affineCoordinateCoefficient L i| ≤ slopes i := hcoeff
  have hbound := volume_minkowskiClosedBall_affineGraphSlab_le_of_controlledRadius
    (lower := lower) (upper := upper) L slopes hepsilon hr
    (by norm_num : (0 : ℝ) ≤ 1)
    hordered hcontrol hslopes hcoeff'
  have hheight :
      epsilon + r * (1 + ∑ i, slopes i) =
        epsilon + r * (1 + (n : ℝ) * slope) := by
    simp [slopes, Finset.sum_const, nsmul_eq_mul]
  have hbase :
      (∏ i, ENNReal.ofReal
        ((1 + 2 * (1 : ℝ)) * (upper i - lower i))) =
        ENNReal.ofReal ((3 / m) ^ n) := by
    simp only [upper, add_sub_cancel_left, one_mul, OfNat.ofNat]
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [← ENNReal.ofReal_pow (by positivity) n]
    congr 1
    field_simp
    ring
  calc
    volume (minkowskiClosedBall
        (affineGraphSlab
          (closedAxisBox lower (fun i ↦ lower i + 1 / m)) L epsilon) r) *
          ENNReal.ofReal ((2 * q) ^ n * outer)
        ≤ ((∏ i, ENNReal.ofReal
              ((1 + 2 * (1 : ℝ)) * (upper i - lower i))) *
            ENNReal.ofReal (2 * (epsilon + r * (1 + ∑ i, slopes i)))) *
          ENNReal.ofReal ((2 * q) ^ n * outer) := by
            gcongr
    _ = ENNReal.ofReal (graphThickeningCost n q outer m epsilon r slope) := by
      rw [hbase, hheight]
      rw [← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul (by positivity)]
      rfl

end
end Erdos186.PZ.ConvexDensity
