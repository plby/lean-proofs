/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.ConvexDensity.ConvexHullClip
import ErdosProblems.Erdos186.PZ.ConvexDensity.GraphSlabAmbient
import ErdosProblems.Erdos186.PZ.ConvexDensity.GridPartition
import ErdosProblems.Erdos186.PZ.ConvexDensity.HouseholderCap
import ErdosProblems.Erdos186.PZ.ConvexDensity.Thickening

/-!
# Retaining labelled grid fibres near a product slab

The boundary-cap and graph-density parts of the Pham--Zakharov argument select
*labels* of heavy cells.  Equal geometric boundary witnesses must not be
deduplicated.  This file supplies the exact end-to-end bookkeeping bridge:
take the disjoint union of the original assignment fibres, place it in the
inverse image of a thickened product region, preserve its exact cardinality,
and invoke convex-hull clipping.
-/

open Set MeasureTheory
open scoped ENNReal BigOperators Pointwise

namespace Erdos186.PZ.ConvexDensity

set_option autoImplicit false

noncomputable section

/-- The union of the original point fibres carrying the selected labels. -/
def retainedFiberUnion {ι E : Type*} [DecidableEq ι] [DecidableEq E]
    (J : Finset ι) (Y : ι → Finset E) : Finset E :=
  J.biUnion Y

@[simp]
theorem mem_retainedFiberUnion {ι E : Type*} [DecidableEq ι] [DecidableEq E]
    {J : Finset ι} {Y : ι → Finset E} {x : E} :
    x ∈ retainedFiberUnion J Y ↔ ∃ i ∈ J, x ∈ Y i := by
  simp [retainedFiberUnion]

/-- Disjoint assignment fibres lose no mass when their selected labels are
united. -/
theorem card_retainedFiberUnion {ι E : Type*} [DecidableEq ι] [DecidableEq E]
    {J : Finset ι} {Y : ι → Finset E}
    (hdisjoint : (J : Set ι).PairwiseDisjoint Y) :
    (retainedFiberUnion J Y).card = ∑ i ∈ J, (Y i).card := by
  simpa [retainedFiberUnion] using Finset.card_biUnion hdisjoint

/-- If every selected fibre is a subfinset of `X`, so is their union. -/
theorem retainedFiberUnion_subset {ι E : Type*} [DecidableEq ι] [DecidableEq E]
    {J : Finset ι} {Y : ι → Finset E} {X : Finset E}
    (hYX : ∀ i ∈ J, Y i ⊆ X) :
    retainedFiberUnion J Y ⊆ X := by
  intro x hx
  obtain ⟨i, hiJ, hxi⟩ := mem_retainedFiberUnion.mp hx
  exact hYX i hiJ hxi

/-- The inverse image, under the last-coordinate split, of a thickened
product region.  This choice keeps the product-volume estimate literal. -/
def ambientProductThickening (n : ℕ)
    (W : Set (EuclideanPoint n × ℝ)) (r : ℝ) :
    Set (EuclideanPoint (n + 1)) :=
  (lastCoordinateCLE n).symm '' minkowskiClosedBall W r

theorem convex_ambientProductThickening {n : ℕ}
    {W : Set (EuclideanPoint n × ℝ)} (r : ℝ) (hW : Convex ℝ W) :
    Convex ℝ (ambientProductThickening n W r) := by
  exact (hW.add (convex_closedBall (0 : EuclideanPoint n × ℝ) r)).linear_image
    (lastCoordinateCLE n).symm.toContinuousLinearEquiv.toLinearMap

theorem volume_ambientProductThickening {n : ℕ}
    (W : Set (EuclideanPoint n × ℝ)) (r : ℝ) :
    volume (ambientProductThickening n W r) =
      volume (minkowskiClosedBall W r) := by
  exact volume_lastCoordinateCLE_symm_image n (minkowskiClosedBall W r)

/-- The last-coordinate split is `1`-Lipschitz from Euclidean `l2` space to
Mathlib's max-norm product. -/
theorem norm_lastCoordinateCLE_le {n : ℕ}
    (z : EuclideanPoint (n + 1)) :
    ‖lastCoordinateCLE n z‖ ≤ ‖z‖ := by
  rw [lastCoordinateCLE_apply, Prod.norm_def]
  exact max_le (norm_baseCoordinates_le_norm z)
    (by simpa [Real.norm_eq_abs] using abs_lastCoordinate_le_norm z)

/-- A point lying within distance `r` of a witness in `W` belongs to the
ambient lift of the radius-`r` product thickening of `W`. -/
theorem mem_ambientProductThickening_of_dist_le {n : ℕ}
    {W : Set (EuclideanPoint n × ℝ)} {r : ℝ}
    {w z : EuclideanPoint (n + 1)}
    (hw : lastCoordinateCLE n w ∈ W) (hzw : dist z w ≤ r) :
    z ∈ ambientProductThickening n W r := by
  let a := lastCoordinateCLE n w
  let b := lastCoordinateCLE n (z - w)
  have hbNorm : ‖b‖ ≤ r := by
    calc
      ‖b‖ ≤ ‖z - w‖ := norm_lastCoordinateCLE_le (z - w)
      _ = dist z w := by rw [dist_eq_norm]
      _ ≤ r := hzw
  have hbBall : b ∈ Metric.closedBall (0 : EuclideanPoint n × ℝ) r := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hbNorm
  have hab : a + b = lastCoordinateCLE n z := by
    dsimp [a, b]
    rw [map_sub]
    module
  refine ⟨lastCoordinateCLE n z, ?_, (lastCoordinateCLE n).symm_apply_apply z⟩
  exact ⟨a, hw, b, hbBall, hab⟩

/-- All points in selected labelled fibres lie in the lifted thickening when
their corresponding witnesses lie in the central product region. -/
theorem retainedFiberUnion_subset_ambientProductThickening
    {ι : Type*} [DecidableEq ι] {n : ℕ}
    {J : Finset ι} {Y : ι → Finset (EuclideanPoint (n + 1))}
    {witness : ι → EuclideanPoint (n + 1)}
    {W : Set (EuclideanPoint n × ℝ)} {r : ℝ}
    (hwitness : ∀ i ∈ J, lastCoordinateCLE n (witness i) ∈ W)
    (hnear : ∀ i ∈ J, ∀ z ∈ Y i, dist z (witness i) ≤ r) :
    (retainedFiberUnion J Y : Set (EuclideanPoint (n + 1))) ⊆
      ambientProductThickening n W r := by
  intro z hz
  obtain ⟨i, hiJ, hzi⟩ := mem_retainedFiberUnion.mp hz
  exact mem_ambientProductThickening_of_dist_le
    (hwitness i hiJ) (hnear i hiJ z hzi)

/-- Complete low-branch output constructor.  It simultaneously preserves
the mass of labelled disjoint grid fibres, transports the product thickening
back to ambient Euclidean space without volume loss, and clips by the convex
hull of the retained original points. -/
theorem convexDensityOutput_of_disjoint_fibers_in_product_thickening
    {ι : Type*} [DecidableEq ι] {n : ℕ}
    {epsilon tau delta eta r : ℝ}
    {Omega : Set (EuclideanPoint (n + 1))}
    {X : Finset (EuclideanPoint (n + 1))}
    {J : Finset ι} {Y : ι → Finset (EuclideanPoint (n + 1))}
    {witness : ι → EuclideanPoint (n + 1)}
    {W : Set (EuclideanPoint n × ℝ)}
    (hEta : eta ∈ Set.Icc delta (delta ^ tau))
    (hOmega : IsConvexBody Omega)
    (hXOmega : (X : Set (EuclideanPoint (n + 1))) ⊆ Omega)
    (hYX : ∀ i ∈ J, Y i ⊆ X)
    (hdisjoint : (J : Set ι).PairwiseDisjoint Y)
    (hW : Convex ℝ W)
    (hwitness : ∀ i ∈ J, lastCoordinateCLE n (witness i) ∈ W)
    (hnear : ∀ i ∈ J, ∀ z ∈ Y i, dist z (witness i) ≤ r)
    (hVolume : volume (minkowskiClosedBall W r) ≤
      ENNReal.ofReal eta * volume Omega)
    (hCard : eta ^ densityExponent (n + 1) epsilon * (X.card : ℝ) ≤
      (∑ i ∈ J, (Y i).card : ℕ)) :
    ConvexDensityOutput epsilon tau delta Omega X := by
  let T := retainedFiberUnion J Y
  let S := ambientProductThickening n W r
  apply convexDensityOutput_of_retainedConvexHull hEta hOmega hXOmega
      (T := T) (S := S)
  · exact retainedFiberUnion_subset hYX
  · exact convex_ambientProductThickening r hW
  · exact retainedFiberUnion_subset_ambientProductThickening hwitness hnear
  · rw [show S = ambientProductThickening n W r by rfl,
      volume_ambientProductThickening]
    exact hVolume
  · rw [show T = retainedFiberUnion J Y by rfl,
      card_retainedFiberUnion hdisjoint]
    exact hCard

/-! ## Specialization to the normalized axis-grid assignment -/

/-- The points of `X` assigned to a particular normalized grid cell. -/
def gridAssignmentFiberFinset {d : ℕ}
    (X : Finset (EuclideanPoint d)) (mesh : ℝ) (k : Fin d → ℕ) :
    Finset (EuclideanPoint d) :=
  X.filter fun z ↦ GridPartition.gridIndex mesh z = k

@[simp]
theorem mem_gridAssignmentFiberFinset_iff {d : ℕ}
    {X : Finset (EuclideanPoint d)} {mesh : ℝ} {k : Fin d → ℕ}
    {z : EuclideanPoint d} :
    z ∈ gridAssignmentFiberFinset X mesh k ↔
      z ∈ X ∧ GridPartition.gridIndex mesh z = k := by
  simp [gridAssignmentFiberFinset]

theorem card_gridAssignmentFiberFinset {d : ℕ}
    (X : Finset (EuclideanPoint d)) (mesh : ℝ) (k : Fin d → ℕ) :
    (gridAssignmentFiberFinset X mesh k).card =
      DyadicCells.occupancy X (GridPartition.gridIndex mesh) k := by
  rfl

theorem gridAssignmentFiberFinset_subset {d : ℕ}
    (X : Finset (EuclideanPoint d)) (mesh : ℝ) (k : Fin d → ℕ) :
    gridAssignmentFiberFinset X mesh k ⊆ X := by
  exact Finset.filter_subset _ _

/-- Distinct grid labels have disjoint assignment fibres even though their
closed geometric boxes may meet on their boundaries. -/
theorem pairwiseDisjoint_gridAssignmentFiberFinset {d : ℕ}
    (X : Finset (EuclideanPoint d)) (mesh : ℝ)
    (J : Finset (Fin d → ℕ)) :
    (J : Set (Fin d → ℕ)).PairwiseDisjoint
      (gridAssignmentFiberFinset X mesh) := by
  intro i _hi j _hj hij
  change Disjoint (gridAssignmentFiberFinset X mesh i)
    (gridAssignmentFiberFinset X mesh j)
  rw [Finset.disjoint_left]
  intro z hzi hzj
  have hi := (mem_gridAssignmentFiberFinset_iff.mp hzi).2
  have hj := (mem_gridAssignmentFiberFinset_iff.mp hzj).2
  exact hij (hi.symm.trans hj)

/-- Every point in a selected grid assignment fibre is within `4*rho` of a
boundary witness which is within `3*rho` of the cell centre, provided `rho`
dominates the actual half-diagonal of a mesh cell. -/
theorem dist_gridAssignmentFiberFinset_witness_le
    {d : ℕ} {X : Finset (EuclideanPoint d)} {mesh rho : ℝ}
    (hmesh : 0 < mesh)
    (hXcube : (X : Set (EuclideanPoint d)) ⊆
      GridPartition.normalizedCube d)
    (hrho : Real.sqrt (d : ℝ) * (mesh / 2) ≤ rho)
    {k : Fin d → ℕ} {witness z : EuclideanPoint d}
    (hz : z ∈ gridAssignmentFiberFinset X mesh k)
    (hwitness : witness ∈
      Metric.closedBall (GridPartition.gridCenter mesh k) (3 * rho)) :
    dist z witness ≤ 4 * rho := by
  have hzX := (mem_gridAssignmentFiberFinset_iff.mp hz).1
  have hzindex := (mem_gridAssignmentFiberFinset_iff.mp hz).2
  have hzcell : z ∈ GridPartition.gridCell mesh k := by
    simpa [hzindex] using GridPartition.mem_gridCell_gridIndex
      hmesh z (hXcube hzX)
  have hzcenter :
      dist z (GridPartition.gridCenter mesh k) ≤ rho := by
    have hhalf : dist z (GridPartition.gridCenter mesh k) ≤
        Real.sqrt (d : ℝ) * (mesh / 2) := by
      simpa [dist_eq_norm] using
        GridPartition.norm_sub_gridCenter_le hmesh.le hzcell
    exact hhalf.trans hrho
  have hcenterWitness :
      dist (GridPartition.gridCenter mesh k) witness ≤ 3 * rho := by
    simpa [Metric.mem_closedBall, dist_comm] using hwitness
  calc
    dist z witness ≤ dist z (GridPartition.gridCenter mesh k) +
        dist (GridPartition.gridCenter mesh k) witness := dist_triangle _ _ _
    _ ≤ rho + 3 * rho := add_le_add hzcenter hcenterWitness
    _ = 4 * rho := by ring

/-- Ready-to-use output constructor for selected normalized grid cells.  Its
cardinality hypothesis is stated directly with `DyadicCells.occupancy`, the
quantity produced by both relative dyadic decompositions. -/
theorem convexDensityOutput_of_grid_fibers_in_product_thickening
    {n : ℕ} {epsilon tau delta eta mesh rho : ℝ}
    {Omega : Set (EuclideanPoint (n + 1))}
    {X : Finset (EuclideanPoint (n + 1))}
    {J : Finset (Fin (n + 1) → ℕ)}
    {witness : (Fin (n + 1) → ℕ) → EuclideanPoint (n + 1)}
    {W : Set (EuclideanPoint n × ℝ)}
    (hmesh : 0 < mesh)
    (hXcube : (X : Set (EuclideanPoint (n + 1))) ⊆
      GridPartition.normalizedCube (n + 1))
    (hrho : Real.sqrt ((n + 1 : ℕ) : ℝ) * (mesh / 2) ≤ rho)
    (hEta : eta ∈ Set.Icc delta (delta ^ tau))
    (hOmega : IsConvexBody Omega)
    (hXOmega : (X : Set (EuclideanPoint (n + 1))) ⊆ Omega)
    (hW : Convex ℝ W)
    (hwitnessW : ∀ k ∈ J, lastCoordinateCLE n (witness k) ∈ W)
    (hwitnessNear : ∀ k ∈ J, witness k ∈
      Metric.closedBall (GridPartition.gridCenter mesh k) (3 * rho))
    (hVolume : volume (minkowskiClosedBall W (4 * rho)) ≤
      ENNReal.ofReal eta * volume Omega)
    (hCard : eta ^ densityExponent (n + 1) epsilon * (X.card : ℝ) ≤
      (∑ k ∈ J,
        DyadicCells.occupancy X (GridPartition.gridIndex mesh) k : ℕ)) :
    ConvexDensityOutput epsilon tau delta Omega X := by
  apply convexDensityOutput_of_disjoint_fibers_in_product_thickening
      (J := J) (Y := gridAssignmentFiberFinset X mesh)
      (witness := witness) (W := W) (r := 4 * rho)
      hEta hOmega hXOmega
  · intro k _hk
    exact gridAssignmentFiberFinset_subset X mesh k
  · exact pairwiseDisjoint_gridAssignmentFiberFinset X mesh J
  · exact hW
  · exact hwitnessW
  · intro k hk z hz
    exact dist_gridAssignmentFiberFinset_witness_le hmesh hXcube hrho hz
      (hwitnessNear k hk)
  · exact hVolume
  · simpa [card_gridAssignmentFiberFinset] using hCard

end

end Erdos186.PZ.ConvexDensity
