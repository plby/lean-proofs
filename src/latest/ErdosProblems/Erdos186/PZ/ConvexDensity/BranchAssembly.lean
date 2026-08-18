/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.ConvexDensity.GraphScale
import ErdosProblems.Erdos186.PZ.ConvexDensity.GraphWindowAffine
import ErdosProblems.Erdos186.PZ.ConvexDensity.InitialBoundary
import ErdosProblems.Erdos186.PZ.ConvexDensity.InitialRegularization
import ErdosProblems.Erdos186.PZ.ConvexDensity.RetainedFibers
import ErdosProblems.Erdos186.PZ.ConvexDensity.UnitGraphGrid
import ErdosProblems.Erdos186.PZ.ConvexDensity.WidthInradiusQuantitative

/-! # End-to-end branch constructors for the normalized PZ argument -/

open Set MeasureTheory
open scoped ENNReal BigOperators

namespace Erdos186.PZ.ConvexDensity

set_option autoImplicit false
noncomputable section

/-- Full-dimensional convex bodies are preserved by arbitrary invertible
affine charts in finite-dimensional Euclidean space. -/
theorem isConvexBody_affineEquiv_image {d : ℕ}
    (e : EuclideanPoint d ≃ᵃ[ℝ] EuclideanPoint d)
    {Omega : Set (EuclideanPoint d)} (hOmega : IsConvexBody Omega) :
    IsConvexBody (e '' Omega) := by
  let ec := AffineEquiv.toContinuousAffineEquiv e
  refine ⟨(convex_affineEquivImage_iff e Omega).2 hOmega.convex,
    hOmega.isCompact.image ec.continuous, ?_⟩
  obtain ⟨x, hx⟩ := hOmega.interior_nonempty
  refine ⟨ec x, ?_⟩
  exact ec.toHomeomorph.isOpenMap.image_interior_subset Omega ⟨x, hx, rfl⟩

/-- The common hull of a first-grid shell contains the union of its actual
assignment fibres. -/
theorem retainedFiberUnion_subset_commonGridHull {d : ℕ}
    (X : Finset (EuclideanPoint d)) (mesh : ℝ)
    (J : Finset (Fin d → ℕ)) :
    (retainedFiberUnion J (gridAssignmentFiberFinset X mesh) :
        Set (EuclideanPoint d)) ⊆
      commonCellHull J (fun k ↦
        (gridAssignmentFiberFinset X mesh k : Set (EuclideanPoint d))) := by
  intro x hx
  apply subset_convexHull ℝ
  rw [mem_retainedCells_iff]
  exact mem_retainedFiberUnion.mp hx

/-- The small-common-hull branch, with no loss from label collisions. -/
theorem convexDensityOutput_of_small_commonGridHull
    {d : ℕ} {epsilon tau delta eta mesh : ℝ}
    {Omega : Set (EuclideanPoint d)} {X : Finset (EuclideanPoint d)}
    {J : Finset (Fin d → ℕ)}
    (hEta : eta ∈ Set.Icc delta (delta ^ tau))
    (hOmega : IsConvexBody Omega)
    (hXOmega : (X : Set (EuclideanPoint d)) ⊆ Omega)
    (hVolume : relativeVolume
        (commonCellHull J (fun k ↦
          (gridAssignmentFiberFinset X mesh k : Set (EuclideanPoint d))))
        Omega ≤ ENNReal.ofReal eta)
    (hCard : eta ^ densityExponent d epsilon * (X.card : ℝ) ≤
      (∑ k ∈ J,
        DyadicCells.occupancy X (GridPartition.gridIndex mesh) k : ℕ)) :
    ConvexDensityOutput epsilon tau delta Omega X := by
  let T := retainedFiberUnion J (gridAssignmentFiberFinset X mesh)
  let P := commonCellHull J (fun k ↦
    (gridAssignmentFiberFinset X mesh k : Set (EuclideanPoint d)))
  apply convexDensityOutput_of_retainedConvexHull_relative
      (T := T) (S := P) hEta hOmega hXOmega
  · exact retainedFiberUnion_subset fun k _hk ↦
      gridAssignmentFiberFinset_subset X mesh k
  · exact convex_commonCellHull J fun k ↦
      (gridAssignmentFiberFinset X mesh k : Set (EuclideanPoint d))
  · exact retainedFiberUnion_subset_commonGridHull X mesh J
  · exact hVolume
  · rw [show T = retainedFiberUnion J
        (gridAssignmentFiberFinset X mesh) by rfl,
      card_retainedFiberUnion
        (pairwiseDisjoint_gridAssignmentFiberFinset X mesh J)]
    simpa [card_gridAssignmentFiberFinset] using hCard

/-- Exact structural split after the first dyadic regularization.  The
small-volume branch returns the PZ output; the other branch returns the
quantitative inball needed by the cap and graph steps. -/
theorem convexDensityOutput_or_commonGridHull_inball
    {d : ℕ} (hd : 0 < d)
    {epsilon tau delta eta mesh R v : ℝ}
    {Omega : Set (EuclideanPoint d)} {X : Finset (EuclideanPoint d)}
    {J : Finset (Fin d → ℕ)}
    (hEta : eta ∈ Set.Icc delta (delta ^ tau))
    (hOmega : IsConvexBody Omega)
    (hXOmega : (X : Set (EuclideanPoint d)) ⊆ Omega)
    (hTne : (retainedFiberUnion J
      (gridAssignmentFiberFinset X mesh)).Nonempty)
    (hR : 0 < R) (hv : 0 ≤ v)
    (hball : commonCellHull J (fun k ↦
        (gridAssignmentFiberFinset X mesh k : Set (EuclideanPoint d))) ⊆
      Metric.closedBall 0 R)
    (hbranch :
      relativeVolume
          (commonCellHull J (fun k ↦
            (gridAssignmentFiberFinset X mesh k : Set (EuclideanPoint d))))
          Omega ≤ ENNReal.ofReal eta ∨
        ENNReal.ofReal v ≤ volume
          (commonCellHull J (fun k ↦
            (gridAssignmentFiberFinset X mesh k : Set (EuclideanPoint d)))))
    (hCard : eta ^ densityExponent d epsilon * (X.card : ℝ) ≤
      (∑ k ∈ J,
        DyadicCells.occupancy X (GridPartition.gridIndex mesh) k : ℕ)) :
    ConvexDensityOutput epsilon tau delta Omega X ∨
      ∃ c ∈ commonCellHull J (fun k ↦
          (gridAssignmentFiberFinset X mesh k : Set (EuclideanPoint d))),
        Metric.closedBall c
            ((v / (2 * R) ^ (d - 1)) / (((d + 1 : ℕ) : ℝ))) ⊆
          commonCellHull J (fun k ↦
            (gridAssignmentFiberFinset X mesh k : Set (EuclideanPoint d))) := by
  rcases hbranch with hsmall | hlarge
  · exact Or.inl (convexDensityOutput_of_small_commonGridHull
      hEta hOmega hXOmega hsmall hCard)
  · right
    let P := commonCellHull J (fun k ↦
      (gridAssignmentFiberFinset X mesh k : Set (EuclideanPoint d)))
    have hPne : P.Nonempty := by
      obtain ⟨x, hx⟩ := hTne
      exact ⟨x, retainedFiberUnion_subset_commonGridHull X mesh J hx⟩
    exact exists_closedBall_volume_div_ball_subset hd
      (convex_commonCellHull J fun k ↦
        (gridAssignmentFiberFinset X mesh k : Set (EuclideanPoint d)))
      (isCompact_commonAssignmentFiberHull X J mesh) hPne hR hv hball hlarge

/-- Run the complete retained-fibre constructor after an arbitrary affine
chart and transport its output back.  The labels and their fibre
multiplicities are preserved because the affine equivalence is injective. -/
theorem convexDensityOutput_of_affineChart_disjointFibers
    {ι : Type*} [DecidableEq ι] {n : ℕ}
    {epsilon tau delta eta r : ℝ}
    {Omega : Set (EuclideanPoint (n + 1))}
    {X : Finset (EuclideanPoint (n + 1))}
    {J : Finset ι} {Y : ι → Finset (EuclideanPoint (n + 1))}
    {witness : ι → EuclideanPoint (n + 1)}
    {W : Set (EuclideanPoint n × ℝ)}
    (e : EuclideanPoint (n + 1) ≃ᵃ[ℝ] EuclideanPoint (n + 1))
    (hEta : eta ∈ Set.Icc delta (delta ^ tau))
    (hOmega : IsConvexBody Omega)
    (hXOmega : (X : Set (EuclideanPoint (n + 1))) ⊆ Omega)
    (hYX : ∀ i ∈ J, Y i ⊆ X)
    (hdisjoint : (J : Set ι).PairwiseDisjoint Y)
    (hW : Convex ℝ W)
    (hwitness : ∀ i ∈ J, lastCoordinateCLE n (e (witness i)) ∈ W)
    (hnear : ∀ i ∈ J, ∀ z ∈ Y i, dist (e z) (e (witness i)) ≤ r)
    (hVolume : volume (minkowskiClosedBall W r) ≤
      ENNReal.ofReal eta * volume (e '' Omega))
    (hCard : eta ^ densityExponent (n + 1) epsilon * (X.card : ℝ) ≤
      (∑ i ∈ J, (Y i).card : ℕ)) :
    ConvexDensityOutput epsilon tau delta Omega X := by
  let X' := affineEquivImageFinset e X
  let Y' : ι → Finset (EuclideanPoint (n + 1)) :=
    fun i ↦ affineEquivImageFinset e (Y i)
  have hX' : (X' : Set (EuclideanPoint (n + 1))) ⊆ e '' Omega := by
    intro x hx
    have hxX : e.symm x ∈ X := by
      simpa [X'] using (mem_affineEquivImageFinset e X x).mp hx
    exact ⟨e.symm x, hXOmega hxX, e.apply_symm_apply x⟩
  have hY'X' : ∀ i ∈ J, Y' i ⊆ X' := by
    intro i hi x hx
    apply (mem_affineEquivImageFinset e X x).mpr
    apply hYX i hi
    exact (mem_affineEquivImageFinset e (Y i) x).mp hx
  have hdisjoint' : (J : Set ι).PairwiseDisjoint Y' := by
    intro i hi j hj hij
    change Disjoint (Y' i) (Y' j)
    rw [Finset.disjoint_left]
    intro x hxi hxj
    have hprei : e.symm x ∈ Y i :=
      (mem_affineEquivImageFinset e (Y i) x).mp hxi
    have hprej : e.symm x ∈ Y j :=
      (mem_affineEquivImageFinset e (Y j) x).mp hxj
    exact (Finset.disjoint_left.mp (hdisjoint hi hj hij)) hprei hprej
  have hnear' : ∀ i ∈ J, ∀ z ∈ Y' i,
      dist z (e (witness i)) ≤ r := by
    intro i hi z hz
    have hz' : e.symm z ∈ Y i :=
      (mem_affineEquivImageFinset e (Y i) z).mp hz
    simpa using hnear i hi (e.symm z) hz'
  have hChart : ConvexDensityOutput epsilon tau delta (e '' Omega) X' := by
    apply convexDensityOutput_of_disjoint_fibers_in_product_thickening
        (J := J) (Y := Y') (witness := fun i ↦ e (witness i))
        (W := W) (r := r) hEta
        (isConvexBody_affineEquiv_image e hOmega) hX'
    · exact hY'X'
    · exact hdisjoint'
    · exact hW
    · exact hwitness
    · exact hnear'
    · exact hVolume
    · simpa [X', Y', card_affineEquivImageFinset] using hCard
  exact (convexDensityOutput_affineEquivImage_iff e epsilon tau delta
    Omega X).1 (by simpa [X'] using hChart)

end
end Erdos186.PZ.ConvexDensity
