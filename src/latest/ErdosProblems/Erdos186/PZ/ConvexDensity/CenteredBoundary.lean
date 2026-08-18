/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.ConvexDensity.BoundaryWitnesses
import ErdosProblems.Erdos186.PZ.ConvexDensity.HouseholderCap

/-!
# Centering and rotating the common boundary hull

The quantitative inball theorem produces a ball about an arbitrary centre.
The cap step then chooses a Householder reflection.  This file packages their
composition as an affine isometry and transports compactness, convexity,
frontiers, balls, and annulus bounds.  Thus the graph theorem can be applied
to one common transformed hull.
-/

open Set

namespace Erdos186.PZ.ConvexDensity

set_option autoImplicit false

noncomputable section

/-- Translate `center` to zero and then apply the chosen Householder
reflection. -/
def centeredHouseholderEquiv {n : ℕ}
    (center direction : EuclideanPoint (n + 1)) :
    EuclideanPoint (n + 1) ≃ᵃⁱ[ℝ] EuclideanPoint (n + 1) :=
  (AffineIsometryEquiv.constVAdd ℝ (EuclideanPoint (n + 1)) (-center)).trans
    (representativeToLast direction).toAffineIsometryEquiv

@[simp]
theorem centeredHouseholderEquiv_apply {n : ℕ}
    (center direction z : EuclideanPoint (n + 1)) :
    centeredHouseholderEquiv center direction z =
      representativeToLast direction (z - center) := by
  simp [centeredHouseholderEquiv, sub_eq_add_neg, add_comm]

@[simp]
theorem centeredHouseholderEquiv_center {n : ℕ}
    (center direction : EuclideanPoint (n + 1)) :
    centeredHouseholderEquiv center direction center = 0 := by
  simp

/-- The centred Householder chart preserves distance. -/
theorem dist_centeredHouseholderEquiv {n : ℕ}
    (center direction z w : EuclideanPoint (n + 1)) :
    dist (centeredHouseholderEquiv center direction z)
        (centeredHouseholderEquiv center direction w) = dist z w := by
  exact (centeredHouseholderEquiv center direction).isometry.dist_eq z w

/-- In particular, its output norm is distance from the chosen centre. -/
theorem norm_centeredHouseholderEquiv {n : ℕ}
    (center direction z : EuclideanPoint (n + 1)) :
    ‖centeredHouseholderEquiv center direction z‖ = dist z center := by
  rw [← dist_zero_right,
    ← centeredHouseholderEquiv_center center direction]
  exact dist_centeredHouseholderEquiv center direction z center

/-- The image of a centred closed ball is the same-radius ball about zero. -/
theorem image_closedBall_centeredHouseholderEquiv {n : ℕ}
    (center direction : EuclideanPoint (n + 1)) (r : ℝ) :
    centeredHouseholderEquiv center direction '' Metric.closedBall center r =
      Metric.closedBall 0 r := by
  change (centeredHouseholderEquiv center direction).toIsometryEquiv ''
      Metric.closedBall center r = Metric.closedBall 0 r
  rw [(centeredHouseholderEquiv center direction).toIsometryEquiv.image_closedBall]
  simp

/-- A radial annulus around `center` becomes the standard annulus about
zero. -/
theorem mem_boundedAnnulus_centeredHouseholderEquiv_iff {n : ℕ}
    {center direction z : EuclideanPoint (n + 1)} {inner outer : ℝ} :
    centeredHouseholderEquiv center direction z ∈
        boundedAnnulus inner outer ↔
      inner ≤ dist z center ∧ dist z center ≤ outer := by
  simp only [boundedAnnulus, mem_setOf_eq,
    norm_centeredHouseholderEquiv]

/-- Compactness of the common hull survives the chart. -/
theorem IsCompact.centeredHouseholder_image {n : ℕ}
    {P : Set (EuclideanPoint (n + 1))} (hP : IsCompact P)
    (center direction : EuclideanPoint (n + 1)) :
    IsCompact (centeredHouseholderEquiv center direction '' P) := by
  exact hP.image (centeredHouseholderEquiv center direction).continuous

/-- Convexity of the common hull survives the chart. -/
theorem Convex.centeredHouseholder_image {n : ℕ}
    {P : Set (EuclideanPoint (n + 1))} (hP : Convex ℝ P)
    (center direction : EuclideanPoint (n + 1)) :
    Convex ℝ (centeredHouseholderEquiv center direction '' P) := by
  exact hP.affine_image
    (centeredHouseholderEquiv center direction).toAffineEquiv.toAffineMap

/-- Boundary witnesses remain frontier points of the one transformed common
hull. -/
theorem mem_frontier_centeredHouseholder_image_iff {n : ℕ}
    {P : Set (EuclideanPoint (n + 1))}
    {center direction z : EuclideanPoint (n + 1)} :
    centeredHouseholderEquiv center direction z ∈
        frontier (centeredHouseholderEquiv center direction '' P) ↔
      z ∈ frontier P := by
  change (centeredHouseholderEquiv center direction).toHomeomorph z ∈
      frontier ((centeredHouseholderEquiv center direction).toHomeomorph '' P) ↔ _
  rw [← (centeredHouseholderEquiv center direction).toHomeomorph.image_frontier]
  simp

/-- Transport an arbitrary inball into a ball about the graph-chart origin. -/
theorem closedBall_zero_subset_centeredHouseholder_image {n : ℕ}
    {P : Set (EuclideanPoint (n + 1))}
    {center direction : EuclideanPoint (n + 1)}
    {r : ℝ} (hball : Metric.closedBall center r ⊆ P) :
    Metric.closedBall 0 r ⊆
      centeredHouseholderEquiv center direction '' P := by
  rw [← image_closedBall_centeredHouseholderEquiv center direction r]
  exact Set.image_mono hball

/-! ## A label-preserving common upper-boundary chart -/

/-- A cap of labelled frontier points of one common convex body becomes a
cap of points on the upper-boundary graph after the representative
Householder reflection.  The size lower bound is the exact indexed cap
pigeonhole bound, so coincident geometric witnesses retain their labels. -/
theorem exists_large_indexed_cap_upperBoundary_chart
    {ι : Type*} [DecidableEq ι] {n m : ℕ}
    (hm : 0 < m) (hmLarge : 4 * Real.sqrt n ≤ m)
    {inner outer : ℝ} (hinnerPos : 0 < inner)
    (hbaseSmall : outer * (2 * Real.sqrt n / m) < inner)
    {P : Set (EuclideanPoint (n + 1))}
    (hPcompact : IsCompact P) (hPconvex : Convex ℝ P)
    (hinner : Metric.closedBall 0 inner ⊆ P)
    (I : Finset ι) (hI : I.Nonempty)
    (witness : ι → EuclideanPoint (n + 1))
    (hfrontier : ∀ i ∈ I, witness i ∈ frontier P)
    (hannulus : ∀ i ∈ I, witness i ∈ boundedAnnulus inner outer) :
    ∃ (c : DirectionCapIndex n m) (J : Finset ι) (representative : ι),
      representative ∈ J ∧
      J ⊆ I ∧
      ((((m : ℝ)⁻¹ / 3) ^ n) / (2 * (n + 1))) * I.card ≤ J.card ∧
      (∀ j ∈ J,
        normalizedDirection (witness j) ∈ directionCap m c) ∧
      IsCompact
        (representativeToLast (normalizedDirection (witness representative)) '' P) ∧
      Convex ℝ
        (representativeToLast (normalizedDirection (witness representative)) '' P) ∧
      Metric.closedBall 0 inner ⊆
        representativeToLast (normalizedDirection (witness representative)) '' P ∧
      ∀ j ∈ J,
        let R := representativeToLast
          (normalizedDirection (witness representative))
        let P' := R '' P
        R (witness j) ∈ frontier P' ∧
          ‖baseCoordinates (R (witness j))‖ < inner ∧
          inner / 2 ≤ lastCoordinate (R (witness j)) ∧
          R (witness j) =
            upperBoundaryPoint P'
              (hPcompact.image R.continuous) (baseCoordinates (R (witness j))) := by
  obtain ⟨c, J, representative, hrepJ, hJI, hcard, hannJ, hcap,
    _hrepLast, _hresidual⟩ :=
    exists_large_indexed_cap_graph_chart hm hinnerPos I hI witness hannulus
  let R := representativeToLast (normalizedDirection (witness representative))
  let P' : Set (EuclideanPoint (n + 1)) := R '' P
  have hP'compact : IsCompact P' := hPcompact.image R.continuous
  have hP'convex : Convex ℝ P' :=
    hPconvex.linear_image R.toLinearEquiv.toLinearMap
  have hP'inner : Metric.closedBall 0 inner ⊆ P' := by
    have himage := R.image_closedBall (0 : EuclideanPoint (n + 1)) inner
    simp only [map_zero] at himage
    rw [← himage]
    exact Set.image_mono hinner
  refine ⟨c, J, representative, hrepJ, hJI, hcard, hcap,
    hP'compact, hP'convex, hP'inner, ?_⟩
  intro j hj
  have hrepCap := hcap representative hrepJ
  have hjBounds := householder_annulus_base_last_bounds hm hmLarge hinnerPos
    (hannJ representative hrepJ) (hannJ j hj) hrepCap (hcap j hj)
  have hjFront : R (witness j) ∈ frontier P' := by
    dsimp only [P']
    have himage := R.toHomeomorph.image_frontier P
    change R '' frontier P = frontier (R '' P) at himage
    rw [← himage]
    exact ⟨witness j, hfrontier j (hJI hj), rfl⟩
  have hjBase : ‖baseCoordinates (R (witness j))‖ < inner :=
    hjBounds.1.trans_lt hbaseSmall
  have hjGraph : R (witness j) =
      upperBoundaryPoint P' hP'compact (baseCoordinates (R (witness j))) := by
    exact eq_upperBoundaryPoint_of_frontier_of_innerBall
      hP'compact hP'convex hinnerPos hP'inner hjFront hjBase hjBounds.2
  exact ⟨hjFront, hjBase, hjBounds.2, hjGraph⟩

end

end Erdos186.PZ.ConvexDensity
