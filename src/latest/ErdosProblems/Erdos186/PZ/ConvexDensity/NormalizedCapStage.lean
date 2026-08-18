/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.ConvexDensity.LargeGraphBranch
import ErdosProblems.Erdos186.PZ.ConvexDensity.NormalizedBranchParameters

/-! # Direction cap for the normalized common hull -/

open Set

namespace Erdos186.PZ.ConvexDensity

set_option autoImplicit false
noncomputable section

/-- Apply the reciprocal-window direction cap to all first-shell labels.  Its
retained fraction is exposed in the `q^n`-compatible rounded form. -/
theorem exists_normalized_cap_window
    {n : ℕ} (hn : 0 < n) {epsilon delta : ℝ}
    (hepsilon : 0 < epsilon) (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    {P : Set (EuclideanPoint (n + 1))}
    (hPcompact : IsCompact P) (hPconvex : Convex ℝ P)
    {center : EuclideanPoint (n + 1)}
    (hcenter : center ∈ P)
    (hinnerBall : Metric.closedBall center
      (normalizedLargeHullInradius (n + 1) epsilon delta) ⊆ P)
    (hPzero : P ⊆ Metric.closedBall 0 (Real.sqrt (n + 1)))
    {J : Finset (Fin (n + 1) → ℕ)} (hJ : J.Nonempty)
    (witness : {k // k ∈ J} → EuclideanPoint (n + 1))
    (hfrontier : ∀ k, witness k ∈ frontier P) :
    ∃ (C : Finset {k // k ∈ J}) (representative : {k // k ∈ J}),
      representative ∈ C ∧
      roundedCapFractionLower n
          (normalizedGraphWindowRadius (n + 1) epsilon delta)
          (normalizedCommonHullOuterRadius (n + 1)) * J.card ≤ C.card ∧
      let T := AffineIsometryEquiv.constVAdd ℝ
        (EuclideanPoint (n + 1)) (-center)
      let w0 : {k // k ∈ J} → EuclideanPoint (n + 1) := fun k ↦ T (witness k)
      let R := representativeToLast (normalizedDirection (w0 representative))
      let P' := R '' (T '' P)
      IsCompact P' ∧ Convex ℝ P' ∧
      Metric.closedBall 0
          (normalizedLargeHullInradius (n + 1) epsilon delta) ⊆ P' ∧
      P' ⊆ Metric.closedBall 0
          (normalizedCommonHullOuterRadius (n + 1)) ∧
      (∀ k ∈ C,
        ‖baseCoordinates (R (w0 k))‖ ≤
          normalizedGraphWindowRadius (n + 1) epsilon delta) ∧
      ∀ k ∈ C,
        R (w0 k) = upperBoundaryPoint P'
          ((hPcompact.image T.continuous).image R.continuous)
          (baseCoordinates (R (w0 k))) := by
  classical
  let inner := normalizedLargeHullInradius (n + 1) epsilon delta
  let q := normalizedGraphWindowRadius (n + 1) epsilon delta
  let outer := normalizedCommonHullOuterRadius (n + 1)
  let mCap := capGridSize n q outer
  have hinner : 0 < inner :=
    normalizedLargeHullInradius_pos (by omega : 0 < n + 1) hdelta
  have hq : 0 < q :=
    normalizedGraphWindowRadius_pos (by omega : 2 ≤ n + 1) hdelta
  have houter : 0 < outer :=
    normalizedCommonHullOuterRadius_pos (by omega : 0 < n + 1)
  have hqinner : q < inner :=
    normalizedGraphWindowRadius_lt_inradius (by omega : 2 ≤ n + 1) hdelta
  have hqouter : q ≤ outer :=
    normalizedGraphWindowRadius_le_outer (by omega : 2 ≤ n + 1)
      hepsilon hdelta hdeltaOne
  obtain ⟨hmLarge, hcapWindow⟩ :=
    capGridSize_geometry_of_le hn hq houter hqouter
  have hmCap : 0 < mCap := capGridSize_pos hn hq houter
  have hPouter : P ⊆ Metric.closedBall center outer := by
    simpa [outer, normalizedCommonHullOuterRadius] using
      subset_closedBall_center_two_mul hPzero hcenter
  have hannulus : ∀ k : {k // k ∈ J},
      inner ≤ dist (witness k) center ∧ dist (witness k) center ≤ outer := by
    intro k
    constructor
    · exact radius_le_dist_of_closedBall_subset_of_mem_frontier
        hinnerBall (hfrontier k)
    · simpa [Metric.mem_closedBall] using hPouter
        (hPcompact.isClosed.frontier_subset (hfrontier k))
  have hI : (Finset.univ : Finset {k // k ∈ J}).Nonempty := by
    simpa using hJ
  obtain ⟨C, representative, hrep, _hsub, hcard, hrest⟩ :=
    exists_cap_centered_upperBoundary_window hmCap hmLarge hinner hqinner
      hcapWindow hPcompact hPconvex hinnerBall hPouter
      Finset.univ hI witness (fun k _hk ↦ hfrontier k)
      (fun k _hk ↦ hannulus k)
  have hround := roundedCapFractionLower_le hn hq houter hqouter
  have hcard' : roundedCapFractionLower n q outer * J.card ≤ C.card := by
    calc
      roundedCapFractionLower n q outer * J.card ≤
          ((((mCap : ℝ)⁻¹ / 3) ^ n) / (2 * (n + 1))) * J.card := by
            gcongr
      _ = ((((mCap : ℝ)⁻¹ / 3) ^ n) / (2 * (n + 1))) *
          (Finset.univ : Finset {k // k ∈ J}).card := by simp
      _ ≤ C.card := hcard
  exact ⟨C, representative, hrep, by simpa [q, outer] using hcard',
    by simpa [inner, q, outer] using hrest⟩

end
end Erdos186.PZ.ConvexDensity
