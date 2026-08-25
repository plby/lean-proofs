import StackExchange.Puzzling139335.Definitions
import StackExchange.Puzzling139335.N4MiddleInvolutions.FaceBounds.Sums.SignedIntervals
import Mathlib.Analysis.Normed.Affine.AddTorsor

/-!
# Packing finitely many straight segments into one segment

Affine parameters turn the subsegments into intervals in `[0, 1]`.
Disjoint open subsegments give disjoint parameter intervals, while distances
are the parameter spans multiplied by the containing segment's length.
-/

open Set
open scoped BigOperators

namespace Puzzling139335.N4MiddleInvolutions.BoundaryBalance

private theorem exists_segment_parameters {ι : Type*} (K : Finset ι)
    (z : ι → Plane) {a b : Plane}
    (hz : ∀ k ∈ K, z k ∈ segment ℝ a b) :
    ∃ t : ι → ℝ, (∀ k ∈ K, t k ∈ Icc (0 : ℝ) 1) ∧
      ∀ k ∈ K, AffineMap.lineMap a b (t k) = z k := by
  classical
  have hex : ∀ k, ∃ t : ℝ, t ∈ Icc (0 : ℝ) 1 ∧
      (k ∈ K → AffineMap.lineMap a b t = z k) := by
    intro k
    by_cases hk : k ∈ K
    · obtain ⟨t, ht, heq⟩ := (segment_eq_image_lineMap ℝ a b) ▸ hz k hk
      exact ⟨t, ht, fun _ => heq⟩
    · exact ⟨0, ⟨le_rfl, zero_le_one⟩, fun h => (hk h).elim⟩
  choose t ht heq using hex
  exact ⟨t, fun k _ => ht k, heq⟩

/-- Pairwise disjoint open subsegments of a fixed segment have total length
at most the length of that segment. Degenerate subsegments are allowed. -/
theorem sum_dist_le_of_disjoint_openSegments {ι : Type*}
    (K : Finset ι) (x y : ι → Plane) {a b : Plane}
    (hx : ∀ k ∈ K, x k ∈ segment ℝ a b)
    (hy : ∀ k ∈ K, y k ∈ segment ℝ a b)
    (hdis : (↑K : Set ι).Pairwise fun i j =>
      Disjoint (openSegment ℝ (x i) (y i)) (openSegment ℝ (x j) (y j))) :
    (∑ k ∈ K, dist (x k) (y k)) ≤ dist a b := by
  classical
  obtain ⟨u, hu, hxu⟩ := exists_segment_parameters K x hx
  obtain ⟨v, hv, hyv⟩ := exists_segment_parameters K y hy
  have hmem (i : ι) (hi : i ∈ K) {t : ℝ}
      (ht : t ∈ Ioo (min (u i) (v i)) (max (u i) (v i))) :
      AffineMap.lineMap a b t ∈ openSegment ℝ (x i) (y i) := by
    have htseg : t ∈ openSegment ℝ (u i) (v i) := by
      by_cases huv : u i = v i
      · simp [huv] at ht
      · rwa [openSegment_eq_Ioo' huv]
    have himage := mem_image_of_mem (AffineMap.lineMap a b) htseg
    rwa [image_openSegment, hxu i hi, hyv i hi] at himage
  have hdis' : (↑K : Set ι).Pairwise fun i j =>
      Disjoint (Ioo (min (u i) (v i)) (max (u i) (v i)))
        (Ioo (min (u j) (v j)) (max (u j) (v j))) := by
    intro i hi j hj hij
    apply Set.disjoint_left.mpr
    intro t hti htj
    exact Set.disjoint_left.mp (hdis hi hj hij) (hmem i hi hti) (hmem j hj htj)
  have hbound := FaceBounds.sum_abs_sub_le_of_disjoint_intervals K u v
    (show (0 : ℝ) ≤ 1 from zero_le_one) hu hv hdis'
  calc
    (∑ k ∈ K, dist (x k) (y k)) =
        (∑ k ∈ K, |u k - v k|) * dist a b := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k hk
      rw [← hxu k hk, ← hyv k hk, dist_lineMap_lineMap, Real.dist_eq]
    _ ≤ 1 * dist a b := mul_le_mul_of_nonneg_right (by simpa using hbound) dist_nonneg
    _ = dist a b := one_mul _

end Puzzling139335.N4MiddleInvolutions.BoundaryBalance
