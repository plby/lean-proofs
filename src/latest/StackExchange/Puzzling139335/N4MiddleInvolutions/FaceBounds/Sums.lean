import StackExchange.Puzzling139335.N4MiddleInvolutions.FaceBounds.Projection
import StackExchange.Puzzling139335.N4MiddleInvolutions.FaceBounds.Sums.SignedIntervals

/-!
# Coordinate span sums for actual supporting segments

For distinct unit outward normals, supporting segments on each of the two
sides of a convex set have disjoint open projections.  Applying the finite
interval length bound to each side bounds the total coordinate span by
twice the containing box's width or height.  No boundary cycle or perimeter
formula is assumed.
-/

open Set

namespace Puzzling139335.N4MiddleInvolutions.FaceBounds

/-- The horizontal spans of finitely many actual supporting segments with
distinct unit normals sum to at most twice the containing interval's width. -/
theorem sum_abs_horizontal_span_le {ι : Type*} [Fintype ι] {K : Set Plane}
    (hK : Convex ℝ K) (nx ny : ι → ℝ) (a b : ι → Plane)
    (hface : ∀ i, SupportsSegment K (nx i) (ny i) (a i) (b i))
    (hnorm : ∀ i, (nx i) ^ 2 + (ny i) ^ 2 = 1)
    (hinj : Function.Injective (fun i => (nx i, ny i)))
    {l r : ℝ} (hlr : l ≤ r) (hbox : ∀ p ∈ K, l ≤ p 0 ∧ p 0 ≤ r) :
    (∑ i, |a i 0 - b i 0|) ≤ 2 * (r - l) := by
  classical
  apply sum_abs_sub_le_two_mul_of_signed_intervals Finset.univ ny
    (fun i => a i 0) (fun i => b i 0) hlr
  · intro i _
    exact hbox (a i) (hface i).left_mem
  · intro i _
    exact hbox (b i) (hface i).right_mem
  · intro i _ hy
    exact (hface i).horizontal_span_eq_zero_of_normal_y_eq_zero (hnorm i) hy
  · intro i _ j _ hij hsign
    exact (hface i).disjoint_horizontal_projection_of_same_sign (hface j)
      hK (hnorm i) (hnorm j) (hinj.ne hij) hsign

/-- The vertical spans of finitely many actual supporting segments with
distinct unit normals sum to at most twice the containing interval's height. -/
theorem sum_abs_vertical_span_le {ι : Type*} [Fintype ι] {K : Set Plane}
    (hK : Convex ℝ K) (nx ny : ι → ℝ) (a b : ι → Plane)
    (hface : ∀ i, SupportsSegment K (nx i) (ny i) (a i) (b i))
    (hnorm : ∀ i, (nx i) ^ 2 + (ny i) ^ 2 = 1)
    (hinj : Function.Injective (fun i => (nx i, ny i)))
    {l r : ℝ} (hlr : l ≤ r) (hbox : ∀ p ∈ K, l ≤ p 1 ∧ p 1 ≤ r) :
    (∑ i, |a i 1 - b i 1|) ≤ 2 * (r - l) := by
  classical
  apply sum_abs_sub_le_two_mul_of_signed_intervals Finset.univ nx
    (fun i => a i 1) (fun i => b i 1) hlr
  · intro i _
    exact hbox (a i) (hface i).left_mem
  · intro i _
    exact hbox (b i) (hface i).right_mem
  · intro i _ hx
    exact (hface i).vertical_span_eq_zero_of_normal_x_eq_zero (hnorm i) hx
  · intro i _ j _ hij hsign
    exact (hface i).disjoint_vertical_projection_of_same_sign (hface j)
      hK (hnorm i) (hnorm j) (hinj.ne hij) hsign

end Puzzling139335.N4MiddleInvolutions.FaceBounds
