import StackExchange.Puzzling139335.N4MiddleInvolutions.FaceBounds.Length
import StackExchange.Puzzling139335.N4MiddleInvolutions.FaceBounds.Sums

/-!
# Finite supporting-face bounds inside a rectangle

Faces with outward normals on one side of a coordinate axis have disjoint
open projections onto the other coordinate axis.  The two signs therefore
contribute at most twice each rectangle dimension.  This gives a finite
Euclidean length bound directly, without a perimeter or boundary ordering.
-/

open Set
open scoped BigOperators

namespace Puzzling139335.N4MiddleInvolutions.FaceBounds

/-- The total length of finitely many supporting segments with distinct
unit outward normals is at most twice the sum of the enclosing rectangle's
width and height.  No compactness or boundary regularity is required. -/
theorem sum_supporting_segment_lengths_le_box {ι : Type*} [Fintype ι]
    {K : Set Plane} (hK : Convex ℝ K) (nx ny : ι → ℝ) (a b : ι → Plane)
    (hface : ∀ i, SupportsSegment K (nx i) (ny i) (a i) (b i))
    (hnorm : ∀ i, (nx i) ^ 2 + (ny i) ^ 2 = 1)
    (hinj : Function.Injective (fun i => (nx i, ny i)))
    {l r bottom top : ℝ} (hlr : l ≤ r) (hbt : bottom ≤ top)
    (hbox : ∀ p ∈ K,
      (l ≤ p 0 ∧ p 0 ≤ r) ∧ (bottom ≤ p 1 ∧ p 1 ≤ top)) :
    ∑ i, dist (a i) (b i) ≤ 2 * ((r - l) + (top - bottom)) := by
  have hx := sum_abs_horizontal_span_le hK nx ny a b hface hnorm hinj hlr
    (fun p hp => (hbox p hp).1)
  have hy := sum_abs_vertical_span_le hK nx ny a b hface hnorm hinj hbt
    (fun p hp => (hbox p hp).2)
  calc
    ∑ i, dist (a i) (b i) ≤
        (∑ i, |a i 0 - b i 0|) + ∑ i, |a i 1 - b i 1| :=
      sum_dist_le_coordinate_sums a b
    _ ≤ 2 * (r - l) + 2 * (top - bottom) := add_le_add hx hy
    _ = _ := by ring

/-- In a strip of width one and height strictly less than one, at most
three distinct outward normal directions can have supporting segments of
length at least one. -/
theorem card_unit_supporting_segments_le_three {ι : Type*} [Fintype ι]
    {K : Set Plane} (hK : Convex ℝ K) (nx ny : ι → ℝ) (a b : ι → Plane)
    (hface : ∀ i, SupportsSegment K (nx i) (ny i) (a i) (b i))
    (hnorm : ∀ i, (nx i) ^ 2 + (ny i) ^ 2 = 1)
    (hinj : Function.Injective (fun i => (nx i, ny i)))
    (hSquare : K ⊆ unitSquare) {l h : ℝ} (hlh : l ≤ h) (hheight : h - l < 1)
    (hstrip : ∀ p ∈ K, l ≤ p 1 ∧ p 1 ≤ h)
    (hlen : ∀ i, 1 ≤ dist (a i) (b i)) : Fintype.card ι ≤ 3 := by
  apply card_le_three_of_sum_dist_lt_four a b hlen
  have hsum := sum_supporting_segment_lengths_le_box hK nx ny a b
    hface hnorm hinj (show (0 : ℝ) ≤ 1 by norm_num) hlh
    (fun p hp => ⟨(hSquare hp).1, hstrip p hp⟩)
  nlinarith

end Puzzling139335.N4MiddleInvolutions.FaceBounds
