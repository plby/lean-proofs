import StackExchange.Puzzling139335.JordanRegion
import Wikipedia.SchoenfliesTheorem.ModelCurve

/-!
# A full horizontal or vertical segment separates the other pieces

The interior of any other piece avoids the segment.  Its connectedness puts it
on one strict side of the segment's supporting line; regular closedness then
puts the whole piece in the corresponding closed half-plane.
-/

open Set Schoenflies

namespace Puzzling139335.RectangularHull

/-- A closed Jordan region whose interior avoids one coordinate level lies
entirely on one closed side of that level. -/
theorem jordan_region_one_side_of_coordinate_avoidance {P : Set Plane}
    (hP : IsJordanRegion P) (axis : Fin 2) (h : ℝ)
    (havoid : ∀ p ∈ interior P, p axis ≠ h) :
    (∀ p ∈ P, p axis ≤ h) ∨ (∀ p ∈ P, h ≤ p axis) := by
  have hopen₁ : IsOpen {p : Plane | p axis < h} :=
    isOpen_lt (by fun_prop) continuous_const
  have hopen₂ : IsOpen {p : Plane | h < p axis} :=
    isOpen_lt continuous_const (by fun_prop)
  have hdis : Disjoint {p : Plane | p axis < h} {p : Plane | h < p axis} := by
    apply Set.disjoint_left.mpr
    intro p hp₁ hp₂
    change p axis < h at hp₁
    change h < p axis at hp₂
    exact lt_asymm hp₁ hp₂
  have hcover : interior P ⊆ {p : Plane | p axis < h} ∪ {p : Plane | h < p axis} := by
    intro p hp
    exact lt_or_gt_of_ne (havoid p hp)
  rcases hP.isConnected_interior.isPreconnected.subset_or_subset
      hopen₁ hopen₂ hdis hcover with hlo | hhi
  · left
    have hsub : interior P ⊆ {p : Plane | p axis ≤ h} :=
      fun p hp => (show p axis < h from hlo hp).le
    have hclosed : IsClosed {p : Plane | p axis ≤ h} :=
      isClosed_le (by fun_prop) continuous_const
    rw [← hP.closure_interior]
    exact closure_minimal hsub hclosed
  · right
    have hsub : interior P ⊆ {p : Plane | h ≤ p axis} :=
      fun p hp => (show h < p axis from hhi hp).le
    have hclosed : IsClosed {p : Plane | h ≤ p axis} :=
      isClosed_le continuous_const (by fun_prop)
    rw [← hP.closure_interior]
    exact closure_minimal hsub hclosed

/-- A region in the unit square whose interior avoids a set containing a full
horizontal unit segment lies wholly above or wholly below that segment. -/
theorem region_one_side_of_horizontal_segment {P Q : Set Plane} {h : ℝ}
    (hP : IsJordanRegion P) (hPS : P ⊆ unitSquare)
    (hdis : Disjoint (interior P) Q)
    (hsegment : segment ℝ (Schoenflies.Plane.mk 0 h) (Schoenflies.Plane.mk 1 h) ⊆ Q) :
    (∀ p ∈ P, p 1 ≤ h) ∨ (∀ p ∈ P, h ≤ p 1) := by
  apply jordan_region_one_side_of_coordinate_avoidance hP 1 h
  intro p hp heq
  apply Set.disjoint_left.mp hdis hp
  apply hsegment
  rw [Schoenflies.mem_segment_horiz, segment_eq_Icc (show (0 : ℝ) ≤ 1 by norm_num)]
  exact ⟨heq, (hPS (interior_subset hp)).1⟩

/-- The analogous separation statement for a full vertical unit segment. -/
theorem region_one_side_of_vertical_segment {P Q : Set Plane} {h : ℝ}
    (hP : IsJordanRegion P) (hPS : P ⊆ unitSquare)
    (hdis : Disjoint (interior P) Q)
    (hsegment : segment ℝ (Schoenflies.Plane.mk h 0) (Schoenflies.Plane.mk h 1) ⊆ Q) :
    (∀ p ∈ P, p 0 ≤ h) ∨ (∀ p ∈ P, h ≤ p 0) := by
  apply jordan_region_one_side_of_coordinate_avoidance hP 0 h
  intro p hp heq
  apply Set.disjoint_left.mp hdis hp
  apply hsegment
  rw [Schoenflies.mem_segment_vert, segment_eq_Icc (show (0 : ℝ) ≤ 1 by norm_num)]
  exact ⟨heq, (hPS (interior_subset hp)).2⟩

/-- If one dissection piece contains a complete horizontal unit segment, every
different piece lies on one closed side of its horizontal line. -/
theorem horizontal_segment_separates_pieces (d : SquareDissection)
    {k i : Fin 4} {h : ℝ}
    (hsegment : segment ℝ (Schoenflies.Plane.mk 0 h) (Schoenflies.Plane.mk 1 h) ⊆
      d.piece k) (hik : i ≠ k) :
    (∀ p ∈ d.piece i, p 1 ≤ h) ∨ (∀ p ∈ d.piece i, h ≤ p 1) :=
  region_one_side_of_horizontal_segment (d.jordan i) (d.piece_subset i)
    (d.disjoint_interior_piece hik) hsegment

/-- If one dissection piece contains a complete vertical unit segment, every
different piece lies on one closed side of its vertical line. -/
theorem vertical_segment_separates_pieces (d : SquareDissection)
    {k i : Fin 4} {h : ℝ}
    (hsegment : segment ℝ (Schoenflies.Plane.mk h 0) (Schoenflies.Plane.mk h 1) ⊆
      d.piece k) (hik : i ≠ k) :
    (∀ p ∈ d.piece i, p 0 ≤ h) ∨ (∀ p ∈ d.piece i, h ≤ p 0) :=
  region_one_side_of_vertical_segment (d.jordan i) (d.piece_subset i)
    (d.disjoint_interior_piece hik) hsegment

end Puzzling139335.RectangularHull
