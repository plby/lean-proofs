import StackExchange.Puzzling139335.Definitions
import StackExchange.Puzzling139335.RectangularHull.Interlacing
import StackExchange.Puzzling139335.BandMass.Geometry

/-!
# The lower rectangle used to clip a height-crossing arc

Its bottom side is an actual boundary arc, and a point at positive top height
lies on the complementary part of the rectangle boundary.
-/

open Set

namespace Puzzling139335.HeightBarrier

/-- The closed rectangle of width one between heights zero and `h`. -/
def lowerRectangle (h : ℝ) : Set Plane :=
  RectangularHull.axisRectangle 0 1 0 h

theorem lowerRectangle_eq_horizontalBand (h : ℝ) :
    lowerRectangle h = horizontalBand 0 h := by
  ext z
  exact and_assoc.symm

/-- The coordinate description does not require a nondegeneracy assumption. -/
theorem mem_lowerRectangle_iff {h : ℝ} {z : Plane} :
    z ∈ lowerRectangle h ↔ 0 ≤ z 0 ∧ z 0 ≤ 1 ∧ 0 ≤ z 1 ∧ z 1 ≤ h := Iff.rfl

theorem isClosed_lowerRectangle (h : ℝ) : IsClosed (lowerRectangle h) := by
  rw [lowerRectangle_eq_horizontalBand]
  exact isClosed_horizontalBand 0 h

/-- A positive-height lower rectangle is a closed Jordan region. -/
theorem isJordanRegion_lowerRectangle {h : ℝ} (hh : 0 < h) :
    IsJordanRegion (lowerRectangle h) :=
  RectangularHull.isJordanRegion_axisRectangle (by norm_num) hh

/-- The interior is exactly the set satisfying all four strict inequalities. -/
theorem mem_interior_lowerRectangle_iff {h : ℝ} {z : Plane} :
    z ∈ interior (lowerRectangle h) ↔
      0 < z 0 ∧ z 0 < 1 ∧ 0 < z 1 ∧ z 1 < h := by
  rw [lowerRectangle_eq_horizontalBand, mem_interior_horizontalBand_iff]
  exact and_assoc

theorem mem_lowerRectangle_of_mem_unitSquare {h : ℝ} {z : Plane}
    (hz : z ∈ unitSquare) (hzh : z 1 ≤ h) : z ∈ lowerRectangle h :=
  ⟨hz.1.1, hz.1.2, hz.2.1, hzh⟩

/-- A subset of the square staying below height `h` lies in the lower rectangle. -/
theorem subset_lowerRectangle {P : Set Plane} {h : ℝ}
    (hPS : P ⊆ unitSquare) (hPh : ∀ z ∈ P, z 1 ≤ h) : P ⊆ lowerRectangle h := by
  intro z hz
  exact mem_lowerRectangle_of_mem_unitSquare (hPS hz) (hPh z hz)

theorem lowerRectangle_subset_unitSquare {h : ℝ} (hh : h ≤ 1) :
    lowerRectangle h ⊆ unitSquare := by
  intro z hz
  exact ⟨⟨hz.1, hz.2.1⟩, hz.2.2.1, hz.2.2.2.trans hh⟩

/-- Membership in the segment between the two bottom square corners. -/
theorem mem_bottom_segment_iff {z : Plane} :
    z ∈ segment ℝ (corner 0) (corner 1) ↔
      z 1 = 0 ∧ 0 ≤ z 0 ∧ z 0 ≤ 1 := by
  change z ∈ segment ℝ (Schoenflies.Plane.mk 0 0) (Schoenflies.Plane.mk 1 0) ↔ _
  rw [Schoenflies.mem_segment_horiz, segment_eq_Icc (show (0 : ℝ) ≤ 1 by norm_num)]
  rfl

/-- The full bottom segment, including its endpoints, is on the rectangle frontier. -/
theorem bottom_segment_subset_frontier_lowerRectangle {h : ℝ} (hh : 0 < h) :
    segment ℝ (corner 0) (corner 1) ⊆ frontier (lowerRectangle h) := by
  intro z hz
  have hcoord := mem_bottom_segment_iff.mp hz
  rw [(isClosed_lowerRectangle h).frontier_eq]
  refine ⟨?_, ?_⟩
  · exact ⟨hcoord.2.1, hcoord.2.2, by rw [hcoord.1], by simpa [hcoord.1] using hh.le⟩
  · intro hzint
    have hpos := (mem_interior_lowerRectangle_iff.mp hzint).2.2.1
    exact (ne_of_gt hpos) hcoord.1

/-- A strict bottom-side point belongs to the bottom arc away from its endpoints. -/
theorem strict_bottom_mem_segment_sdiff_endpoints {x : ℝ}
    (hx0 : 0 < x) (hx1 : x < 1) :
    (!₂[x, 0] : Plane) ∈ segment ℝ (corner 0) (corner 1) \ {corner 0, corner 1} := by
  refine ⟨mem_bottom_segment_iff.mpr ⟨rfl, hx0.le, hx1.le⟩, ?_⟩
  simp only [mem_insert_iff, mem_singleton_iff]
  rintro (hzero | hone)
  · have h := congrArg (fun p : Plane => p 0) hzero
    change x = 0 at h
    exact (ne_of_gt hx0) h
  · have h := congrArg (fun p : Plane => p 0) hone
    change x = 1 at h
    exact (ne_of_lt hx1) h

/-- Every square point at the top height lies on the rectangle frontier. -/
theorem top_mem_frontier_lowerRectangle {h : ℝ} {z : Plane}
    (hz : z ∈ unitSquare) (hzh : z 1 = h) :
    z ∈ frontier (lowerRectangle h) := by
  rw [(isClosed_lowerRectangle h).frontier_eq]
  refine ⟨mem_lowerRectangle_of_mem_unitSquare hz hzh.le, ?_⟩
  intro hzint
  have hlt := (mem_interior_lowerRectangle_iff.mp hzint).2.2.2
  exact (ne_of_lt hlt) hzh

/-- A point at positive top height cannot lie on the bottom segment. -/
theorem top_not_mem_bottom_segment {h : ℝ} {z : Plane}
    (hh : 0 < h) (hzh : z 1 = h) :
    z ∉ segment ℝ (corner 0) (corner 1) := by
  intro hz
  have hzero := (mem_bottom_segment_iff.mp hz).1
  exact (ne_of_gt hh) (hzh.symm.trans hzero)

/-- The top contact lies on the rectangle frontier outside the chosen bottom arc. -/
theorem top_mem_frontier_sdiff_bottom_segment {h : ℝ} {z : Plane}
    (hh : 0 < h) (hz : z ∈ unitSquare) (hzh : z 1 = h) :
    z ∈ frontier (lowerRectangle h) \ segment ℝ (corner 0) (corner 1) :=
  ⟨top_mem_frontier_lowerRectangle hz hzh, top_not_mem_bottom_segment hh hzh⟩

end Puzzling139335.HeightBarrier
