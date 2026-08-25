import StackExchange.Puzzling139335.N4OuterPair.Defs
import StackExchange.Puzzling139335.RectangularHull
import StackExchange.Puzzling139335.RectangularHull.CanonicalFrame

/-!
# Both outer side legs cannot reach the midline

The two bottom corners and two side contacts at height one half are actual
points of the lower outer piece.  They force its convex hull to be the full
lower half-square, since that piece is already contained in the half-square.
The unconditional rectangular-hull obstruction then excludes a protected
center.  No rectangular frame or convexity certificate is assumed.
-/

open Set

namespace Puzzling139335.N4OuterPair

namespace Configuration

variable {d : SquareDissection}

/-- Four actual extreme points force the lower piece's hull to be the whole
lower half-square, even when the piece itself is nonconvex. -/
theorem convexHull_eq_lower_half_of_full_height_legs (h : Configuration d)
    (hleft : Schoenflies.Plane.mk 0 (1 / 2) ∈ d.piece 0)
    (hright : Schoenflies.Plane.mk 1 (1 / 2) ∈ d.piece 0) :
    convexHull ℝ (d.piece 0) = horizontalBand 0 (1 / 2) := by
  have hhalf : (0 : ℝ) < 1 / 2 := by norm_num
  let R : RectangularHull.Frame := RectangularHull.unitFrame hhalf
  have hcarrier : R.carrier = horizontalBand 0 (1 / 2) :=
    RectangularHull.unitFrame_carrier hhalf
  have h00 : R.origin = Schoenflies.Plane.mk 0 0 := by
    ext i
    fin_cases i <;> simp [R, RectangularHull.unitFrame, Schoenflies.Plane.mk]
  have h10 : R.origin + R.first = Schoenflies.Plane.mk 1 0 := by
    ext i
    fin_cases i <;> simp [R, RectangularHull.unitFrame, Schoenflies.Plane.mk]
  have h11 : R.origin + R.first + R.second = Schoenflies.Plane.mk 1 (1 / 2) := by
    ext i
    fin_cases i <;> simp [R, RectangularHull.unitFrame, Schoenflies.Plane.mk]
  have h01 : R.origin + R.second = Schoenflies.Plane.mk 0 (1 / 2) := by
    ext i
    fin_cases i <;> simp [R, RectangularHull.unitFrame, Schoenflies.Plane.mk]
  have hvertices : R.vertices ⊆ d.piece 0 := by
    intro p hp
    simp only [RectangularHull.Frame.vertices, mem_insert_iff, mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · rw [h00]
      exact h.bottom_left_mk
    · rw [h10]
      exact h.bottom_right_mk
    · rw [h11]
      exact hright
    · rw [h01]
      exact hleft
  have hsubset : d.piece 0 ⊆ R.carrier := by
    rw [hcarrier]
    exact h.outer_halves.1
  have hHull : convexHull ℝ (d.piece 0) = R.carrier :=
    subset_antisymm (convexHull_min hsubset R.carrier_convex)
      (convexHull_mono hvertices)
  exact hHull.trans hcarrier

/-- The rectangular-hull witness is derived from actual side contacts. -/
theorem rectangular_hull_of_full_height_legs (h : Configuration d)
    (hleft : Schoenflies.Plane.mk 0 (1 / 2) ∈ d.piece 0)
    (hright : Schoenflies.Plane.mk 1 (1 / 2) ∈ d.piece 0) :
    HasRectangularHull (d.piece 0) := by
  have hhalf : (0 : ℝ) < 1 / 2 := by norm_num
  refine ⟨RectangularHull.unitFrame hhalf, ?_⟩
  rw [RectangularHull.unitFrame_carrier]
  exact h.convexHull_eq_lower_half_of_full_height_legs hleft hright

/-- In a protected-center dissection the two lower side legs cannot both
reach the midline. -/
theorem full_height_legs_impossible (h : Configuration d) (hc : d.HasProtectedCenter)
    (hleft : Schoenflies.Plane.mk 0 (1 / 2) ∈ d.piece 0)
    (hright : Schoenflies.Plane.mk 1 (1 / 2) ∈ d.piece 0) : False :=
  d.no_rectangular_hull hc 0 (h.rectangular_hull_of_full_height_legs hleft hright)

end Configuration

end Puzzling139335.N4OuterPair
