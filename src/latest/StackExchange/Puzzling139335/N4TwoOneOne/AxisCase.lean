import StackExchange.Puzzling139335.N4TwoOneOne.AxisCase.Vertical
import StackExchange.Puzzling139335.N4TwoOneOne.AxisCase.Horizontal

/-!
# The cornerless fourth piece has no axis-aligned unit base

Both alternatives are excluded from actual image equalities and memberships.
Vertical placement would force a forbidden bottom contact. Horizontal placement
would preserve the source's height, which is too small to contain both the
square center and the top midpoint.
-/

namespace Puzzling139335.N4TwoOneOne

open PlaneIsometries

theorem axis_image_false {d : SquareDissection} {θ u v : ℝ}
    (hcfg : Configuration d) (h : SourceData d θ u v) (hc : d.HasProtectedCenter)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (he : e '' d.piece 0 = d.piece 3)
    (hAxis : linearMatrix e 0 0 = 0 ∨ linearMatrix e 1 0 = 0) : False := by
  rcases hAxis with hvertical | hhorizontal
  · exact vertical_axis_image_false hcfg h e he hvertical
  · exact horizontal_axis_image_false hcfg h hc e he hhorizontal

theorem fourth_image_column_nonzero {d : SquareDissection} {θ u v : ℝ}
    (hcfg : Configuration d) (h : SourceData d θ u v) (hc : d.HasProtectedCenter)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (he : e '' d.piece 0 = d.piece 3) :
    linearMatrix e 0 0 ≠ 0 ∧ linearMatrix e 1 0 ≠ 0 :=
  ⟨fun hzero => axis_image_false hcfg h hc e he (Or.inl hzero),
    fun hzero => axis_image_false hcfg h hc e he (Or.inr hzero)⟩

theorem axis_image_false_of_row_axis {d : SquareDissection} {θ u v : ℝ}
    (hcfg : Configuration d) (h : SourceData d θ u v) (hc : d.HasProtectedCenter)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (he : e '' d.piece 0 = d.piece 3)
    (hAxis : linearMatrix e 0 0 = 0 ∨ linearMatrix e 0 1 = 0) : False :=
  axis_image_false hcfg h hc e he
    ((RectangularHull.matrix_row_axis_iff_column_axis e).mp hAxis)

end Puzzling139335.N4TwoOneOne
