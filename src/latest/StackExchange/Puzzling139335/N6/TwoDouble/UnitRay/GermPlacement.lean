import StackExchange.Puzzling139335.N6.TwoDouble.UnitRay.GermPlacement.Neighborhood
import StackExchange.Puzzling139335.N6.TwoDouble.UnitRay.GermPlacement.ConeRigidity
import StackExchange.Puzzling139335.DoubleCorner.MixedCorner

/-!
# Placement of an actual forty-five-degree germ at a double corner

A piece with a filled forty-five-degree cone germ at a corner occupied by
two Jordan pieces must use one of the two diagonal half-cones.  First the
germ puts the entire supporting image cone in the first quadrant. Actual
contact with an outer square side then places that cone on one side of the
diagonal; rigidity of an isometric forty-five-degree cone makes the
containment an equality. Reflections are allowed throughout.
-/

open Set Metric

namespace Puzzling139335.N6.TwoDouble.UnitRay

open AcuteCorner DoubleCorner

/-- The entire supporting image cone is exactly one of the two diagonal
half-cones, as a consequence of the actual germ and the two-piece cover. -/
theorem image_cone45_eq_at_double_corner
    {P Q : Set Plane} (hP : IsJordanRegion P) (hQ : IsJordanRegion Q)
    (hPsub : P ⊆ unitSquare) (hQsub : Q ⊆ unitSquare)
    (hdis : Disjoint (interior P) (interior Q)) (hzero : (0 : Plane) ∈ P)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (he0 : e 0 = 0)
    (hsupport : P ⊆ e '' cone45) (hgerm : SameBoundaryGerm P (e '' cone45) 0)
    {ε : ℝ} (hε : 0 < ε) (hcover : ball 0 ε ∩ unitSquare ⊆ P ∪ Q) :
    e '' cone45 = cone45 ∨ e '' cone45 = upperCone45 := by
  have hquad := GermPlacement.image_cone45_coordinates_nonneg hPsub e he0 hgerm
  obtain ⟨x, hxP, hxne, hxaxis⟩ := MixedCorner.exists_axis_contact_of_mem_zero
    hP hQ hPsub hQsub hdis hzero hε hcover
  have hxS := hPsub hxP
  rcases MixedCorner.image_cone45_diagonal_support_of_positive_axis_contact
      e he0 (hsupport hxP) hxne hxS.1.1 hxS.2.1 hxaxis with hupper | hlower
  · right
    apply GermPlacement.image_cone45_eq_upper_of_subset e he0
    intro y hy
    exact ⟨(hquad y hy).1, hupper y hy⟩
  · left
    apply GermPlacement.image_cone45_eq_of_subset e he0
    intro y hy
    exact ⟨(hquad y hy).2, hlower y hy⟩

/-- An actual filled forty-five-degree germ at a double corner is either
the lower diagonal cone germ or the upper diagonal cone germ. Both the
global support and the filled local germ are preserved in the conclusion. -/
theorem cone_germ_at_double_corner
    {P Q : Set Plane} (hP : IsJordanRegion P) (hQ : IsJordanRegion Q)
    (hPsub : P ⊆ unitSquare) (hQsub : Q ⊆ unitSquare)
    (hdis : Disjoint (interior P) (interior Q)) (hzero : (0 : Plane) ∈ P)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (he0 : e 0 = 0)
    (hsupport : P ⊆ e '' cone45) (hgerm : SameBoundaryGerm P (e '' cone45) 0)
    {ε : ℝ} (hε : 0 < ε) (hcover : ball 0 ε ∩ unitSquare ⊆ P ∪ Q) :
    (P ⊆ cone45 ∧ SameBoundaryGerm P cone45 0) ∨
      (P ⊆ upperCone45 ∧ SameBoundaryGerm P upperCone45 0) := by
  rcases image_cone45_eq_at_double_corner hP hQ hPsub hQsub hdis hzero
      e he0 hsupport hgerm hε hcover with hlower | hupper
  · left
    exact ⟨by simpa only [hlower] using hsupport, by simpa only [hlower] using hgerm⟩
  · right
    exact ⟨by simpa only [hupper] using hsupport, by simpa only [hupper] using hgerm⟩

/-- The same conclusion without a separate vertex-membership hypothesis:
the filled germ already supplies that membership. -/
theorem cone_germ_at_double_corner_of_germ
    {P Q : Set Plane} (hP : IsJordanRegion P) (hQ : IsJordanRegion Q)
    (hPsub : P ⊆ unitSquare) (hQsub : Q ⊆ unitSquare)
    (hdis : Disjoint (interior P) (interior Q))
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (he0 : e 0 = 0)
    (hsupport : P ⊆ e '' cone45) (hgerm : SameBoundaryGerm P (e '' cone45) 0)
    {ε : ℝ} (hε : 0 < ε) (hcover : ball 0 ε ∩ unitSquare ⊆ P ∪ Q) :
    (P ⊆ cone45 ∧ SameBoundaryGerm P cone45 0) ∨
      (P ⊆ upperCone45 ∧ SameBoundaryGerm P upperCone45 0) :=
  cone_germ_at_double_corner hP hQ hPsub hQsub hdis
    (GermPlacement.zero_mem_of_image_cone45_germ e he0 hgerm)
    e he0 hsupport hgerm hε hcover

end Puzzling139335.N6.TwoDouble.UnitRay
