import StackExchange.Puzzling139335.N4HalfLeg.Spans.Extrema
import StackExchange.Puzzling139335.N4HalfLeg.Spans.MatrixTransport
import StackExchange.Puzzling139335.N4HalfLeg.Spans.IntervalCover

/-!
# Extracting source-face spans from actual right-side contacts

Compactness supplies the lowest and highest actual contacts. Pulling them
back through the placement gives two actual maximizers of its first matrix
row. The orthogonal-matrix identity orders those source points by height
and computes their vertical separation from the physical contact span.
-/

open Set

namespace Puzzling139335.N4HalfLeg

open PlaneIsometries SourceFaceBridge

private theorem affine_first_coordinate (e : Plane ≃ᵃⁱ[ℝ] Plane) (p : Plane) :
    e p 0 = linearMatrix e 0 0 * p 0 + linearMatrix e 0 1 * p 1 + e 0 0 :=
  congrArg (fun q : Plane => q 0) (affine_apply_eq_matrix_coordinates e p)

/-- Every actual right-side contact pulls back to a source support point
for the first row of the placement matrix. -/
theorem source_support_of_right_contact {P Q : Set Plane}
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (he : e '' P = Q) (hQS : Q ⊆ unitSquare)
    {y : ℝ} (hy : Schoenflies.Plane.mk 1 y ∈ Q) :
    SupportsAt P (linearMatrix e 0 0) (linearMatrix e 0 1)
      (e.symm (Schoenflies.Plane.mk 1 y)) := by
  have hsource : e.symm (Schoenflies.Plane.mk 1 y) ∈ P := by
    obtain ⟨p, hp, heq⟩ : Schoenflies.Plane.mk 1 y ∈ e '' P := by
      rw [he]
      exact hy
    have hpre : e.symm (Schoenflies.Plane.mk 1 y) = p := by
      rw [← heq, e.symm_apply_apply]
    rw [hpre]
    exact hp
  refine ⟨hsource, ?_⟩
  intro p hp
  have hupper : e p 0 ≤ 1 := (hQS (he ▸ mem_image_of_mem e hp)).1.2
  rw [affine_first_coordinate] at hupper
  have hcontact :
      linearMatrix e 0 0 * (e.symm (Schoenflies.Plane.mk 1 y)) 0 +
        linearMatrix e 0 1 * (e.symm (Schoenflies.Plane.mk 1 y)) 1 + e 0 0 = 1 := by
    simpa only [e.apply_symm_apply, Schoenflies.Plane.mk_zero] using
      (affine_first_coordinate e (e.symm (Schoenflies.Plane.mk 1 y))).symm
  linarith only [hupper, hcontact]

/-- Construct a complete actual right-side span from compactness, nontrivial
contact, square containment, and the derived acute-normal bounds. -/
theorem exists_rightSpan {P Q : Set Plane} (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (he : e '' P = Q) (hQ : IsCompact Q) (hQS : Q ⊆ unitSquare)
    (hcontact : (Q ∩ {p : Plane | p 0 = 1}).Nontrivial)
    (hc : (4 / 5 : ℝ) < linearMatrix e 0 0)
    (hs : 0 < linearMatrix e 0 1) : Nonempty (RightSpan P Q e) := by
  obtain ⟨bottom, top, hbt, hbottom, htop, hbounds⟩ :=
    exists_right_contact_extrema hQ hcontact
  let p := e.symm (Schoenflies.Plane.mk 1 bottom)
  let q := e.symm (Schoenflies.Plane.mk 1 top)
  have hp : SupportsAt P (linearMatrix e 0 0) (linearMatrix e 0 1) p :=
    source_support_of_right_contact e he hQS hbottom
  have hq : SupportsAt P (linearMatrix e 0 0) (linearMatrix e 0 1) q :=
    source_support_of_right_contact e he hQS htop
  have hunit : (linearMatrix e 0 0) ^ 2 + (linearMatrix e 0 1) ^ 2 = 1 := by
    simpa [pow_two] using linearMatrix_row_dot e 0 0
  obtain ⟨lower, upper, hlower, hupper, hspan⟩ :
      ∃ lower upper : Plane,
        SupportsAt P (linearMatrix e 0 0) (linearMatrix e 0 1) lower ∧
        SupportsAt P (linearMatrix e 0 0) (linearMatrix e 0 1) upper ∧
        upper 1 - lower 1 = linearMatrix e 0 0 * (top - bottom) := by
    rcases vertical_span_or_neg_of_right_preimages e bottom top with h | h
    · exact ⟨p, q, hp, hq, h⟩
    · exact ⟨q, p, hq, hp, h⟩
  exact ⟨{
    bottom := bottom
    top := top
    bottom_lt_top := hbt
    bottom_mem := hbottom
    top_mem := htop
    bounds := hbounds
    face := {
      lower := lower
      upper := upper
      length := top - bottom
      length_pos := sub_pos.mpr hbt
      c_gt_four_fifths := hc
      s_pos := hs
      normal_unit := hunit
      lower_support := hlower
      upper_support := hupper
      vertical_span := hspan }
    length_eq := rfl }⟩

/-- A chosen actual span, with no additional geometric assumptions. -/
noncomputable def rightSpan {P Q : Set Plane} (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (he : e '' P = Q) (hQ : IsCompact Q) (hQS : Q ⊆ unitSquare)
    (hcontact : (Q ∩ {p : Plane | p 0 = 1}).Nontrivial)
    (hc : (4 / 5 : ℝ) < linearMatrix e 0 0)
    (hs : 0 < linearMatrix e 0 1) : RightSpan P Q e :=
  Classical.choice (exists_rightSpan e he hQ hQS hcontact hc hs)

end Puzzling139335.N4HalfLeg
