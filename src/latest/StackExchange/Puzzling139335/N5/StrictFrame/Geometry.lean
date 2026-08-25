import StackExchange.Puzzling139335.N5.StrictFrame.Placement
import StackExchange.Puzzling139335.N5.StrictFrame.Contacts
import StackExchange.Puzzling139335.N5.StrictFrame.Algebra
import StackExchange.Puzzling139335.N5Facet.Elementary

/-!
# Strict bounds from actual points in the singleton placement

The coordinate formulas describe the actual isometry.  Square fit, the
positive diagonal contact, and the exclusion of a long diagonal contact
give every strict support inequality used in the N5 calculation.
-/

open Set

namespace Puzzling139335.N5

/-- Once an actual diagonal source point is known to lie below the center,
all endpoint equalities in the nonstrict corner frame are excluded. -/
theorem Normalized.strict_parameters_of_diagonal_bound {d : SquareDissection}
    (h : Normalized d) (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (he : e '' d.piece 0 = d.piece 2) {C : Plane} {c s : ℝ}
    (hC : C ∈ d.piece 0) (hunit : c ^ 2 + s ^ 2 = 1)
    (hs : 0 ≤ s) (hsc : s ≤ c) (hc : 0 < c)
    (hA : s * C 0 ≤ c * C 1) (hB : c * (1 - C 0) ≤ s * C 1)
    (hf : CornerPlacementForm e C c s)
    (hdiag : C 0 = C 1 → C 0 < 1 / 2) :
    0 < s ∧ s < c ∧ C 1 < C 0 ∧ C 0 < c ∧ c < 1 ∧
      0 < c * C 1 - s * C 0 ∧ c * C 0 + s * C 1 < 1 := by
  have hd := h.frame_sum_lt_one e he hf
  have hspos := StrictFrame.sin_pos_of_strict_offset hunit hc hs hB hd
  obtain ⟨hkh, hsc'⟩ := StrictFrame.strict_order_of_diagonal_bound hc hs hsc
    (h.below_diagonal hC) hA hB hdiag
  have hefit : e '' d.piece 0 ⊆ unitSquare := by
    rw [he]
    exact d.piece_subset 2
  obtain ⟨a, ha, hF⟩ := h.exists_positive_diagonal_point
  have hsupport := (hf.support hefit hF).2
  have hleg : (c - s) * a ≤ c * C 1 - s * C 0 := by
    change -s * a + c * a ≤ -s * C 0 + c * C 1 at hsupport
    nlinarith only [hsupport]
  have hz := StrictFrame.transverse_offset_pos_of_leg ha hsc' hleg
  obtain ⟨hhc, hc1⟩ := StrictFrame.height_lt_cos_of_strict_offsets hunit hc hspos hd hz
  exact ⟨hspos, hsc', hkh, hhc, hc1, hz, hd⟩

/-- Any actual right-side contact, in particular the endpoint of the
complete right leg, obeys the strict half-angle ratio bound. -/
theorem Normalized.right_contact_lt_frame_ratio {d : SquareDissection}
    (h : Normalized d) (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (he : e '' d.piece 0 = d.piece 2) {C : Plane} {c s b : ℝ}
    (hunit : c ^ 2 + s ^ 2 = 1) (hc : 0 < c) (hs : 0 < s)
    (hf : CornerPlacementForm e C c s)
    (hb : Schoenflies.Plane.mk 1 b ∈ d.piece 0) : b < s / (1 + c) := by
  have hefit : e '' d.piece 0 ⊆ unitSquare := by
    rw [he]
    exact d.piece_subset 2
  have hsupport : c + s * b ≤ c * C 0 + s * C 1 := by
    have hsupp := (hf.support hefit hb).1
    change c * 1 + s * b ≤ c * C 0 + s * C 1 at hsupp
    simpa only [mul_one] using hsupp
  exact N5Facet.side_fit_lt_ratio hc hs hunit hsupport (h.frame_sum_lt_one e he hf)

end Puzzling139335.N5
