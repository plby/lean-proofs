import StackExchange.Puzzling139335.N4TwoOneOne.SideGeometry
import StackExchange.Puzzling139335.N4TwoOneOne.SupportContacts
import StackExchange.Puzzling139335.N4TwoOneOne.Preparation.Nonaxis

/-!
# Preparing the fourth piece's geometry from actual dissection data

The fourth piece has two distinct top contacts. Consequently an additional
nontrivial vertical-side contact would force a square corner in that piece.
This removes the exceptional-contact hypotheses from the side geometry.
-/

open Set

namespace Puzzling139335.N4TwoOneOne

open SupportContacts

namespace SourceData

variable {d : SquareDissection} {θ u v : ℝ}

/-- The supporting source model is a consequence of the actual placement
identities and the actual source-corner memberships. -/
theorem source_support (h : SourceData d θ u v) :
    SourceSupport (d.piece 0) θ u v where
  subset_square := d.piece_subset 0
  base_left := h.bottom_left
  base_right := h.bottom_right
  upper_corner := h.sourceCorner_mem
  e_le := fun _ hp => (h.projection_bounds hp).1
  f_le := fun _ hp => (h.projection_bounds hp).2

/-- The strict top interval contains two distinct actual fourth-piece points. -/
theorem fourth_top_hasTwoSidePoints (h : SourceData d θ u v)
    (hcfg : Configuration d) : HasTwoSidePoints (d.piece 3) 1 true := by
  obtain ⟨T, hT, _, hleft, hright, _⟩ := h.exists_top_geometry hcfg
  refine ⟨!₂[T, 1], hleft, !₂[1 - T, 1], hright, ?_, rfl, rfl⟩
  intro heq
  have hx := congrArg (fun p : Plane => p 0) heq
  change T = 1 - T at hx
  linarith only [hT.2, hx]

/-- A nontrivial contact with either vertical side would combine with the
actual top contact to put a forbidden square corner in the fourth piece. -/
theorem fourth_vertical_contact_subsingleton (h : SourceData d θ u v)
    (hcfg : Configuration d) (upper : Bool) :
    (d.piece 3 ∩ {p : Plane | p 0 = sideLevel upper}).Subsingleton := by
  rintro p ⟨hp, hpx⟩ q ⟨hq, hqx⟩
  by_contra hpq
  obtain ⟨e, he⟩ := d.congruent 0 3
  have hfit : e '' d.piece 0 ⊆ unitSquare := by
    rw [he]
    exact d.piece_subset 3
  have htop : HasTwoSidePoints (e '' d.piece 0) 1 true := by
    rw [he]
    exact h.fourth_top_hasTwoSidePoints hcfg
  have hside : HasTwoSidePoints (e '' d.piece 0) 0 upper := by
    rw [he]
    exact ⟨p, hp, q, hq, hpq, hpx, hqx⟩
  obtain ⟨k, hk⟩ := exists_square_corner_of_adjacent_contacts h.source_support
    (h.cos_pos hcfg) h.sin_pos e hfit (by decide : (0 : Fin 2) ≠ 1) hside htop
  rw [he] at hk
  exact hcfg.cornerless k hk

theorem fourth_left_contact_subsingleton (h : SourceData d θ u v)
    (hcfg : Configuration d) :
    (d.piece 3 ∩ {p : Plane | p 0 = 0}).Subsingleton := by
  simpa only [sideLevel, Bool.false_eq_true, if_false] using
    h.fourth_vertical_contact_subsingleton hcfg false

theorem fourth_right_contact_subsingleton (h : SourceData d θ u v)
    (hcfg : Configuration d) :
    (d.piece 3 ∩ {p : Plane | p 0 = 1}).Subsingleton := by
  simpa only [sideLevel, if_true] using h.fourth_vertical_contact_subsingleton hcfg true

/-- The full side geometry no longer requires assumptions on the fourth
piece's contacts with the two vertical sides. -/
theorem exists_derived_side_geometry (h : SourceData d θ u v)
    (hcfg : Configuration d) : ∃ l T : ℝ, SideContactGeometry d θ u v l T :=
  h.exists_side_geometry hcfg (h.fourth_left_contact_subsingleton hcfg)
    (h.fourth_right_contact_subsingleton hcfg)

/-- The top row of any actual placement has two distinct actual supporting
source points. -/
theorem fourth_top_support_points (h : SourceData d θ u v) (hcfg : Configuration d)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (he : e '' d.piece 0 = d.piece 3) :
    HasTwoSupportPoints (d.piece 0) (PlaneIsometries.linearMatrix e 1 0)
      (PlaneIsometries.linearMatrix e 1 1) := by
  have hfit : e '' d.piece 0 ⊆ unitSquare := by
    rw [he]
    exact d.piece_subset 3
  have htop : HasTwoSidePoints (e '' d.piece 0) 1 true := by
    rw [he]
    exact h.fourth_top_hasTwoSidePoints hcfg
  simpa only [sideNormalX, sideNormalY, sideSign, if_true, one_mul] using
    hasTwoSupportPoints_of_hasTwoSidePoints e hfit htop

/-- Actual congruence, derived side geometry, and actual nontrivial top
support are obtained simultaneously from the normalized configuration. -/
theorem exists_derived_geometry (h : SourceData d θ u v) (hcfg : Configuration d) :
    ∃ e : Plane ≃ᵃⁱ[ℝ] Plane, ∃ l T : ℝ,
      e '' d.piece 0 = d.piece 3 ∧ SideContactGeometry d θ u v l T ∧
      HasTwoSupportPoints (d.piece 0) (PlaneIsometries.linearMatrix e 1 0)
        (PlaneIsometries.linearMatrix e 1 1) := by
  obtain ⟨e, he⟩ := d.congruent 0 3
  obtain ⟨l, T, hgeometry⟩ := h.exists_derived_side_geometry hcfg
  exact ⟨e, l, T, he, hgeometry, h.fourth_top_support_points hcfg e he⟩

end SourceData

end Puzzling139335.N4TwoOneOne
