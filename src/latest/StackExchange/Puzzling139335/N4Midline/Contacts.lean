import StackExchange.Puzzling139335.N4Midline.Contacts.Angles
import StackExchange.Puzzling139335.N4Midline.Contacts.Strict

/-!
# Finite bottom contacts for the two upper placements

For a piece confined to the left half-square, the two ordered supporting
right-angle frames cannot supply an interval on a opposite unit side
when the last frame puts the square center inside the piece. Each of
the four possible coordinate contacts is empty or a single actual point
of the piece.
-/

open Set

namespace Puzzling139335.N4Midline

open ThreeCorners

noncomputable section

/-- The two southwest-pointing coordinates have their only possible
contact at the origin. -/
theorem southwest_contacts_subset_origin {P : Set Plane} {B C : Plane} {θ φ : ℝ}
    (hP : P ⊆ leftHalfSquare) (hzero : (0 : Plane) ∈ P) (hB : B ∈ P)
    (hθ : θ ∈ Ico (Real.pi / 2) Real.pi)
    (hφ : φ ∈ Ioo Real.pi (3 * Real.pi / 2))
    (hBbound : ∀ x ∈ P, inner ℝ (perpRay θ) (x - B) ≤ 1)
    (hCbound : ∀ x ∈ P, inner ℝ (ray φ) (x - C) ≤ 1) :
    levelOneContact P B (perpRay θ) ⊆ {0} ∧
      levelOneContact P C (ray φ) ⊆ {0} := by
  constructor
  · rcases eq_or_lt_of_le hθ.1 with hθeq | hθstrict
    · rw [← hθeq, middle_perp_contact_empty_at_half_pi hP hB]
      exact empty_subset _
    · apply negative_contact_subset_origin hP (hBbound 0 hzero)
      · simpa only [perpRay_zero] using neg_neg_of_pos (sin_pos_of_left_frame_angle hθ)
      · simpa only [perpRay_one] using cos_neg_of_strict_left_frame_angle ⟨hθstrict, hθ.2⟩
  · apply negative_contact_subset_origin hP (hCbound 0 hzero)
    · simpa only [ray_zero] using cos_neg_of_right_frame_angle hφ
    · simpa only [ray_one] using sin_neg_of_right_frame_angle hφ

/-- At a gap of exactly a quarter-turn, both facing contacts are empty:
a contact would identify a frame center outside the piece with the
frame center in its interior. -/
theorem facing_contacts_empty_at_quarter_turn {P : Set Plane} {B C : Plane} {θ φ : ℝ}
    (hP : P ⊆ leftHalfSquare) (hB : B ∈ P) (hC : C ∈ P)
    (hconeB : P ⊆ supportCone B θ) (hconeC : P ⊆ supportCone C φ)
    (hθ : θ ∈ Icc (Real.pi / 2) Real.pi)
    (hgap : φ - θ = Real.pi / 2)
    (hbound : inner ℝ (ray θ) (C - B) ≤ 1)
    (hcenter : frameCenter C φ ∈ interior P) :
    levelOneContact P B (ray θ) = ∅ ∧
      levelOneContact P C (perpRay φ) = ∅ := by
  have hφ : φ = θ + Real.pi / 2 := by linarith
  have hcenters : frameCenter C φ ≠ frameCenter B θ := by
    intro heq
    apply frameCenter_not_mem_interior_left hP (hP hB) hθ
    rwa [← heq]
  have hlevels (x : Plane) (hx : x ∈ P) :
      inner ℝ (ray θ) (x - B) < 1 ∧
        inner ℝ (perpRay φ) (x - C) < 1 := by
    subst φ
    exact adjacent_frames_strict_levels (hconeB hC) (hconeC hB) hbound
      hcenters (hconeB hx) (hconeC hx)
  constructor
  · apply eq_empty_iff_forall_notMem.mpr
    rintro x ⟨hxP, hxlevel⟩
    exact (ne_of_lt (hlevels x hxP).1) hxlevel
  · apply eq_empty_iff_forall_notMem.mpr
    rintro x ⟨hxP, hxlevel⟩
    exact (ne_of_lt (hlevels x hxP).2) hxlevel

/-- Each possible opposite-side contact of the two upper frames is
confined to a specified singleton. This uses the actual piece, not its
convex hull. -/
theorem four_contacts_subset_singletons {P : Set Plane} {B C : Plane} {θ φ : ℝ}
    (hP : P ⊆ leftHalfSquare) (hzero : (0 : Plane) ∈ P)
    (hB : B ∈ P) (hC : C ∈ P)
    (hconeB : P ⊆ supportCone B θ) (hconeC : P ⊆ supportCone C φ)
    (hθ : θ ∈ Icc (Real.pi / 2) Real.pi)
    (horder : θ + Real.pi / 2 ≤ φ) (hφ : φ ≤ 3 * Real.pi / 2)
    (hBbounds : ∀ x ∈ P, inner ℝ (ray θ) (x - B) ≤ 1 ∧
      inner ℝ (perpRay θ) (x - B) ≤ 1)
    (hCbounds : ∀ x ∈ P, inner ℝ (ray φ) (x - C) ≤ 1 ∧
      inner ℝ (perpRay φ) (x - C) ≤ 1)
    (hcenter : frameCenter C φ ∈ interior P) :
    levelOneContact P B (ray θ) ⊆ {C} ∧
      levelOneContact P B (perpRay θ) ⊆ {0} ∧
      levelOneContact P C (ray φ) ⊆ {0} ∧
      levelOneContact P C (perpRay φ) ⊆ {B} := by
  obtain ⟨hφstrict, hθstrict, hgap⟩ :=
    ordered_angles_of_frameCenter_mem_interior hP hC hθ horder hφ hcenter
  obtain ⟨hBperp, hCray⟩ := southwest_contacts_subset_origin hP hzero hB
    ⟨hθ.1, hθstrict⟩ hφstrict
    (fun x hx => (hBbounds x hx).2) (fun x hx => (hCbounds x hx).1)
  have hfacing : levelOneContact P B (ray θ) ⊆ {C} ∧
      levelOneContact P C (perpRay φ) ⊆ {B} := by
    rcases eq_or_lt_of_le hgap.1 with heq | hlt
    · obtain ⟨hfirst, hlast⟩ := facing_contacts_empty_at_quarter_turn hP hB hC
        hconeB hconeC hθ heq.symm (hBbounds C hC).1 hcenter
      rw [hfirst, hlast]
      exact ⟨empty_subset _, empty_subset _⟩
    · exact ⟨first_contact_subset_last_corner hconeC (hBbounds C hC).1 hlt hgap.2,
        last_contact_subset_first_corner hconeB (hCbounds B hB).2 hlt hgap.2⟩
  exact ⟨hfacing.1, hBperp, hCray, hfacing.2⟩

/-- In particular, every possible bottom-contact set is a subsingleton. -/
theorem four_contacts_subsingleton {P : Set Plane} {B C : Plane} {θ φ : ℝ}
    (hP : P ⊆ leftHalfSquare) (hzero : (0 : Plane) ∈ P)
    (hB : B ∈ P) (hC : C ∈ P)
    (hconeB : P ⊆ supportCone B θ) (hconeC : P ⊆ supportCone C φ)
    (hθ : θ ∈ Icc (Real.pi / 2) Real.pi)
    (horder : θ + Real.pi / 2 ≤ φ) (hφ : φ ≤ 3 * Real.pi / 2)
    (hBbounds : ∀ x ∈ P, inner ℝ (ray θ) (x - B) ≤ 1 ∧
      inner ℝ (perpRay θ) (x - B) ≤ 1)
    (hCbounds : ∀ x ∈ P, inner ℝ (ray φ) (x - C) ≤ 1 ∧
      inner ℝ (perpRay φ) (x - C) ≤ 1)
    (hcenter : frameCenter C φ ∈ interior P) :
    (levelOneContact P B (ray θ)).Subsingleton ∧
      (levelOneContact P B (perpRay θ)).Subsingleton ∧
      (levelOneContact P C (ray φ)).Subsingleton ∧
      (levelOneContact P C (perpRay φ)).Subsingleton := by
  obtain ⟨hBr, hBp, hCr, hCp⟩ := four_contacts_subset_singletons hP hzero hB hC
    hconeB hconeC hθ horder hφ hBbounds hCbounds hcenter
  exact ⟨subsingleton_of_subset_singleton hBr, subsingleton_of_subset_singleton hBp,
    subsingleton_of_subset_singleton hCr, subsingleton_of_subset_singleton hCp⟩

end

end Puzzling139335.N4Midline
