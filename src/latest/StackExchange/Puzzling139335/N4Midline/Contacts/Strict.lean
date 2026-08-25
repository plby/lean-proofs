import StackExchange.Puzzling139335.N4Midline.Contacts.Algebra
import StackExchange.Puzzling139335.N4Midline.HalfContainment

/-!
# Strict supporting directions in the left half-square

The conclusions concern contacts of the actual piece. Only its cone
containments and the unit coordinate bounds from its square placements
are used.
-/

open Set

namespace Puzzling139335.N4Midline

open ThreeCorners

noncomputable section

/-- For two supporting frames separated by more than a quarter-turn,
the first coordinate at `B` can contact level one only at `C`. -/
theorem first_contact_subset_last_corner {P : Set Plane} {B C : Plane} {θ φ : ℝ}
    (hconeC : P ⊆ supportCone C φ)
    (hbound : inner ℝ (ray θ) (C - B) ≤ 1)
    (hgaplo : Real.pi / 2 < φ - θ) (hgaphigh : φ - θ < Real.pi) :
    levelOneContact P B (ray θ) ⊆ {C} := by
  have hcos : Real.cos (φ - θ) < 0 :=
    Real.cos_neg_of_pi_div_two_lt_of_lt hgaplo (by linarith [Real.pi_pos])
  have hsin : 0 < Real.sin (φ - θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [Real.pi_pos]) hgaphigh
  apply levelOneContact_subset_singleton_of_support hbound
  intro x hx
  apply strict_cone_support (hconeC hx)
  · simpa only [ray_inner_ray] using hcos
  · simpa only [ray_inner_perp] using neg_neg_of_pos hsin

/-- The second coordinate of the last frame can contact level one only
at the middle corner, for a strict quarter-turn separation. -/
theorem last_contact_subset_first_corner {P : Set Plane} {B C : Plane} {θ φ : ℝ}
    (hconeB : P ⊆ supportCone B θ)
    (hbound : inner ℝ (perpRay φ) (B - C) ≤ 1)
    (hgaplo : Real.pi / 2 < φ - θ) (hgaphigh : φ - θ < Real.pi) :
    levelOneContact P C (perpRay φ) ⊆ {B} := by
  have hcos : Real.cos (φ - θ) < 0 :=
    Real.cos_neg_of_pi_div_two_lt_of_lt hgaplo (by linarith [Real.pi_pos])
  have hsin : 0 < Real.sin (φ - θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [Real.pi_pos]) hgaphigh
  apply levelOneContact_subset_singleton_of_support hbound
  intro x hx
  apply strict_cone_support (hconeB hx)
  · rw [real_inner_comm, ray_inner_perp]
    exact neg_neg_of_pos hsin
  · rw [real_inner_comm, perp_inner_perp]
    exact hcos

/-- A strictly southwest coordinate has its only possible level-one
contact at the origin. -/
theorem negative_contact_subset_origin {P : Set Plane} {V e : Plane}
    (hP : P ⊆ leftHalfSquare)
    (hbound : inner ℝ e (0 - V) ≤ 1)
    (he0 : e 0 < 0) (he1 : e 1 < 0) :
    levelOneContact P V e ⊆ {0} := by
  apply levelOneContact_subset_singleton_of_support hbound
  intro x hx
  simpa only [sub_zero] using
    negative_coordinate_support (hP hx).1.1 (hP hx).2.1 he0 he1

/-- At the endpoint angle `π/2`, the second inward coordinate spans
at most one half in the left half-square. -/
theorem middle_perp_contact_empty_at_half_pi {P : Set Plane} {B : Plane}
    (hP : P ⊆ leftHalfSquare) (hB : B ∈ P) :
    levelOneContact P B (perpRay (Real.pi / 2)) = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  rintro x ⟨hxP, hxlevel⟩
  have hx0 := (hP hxP).1.1
  have hB0 := (hP hB).1.2
  simp only [Schoenflies.Plane.inner_eq, perpRay_zero, perpRay_one,
    Real.sin_pi_div_two, Real.cos_pi_div_two, PiLp.sub_apply] at hxlevel
  linarith

end

end Puzzling139335.N4Midline
