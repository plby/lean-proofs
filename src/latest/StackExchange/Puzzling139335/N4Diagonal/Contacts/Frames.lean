import StackExchange.Puzzling139335.N4Diagonal.Defs
import StackExchange.Puzzling139335.N4Diagonal.Contacts.Strict

/-!
# Actual inward frames in the diagonal model

The recorded supporting directions give positively oriented cones at
the two remaining corner types. Their actual square placements give
unit bounds on both inward coordinates.
-/

open Set

namespace Puzzling139335.N4Diagonal

open ThreeCorners

noncomputable section

namespace Model

theorem first_cone (m : Model) :
    m.P ⊆ supportCone m.p (m.θ + Real.pi / 2) := by
  intro x hx
  obtain ⟨hfirst, hsecond⟩ := m.first_support x hx
  change 0 ≤ inner ℝ (ray (m.θ + Real.pi / 2)) (x - m.p) ∧
    0 ≤ inner ℝ (perpRay (m.θ + Real.pi / 2)) (x - m.p)
  rw [N4Midline.ray_add_pi_div_two, N4Midline.perp_add_pi_div_two,
    inner_neg_left]
  exact ⟨hfirst, neg_nonneg.mpr hsecond⟩

theorem last_cone (m : Model) :
    m.P ⊆ supportCone m.q (m.β + Real.pi) := by
  intro x hx
  obtain ⟨hfirst, hsecond⟩ := m.last_support x hx
  change 0 ≤ inner ℝ (ray (m.β + Real.pi)) (x - m.q) ∧
    0 ≤ inner ℝ (perpRay (m.β + Real.pi)) (x - m.q)
  rw [ray_add_pi, perp_add_pi, inner_neg_left, inner_neg_left]
  exact ⟨neg_nonneg.mpr hfirst, neg_nonneg.mpr hsecond⟩

theorem first_frame_center (m : Model) :
    m.e (m.p + (1 / 2 : ℝ) •
      (ray (m.θ + Real.pi / 2) + perpRay (m.θ + Real.pi / 2))) = squareCenter := by
  rw [N4Midline.ray_add_pi_div_two, N4Midline.perp_add_pi_div_two,
    ← sub_eq_add_neg, ← m.first_center, m.e.apply_symm_apply]

theorem last_frame_center (m : Model) :
    m.f (m.q + (1 / 2 : ℝ) •
      (ray (m.β + Real.pi) + perpRay (m.β + Real.pi))) = squareCenter := by
  have hc : m.q + (1 / 2 : ℝ) •
      (ray (m.β + Real.pi) + perpRay (m.β + Real.pi)) =
      m.f.symm squareCenter := by
    rw [m.last_center, ray_add_pi, perp_add_pi]
    simp only [smul_add, smul_neg, sub_eq_add_neg]
    abel
  rw [hc, m.f.apply_symm_apply]

theorem first_inward_bounds (m : Model) {x : Plane} (hx : x ∈ m.P) :
    inner ℝ (perpRay m.θ) (x - m.p) ∈ Icc (0 : ℝ) 1 ∧
      inner ℝ (-ray m.θ) (x - m.p) ∈ Icc (0 : ℝ) 1 := by
  have h := N4Midline.inward_coordinates_mem_Icc m.e m.p
    (m.θ + Real.pi / 2) m.firstCorner m.first_corner m.first_frame_center
    (m.first_subset (mem_image_of_mem m.e hx))
  simpa only [N4Midline.ray_add_pi_div_two, N4Midline.perp_add_pi_div_two] using h

theorem last_inward_bounds (m : Model) {x : Plane} (hx : x ∈ m.P) :
    inner ℝ (-ray m.β) (x - m.q) ∈ Icc (0 : ℝ) 1 ∧
      inner ℝ (-perpRay m.β) (x - m.q) ∈ Icc (0 : ℝ) 1 := by
  have h := N4Midline.inward_coordinates_mem_Icc m.f m.q
    (m.β + Real.pi) m.lastCorner m.last_corner m.last_frame_center
    (m.last_subset (mem_image_of_mem m.f hx))
  simpa only [ray_add_pi, perp_add_pi] using h

end Model

end

end Puzzling139335.N4Diagonal
