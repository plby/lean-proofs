import StackExchange.Puzzling139335.PlaneIsometries.Matrix

/-!
# Right contacts determine the first affine coordinate

Two copies of the same set, contained in the square and both meeting its
right side, have the same horizontal translation whenever their first
linear rows agree.  Their relative isometry consequently fixes the first
coordinate, so it is a vertical translation or a horizontal reflection.
-/

open Set

namespace Puzzling139335.N4Axial

open PlaneIsometries

/-- A common first linear row, together with actual right-side contacts,
determines the entire first-coordinate function of two placements. -/
theorem first_coordinates_eq_of_right_contacts_equal_first_rows
    (P : Set Plane) (e f : Plane ≃ᵃⁱ[ℝ] Plane)
    (he : e '' P ⊆ unitSquare) (hf : f '' P ⊆ unitSquare)
    (heright : (e '' P ∩ {p | p 0 = 1}).Nonempty)
    (hfright : (f '' P ∩ {p | p 0 = 1}).Nonempty)
    (h00 : linearMatrix e 0 0 = linearMatrix f 0 0)
    (h01 : linearMatrix e 0 1 = linearMatrix f 0 1) :
    ∀ p, (e p) 0 = (f p) 0 := by
  have he0 (p : Plane) : (e p) 0 =
      linearMatrix e 0 0 * p 0 + linearMatrix e 0 1 * p 1 + (e 0) 0 := by
    simpa using congrArg (fun q : Plane => q 0)
      (affine_apply_eq_matrix_coordinates e p)
  have hf0 (p : Plane) : (f p) 0 =
      linearMatrix f 0 0 * p 0 + linearMatrix f 0 1 * p 1 + (f 0) 0 := by
    simpa using congrArg (fun q : Plane => q 0)
      (affine_apply_eq_matrix_coordinates f p)
  obtain ⟨x, hxP, hxright⟩ := heright
  obtain ⟨a, ha, rfl⟩ := hxP
  obtain ⟨y, hyP, hyright⟩ := hfright
  obtain ⟨b, hb, rfl⟩ := hyP
  have hfa : (f a) 0 ≤ 1 := (hf (mem_image_of_mem f ha)).1.2
  have heb : (e b) 0 ≤ 1 := (he (mem_image_of_mem e hb)).1.2
  have horigin : (e 0) 0 = (f 0) 0 := by
    change (e a) 0 = 1 at hxright
    change (f b) 0 = 1 at hyright
    rw [he0, h00, h01] at hxright heb
    rw [hf0] at hyright hfa
    linarith
  intro p
  rw [he0, hf0, h00, h01, horigin]

/-- Every affine plane isometry fixing the first coordinate is either a
vertical translation or reflection in a horizontal line. -/
theorem vertical_translation_or_horizontal_reflection_of_first_coordinate
    (g : Plane ≃ᵃⁱ[ℝ] Plane) (hg : ∀ p, (g p) 0 = p 0) :
    (∃ t : ℝ, ∀ p, (g p) 0 = p 0 ∧ (g p) 1 = p 1 + t) ∨
      (∃ b : ℝ, ∀ p, (g p) 0 = p 0 ∧ (g p) 1 = b - p 1) := by
  have ht : (g 0) 0 = 0 := by simpa using hg 0
  obtain ⟨c, s, _, hform | hform⟩ := affine_coordinate_classification g
  · have hzero := congrArg (fun p : Plane => p 0)
      (hform (EuclideanSpace.single 0 1))
    have hone := congrArg (fun p : Plane => p 0)
      (hform (EuclideanSpace.single 1 1))
    rw [hg] at hzero hone
    norm_num [directCoordinates, ht] at hzero hone
    have hc : c = 1 := by linarith
    have hs : s = 0 := by linarith
    refine Or.inl ⟨(g 0) 1, ?_⟩
    intro p
    refine ⟨hg p, ?_⟩
    simpa [directCoordinates, hc, hs] using
      congrArg (fun q : Plane => q 1) (hform p)
  · have hzero := congrArg (fun p : Plane => p 0)
      (hform (EuclideanSpace.single 0 1))
    have hone := congrArg (fun p : Plane => p 0)
      (hform (EuclideanSpace.single 1 1))
    rw [hg] at hzero hone
    norm_num [reversingCoordinates, ht] at hzero hone
    have hc : c = 1 := by linarith
    have hs : s = 0 := by linarith
    refine Or.inr ⟨(g 0) 1, ?_⟩
    intro p
    refine ⟨hg p, ?_⟩
    simpa [reversingCoordinates, hc, hs, sub_eq_add_neg, add_comm] using
      congrArg (fun q : Plane => q 1) (hform p)

end Puzzling139335.N4Axial
