import StackExchange.Puzzling139335.N4TwoOneOne.AlignedFaces.Coordinates
import StackExchange.Puzzling139335.N4TwoOneOne.AlignedFaces.Intervals
import StackExchange.Puzzling139335.N4TwoOneOne.SideGeometry.TopIntervals

/-!
# The actual translations forced by outgoing alignment

The image of the intrinsic source corner is the extreme point on the fourth
piece's top interval. This determines the horizontal offset, after which the
actual top intervals force a translation distance of one third.
-/

open Set

namespace Puzzling139335.N4TwoOneOne

open PlaneIsometries AlignedOutgoing

variable {d : SquareDissection} {θ u v T : ℝ}

private theorem sourceCorner_top_mem (hcfg : Configuration d) (h : SourceData d θ u v)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (he : e '' d.piece 0 = d.piece 3)
    (h10 : linearMatrix e 1 0 = -Real.sin θ)
    (h11 : linearMatrix e 1 1 = Real.cos θ) :
    (!₂[(e (sourceCorner θ u v)) 0, 1] : Plane) ∈ d.piece 3 ∧
      (e (sourceCorner θ u v)) 0 ∈ Icc (0 : ℝ) 1 := by
  have hC : e (sourceCorner θ u v) ∈ d.piece 3 := by
    rw [← he]
    exact mem_image_of_mem e h.sourceCorner_mem
  refine ⟨?_, (d.piece_subset 3 hC).1⟩
  have heq : e (sourceCorner θ u v) = !₂[(e (sourceCorner θ u v)) 0, 1] :=
    plane_ext rfl (outgoing_sourceCorner_top hcfg h e he h10 h11)
  exact heq ▸ hC

theorem outgoing_positive_translate (hcfg : Configuration d) (h : SourceData d θ u v)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (he : e '' d.piece 0 = d.piece 3)
    (h10 : linearMatrix e 1 0 = -Real.sin θ)
    (h11 : linearMatrix e 1 1 = Real.cos θ)
    (h00 : linearMatrix e 0 0 = Real.cos θ)
    (h01 : linearMatrix e 0 1 = Real.sin θ)
    (hT : T ∈ Ioo (0 : ℝ) (1 / 2))
    (hDtop : ∀ x ∈ Icc (0 : ℝ) 1,
      (!₂[x, 1] : Plane) ∈ d.piece 3 ↔ T ≤ x ∧ x ≤ 1 - T) :
    horizontalShift (-T) '' d.piece 1 = d.piece 3 := by
  obtain ⟨hCtop, hCxfit⟩ := sourceCorner_top_mem hcfg h e he h10 h11
  have hCx := ((hDtop _ hCxfit).mp hCtop).2
  rw [outgoing_positive_x θ e h00 h01, eCoord_sourceCorner] at hCx
  have hright : (!₂[1 - T, 1] : Plane) ∈ d.piece 3 :=
    (hDtop (1 - T) ⟨by linarith [hT.2], by linarith [hT.1]⟩).mpr
      ⟨by linarith [hT.2], le_rfl⟩
  obtain ⟨p, hp, hpRight⟩ := he.symm ▸ hright
  have hpX : (e p) 0 = 1 - T := by rw [hpRight]; rfl
  rw [outgoing_positive_x θ e h00 h01] at hpX
  have hpE := (h.projection_bounds hp).1
  have htx : (e 0) 0 = 1 - T - u := by
    linarith only [hCx, hpX, hpE]
  have hty := outgoing_vertical_offset hcfg h e he h10 h11
  have hformula : ∀ p : Plane, e p = horizontalShift (-T) (rightMap θ u v p) := by
    intro p
    apply plane_ext
    · rw [outgoing_positive_x θ e h00 h01, htx]
      simp only [horizontalShift_zero, rightMap_zero_coord]
      ring
    · rw [outgoing_aligned_y θ e h10 h11, hty]
      simp only [horizontalShift_one, rightMap_one_coord]
      ring
  rw [← h.right_image, Set.image_image]
  have hf : (fun p : Plane => horizontalShift (-T) (rightMap θ u v p)) = e := by
    funext p
    exact (hformula p).symm
  rw [hf, he]

theorem outgoing_negative_translate (hcfg : Configuration d) (h : SourceData d θ u v)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (he : e '' d.piece 0 = d.piece 3)
    (h10 : linearMatrix e 1 0 = -Real.sin θ)
    (h11 : linearMatrix e 1 1 = Real.cos θ)
    (h00 : linearMatrix e 0 0 = -Real.cos θ)
    (h01 : linearMatrix e 0 1 = -Real.sin θ)
    (hT : T ∈ Ioo (0 : ℝ) (1 / 2))
    (hDtop : ∀ x ∈ Icc (0 : ℝ) 1,
      (!₂[x, 1] : Plane) ∈ d.piece 3 ↔ T ≤ x ∧ x ≤ 1 - T) :
    horizontalShift T '' d.piece 2 = d.piece 3 := by
  obtain ⟨hCtop, hCxfit⟩ := sourceCorner_top_mem hcfg h e he h10 h11
  have hCx := ((hDtop _ hCxfit).mp hCtop).1
  rw [outgoing_negative_x θ e h00 h01, eCoord_sourceCorner] at hCx
  have hleft : (!₂[T, 1] : Plane) ∈ d.piece 3 :=
    (hDtop T ⟨hT.1.le, by linarith [hT.2]⟩).mpr
      ⟨le_rfl, by linarith [hT.2]⟩
  obtain ⟨p, hp, hpLeft⟩ := he.symm ▸ hleft
  have hpX : (e p) 0 = T := by rw [hpLeft]; rfl
  rw [outgoing_negative_x θ e h00 h01] at hpX
  have hpE := (h.projection_bounds hp).1
  have htx : (e 0) 0 = T + u := by
    linarith only [hCx, hpX, hpE]
  have hty := outgoing_vertical_offset hcfg h e he h10 h11
  have hformula : ∀ p : Plane, e p = horizontalShift T (leftMap θ u v p) := by
    intro p
    apply plane_ext
    · rw [outgoing_negative_x θ e h00 h01, htx]
      simp only [horizontalShift_zero, leftMap_zero_coord]
      ring
    · rw [outgoing_aligned_y θ e h10 h11, hty]
      simp only [horizontalShift_one, leftMap_one_coord]
      ring
  rw [← h.left_image, Set.image_image]
  have hf : (fun p : Plane => horizontalShift T (leftMap θ u v p)) = e := by
    funext p
    exact (hformula p).symm
  rw [hf, he]

/-- Explicit actual top intervals determine the distance and the image set. -/
theorem outgoing_aligned_translation_of_intervals
    (hcfg : Configuration d) (h : SourceData d θ u v)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (he : e '' d.piece 0 = d.piece 3)
    (h10 : linearMatrix e 1 0 = -Real.sin θ)
    (h11 : linearMatrix e 1 1 = Real.cos θ)
    (hT : T ∈ Ioo (0 : ℝ) (1 / 2))
    (hRtop : ∀ x ∈ Icc (0 : ℝ) 1,
      (!₂[x, 1] : Plane) ∈ d.piece 1 ↔ 1 - T ≤ x)
    (hDtop : ∀ x ∈ Icc (0 : ℝ) 1,
      (!₂[x, 1] : Plane) ∈ d.piece 3 ↔ T ≤ x ∧ x ≤ 1 - T) :
    T = 1 / 3 ∧
      (horizontalShift (-(1 / 3 : ℝ)) '' d.piece 1 = d.piece 3 ∨
        horizontalShift (1 / 3 : ℝ) '' d.piece 2 = d.piece 3) := by
  rcases outgoing_aligned_rows θ e h10 h11 with ⟨h00, h01⟩ | ⟨h00, h01⟩
  · have hshift := outgoing_positive_translate hcfg h e he h10 h11 h00 h01 hT hDtop
    have hthird := right_shift_interval_third hT hRtop hDtop hshift
    refine ⟨hthird, Or.inl ?_⟩
    simpa only [hthird] using hshift
  · have hshift := outgoing_negative_translate hcfg h e he h10 h11 h00 h01 hT hDtop
    have hLtop : ∀ x ∈ Icc (0 : ℝ) 1,
        (!₂[x, 1] : Plane) ∈ d.piece 2 ↔ x ≤ T := by
      intro x hx
      have hmirror := h.top_right_mem_iff_reflected_left (1 - x)
      have harg : 1 - (1 - x) = x := by ring
      rw [harg] at hmirror
      refine hmirror.symm.trans ((hRtop (1 - x)
        ⟨by linarith [hx.2], by linarith [hx.1]⟩).trans ?_)
      constructor <;> intro hbound <;> linarith only [hbound]
    have hthird := left_shift_interval_third hT hLtop hDtop hshift
    refine ⟨hthird, Or.inr ?_⟩
    simpa only [hthird] using hshift

/-- The Jordan top-side geometry supplies the intervals, so no interval or
support-face condition is needed in this actual-placement theorem. -/
theorem outgoing_aligned_translation (hcfg : Configuration d) (h : SourceData d θ u v)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (he : e '' d.piece 0 = d.piece 3)
    (h10 : linearMatrix e 1 0 = -Real.sin θ)
    (h11 : linearMatrix e 1 1 = Real.cos θ) :
    horizontalShift (-(1 / 3 : ℝ)) '' d.piece 1 = d.piece 3 ∨
      horizontalShift (1 / 3 : ℝ) '' d.piece 2 = d.piece 3 := by
  obtain ⟨T, hT, hparts⟩ := h.exists_top_contact_intervals hcfg
  exact (outgoing_aligned_translation_of_intervals hcfg h e he h10 h11 hT
    (fun x hx => (hparts x hx).2.1) (fun x hx => (hparts x hx).2.2)).2

end Puzzling139335.N4TwoOneOne
