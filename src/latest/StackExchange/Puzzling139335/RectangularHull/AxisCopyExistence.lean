import StackExchange.Puzzling139335.RectangularHull.NormalizedBands
import StackExchange.Puzzling139335.RectangularHull.GapCoverage
import StackExchange.Puzzling139335.RectangularHull.MatrixFit
import StackExchange.Puzzling139335.RectangularHull.AxisSegment

/-!
# One middle placement has an axis-aligned unit base

For height strictly below one half, three actual side-gap points force an
aligned middle hull. At height exactly one half, the four transformed
rectangle vertices force every fitted hull to be aligned.
-/

open Set

namespace Puzzling139335.RectangularHull

open PlaneIsometries

theorem NormalizedOuterBands.exists_axis_middle_copy {d : SquareDissection} {h : ℝ}
    (N : NormalizedOuterBands d h) :
    ∃ i : Fin 4, (i = 2 ∨ i = 3) ∧ ∃ e : Plane ≃ᵃⁱ[ℝ] Plane,
      e '' d.piece 0 = d.piece i ∧
        (linearMatrix e 0 0 = 0 ∨ linearMatrix e 0 1 = 0) := by
  obtain ⟨e, he⟩ := d.congruent 0 2
  obtain ⟨f, hf⟩ := d.congruent 0 3
  have hefit := N.isometry_hull_subset_square e he
  have hffit := N.isometry_hull_subset_square f hf
  by_cases hh : h < 1 / 2
  · have h2 : d.piece 2 ⊆ e '' axisBox h := by
      rw [N.isometry_hull_image e he]
      exact subset_convexHull ℝ _
    have h3 : d.piece 3 ⊆ f '' axisBox h := by
      rw [N.isometry_hull_image f hf]
      exact subset_convexHull ℝ _
    have haxis := gap_coverage_forces_axis_alignment d e f N.height_pos.le hh
      (fun _ hp => (N.bottom_subset hp).2.2)
      (fun _ hp => (N.top_subset hp).2.1) h2 h3 hefit hffit
    rcases haxis with heaxis | hfaxis
    · exact ⟨2, Or.inl rfl, e, he, heaxis⟩
    · exact ⟨3, Or.inr rfl, f, hf, hfaxis⟩
  · have hhge : (1 / 2 : ℝ) ≤ h := le_of_not_gt hh
    have h00 : e (!₂[0, 0] : Plane) ∈ unitSquare :=
      hefit (mem_image_of_mem e ⟨⟨by norm_num, by norm_num⟩, ⟨le_rfl, N.height_pos.le⟩⟩)
    have h10 : e (!₂[1, 0] : Plane) ∈ unitSquare :=
      hefit (mem_image_of_mem e ⟨⟨by norm_num, le_rfl⟩, ⟨le_rfl, N.height_pos.le⟩⟩)
    have h0h : e (!₂[0, h] : Plane) ∈ unitSquare :=
      hefit (mem_image_of_mem e ⟨⟨by norm_num, by norm_num⟩, ⟨N.height_pos.le, le_rfl⟩⟩)
    have h1h : e (!₂[1, h] : Plane) ∈ unitSquare :=
      hefit (mem_image_of_mem e ⟨⟨by norm_num, le_rfl⟩, ⟨N.height_pos.le, le_rfl⟩⟩)
    have haxis := affine_rectangle_fit_axis_aligned e hhge h00 h10 h0h h1h
    exact ⟨2, Or.inl rfl, e, he, (matrix_row_axis_iff_column_axis e).mpr haxis⟩

end Puzzling139335.RectangularHull
