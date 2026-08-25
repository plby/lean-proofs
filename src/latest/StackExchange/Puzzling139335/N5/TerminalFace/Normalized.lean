import StackExchange.Puzzling139335.N5.TerminalFace
import StackExchange.Puzzling139335.N5.SideExclusion.Normalized

/-!
# The terminal support obstruction in the actual normalized dissection

The image of the source origin lies on the open top side because the
source is below the diagonal, the target has a top contact, and the
corner-free target avoids all square corners.
-/

open Set

namespace Puzzling139335.N5

open PlaneIsometries

/-- The terminal diagonal normal cannot occur for a corner-free piece
containing the center.  Every geometric premise comes from the actual
placement, source containment, or top contact. -/
theorem Normalized.terminal_top_normal_excludes_center {d : SquareDissection}
    (h : Normalized d) (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (he : e '' d.piece 0 = d.piece 3) {r : ℝ} (hr : 0 < r)
    (hrow₀ : linearMatrix e 1 0 = -r)
    (hrow₁ : linearMatrix e 1 1 = r)
    (hcontact : ∃ X ∈ d.piece 3, X 1 = 1) :
    squareCenter ∉ d.piece 3 := by
  have hzero : (0 : Plane) ∈ d.piece 0 := by
    have hcorner : corner 0 = (0 : Plane) := by
      apply plane_ext <;> norm_num [corner, Fin.ext_iff]
    exact hcorner ▸ h.bottom_left
  have hA : e 0 ∈ d.piece 3 := he ▸ mem_image_of_mem e hzero
  have hAS := d.piece_subset 3 hA
  have hApos := h.piece_three_coordinates_pos hA
  have htop : (e 0) 1 = 1 := by
    obtain ⟨X, hX, hXtop⟩ := hcontact
    rw [← he] at hX
    obtain ⟨p, hp, rfl⟩ := hX
    have hcoordinates := congrArg (fun q : Plane => q 1)
      (affine_apply_eq_matrix_coordinates e p)
    simp [hrow₀, hrow₁] at hcoordinates
    have hnonneg := mul_nonneg hr.le (sub_nonneg.mpr (h.below_diagonal hp))
    linarith only [hcoordinates, hXtop, hnonneg, hAS.2.2]
  have hright : (e 0) 0 < 1 := by
    apply lt_of_le_of_ne hAS.1.2
    intro heq
    have hcorner : e 0 = corner 2 := by
      apply plane_ext <;> simp [corner, heq, htop]
    exact no_corner_of_count_zero d 3 h.count_three 2 (hcorner ▸ hA)
  rw [← he]
  exact Puzzling139335.N5.terminal_top_normal_excludes_center
    (fun p hp => (d.piece_subset 0 hp).2.1) e hr hrow₀ hrow₁ htop hApos.1 hright

end Puzzling139335.N5
