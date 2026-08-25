import StackExchange.Puzzling139335.N4TwoOneOne.TopGap
import StackExchange.Puzzling139335.PlaneIsometries.Matrix

/-!
# Coordinates of an outgoing-aligned fourth placement

The specified outgoing normal determines the first matrix row up to its sign.
An actual top contact and the actual source corner then determine the vertical
translation exactly.
-/

open Set

namespace Puzzling139335.N4TwoOneOne

open PlaneIsometries

theorem outgoing_aligned_rows (θ : ℝ) (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (h10 : linearMatrix e 1 0 = -Real.sin θ)
    (h11 : linearMatrix e 1 1 = Real.cos θ) :
    (linearMatrix e 0 0 = Real.cos θ ∧ linearMatrix e 0 1 = Real.sin θ) ∨
      (linearMatrix e 0 0 = -Real.cos θ ∧ linearMatrix e 0 1 = -Real.sin θ) := by
  obtain ⟨a, b, _hab, hm | hm⟩ := linearMatrix_classification e
  · left
    rw [hm] at h10 h11 ⊢
    change b = -Real.sin θ at h10
    change a = Real.cos θ at h11
    change a = Real.cos θ ∧ -b = Real.sin θ
    exact ⟨h11, by linarith only [h10]⟩
  · right
    rw [hm] at h10 h11 ⊢
    change b = -Real.sin θ at h10
    change -a = Real.cos θ at h11
    change a = -Real.cos θ ∧ b = -Real.sin θ
    exact ⟨by linarith only [h11], h10⟩

theorem outgoing_aligned_y (θ : ℝ) (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (h10 : linearMatrix e 1 0 = -Real.sin θ)
    (h11 : linearMatrix e 1 1 = Real.cos θ) (p : Plane) :
    (e p) 1 = fCoord θ p + (e 0) 1 := by
  rw [affine_apply_eq_matrix_coordinates e p]
  simp [h10, h11, fCoord]

theorem outgoing_positive_x (θ : ℝ) (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (h00 : linearMatrix e 0 0 = Real.cos θ)
    (h01 : linearMatrix e 0 1 = Real.sin θ) (p : Plane) :
    (e p) 0 = eCoord θ p + (e 0) 0 := by
  rw [affine_apply_eq_matrix_coordinates e p]
  simp [h00, h01, eCoord]

theorem outgoing_negative_x (θ : ℝ) (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (h00 : linearMatrix e 0 0 = -Real.cos θ)
    (h01 : linearMatrix e 0 1 = -Real.sin θ) (p : Plane) :
    (e p) 0 = -eCoord θ p + (e 0) 0 := by
  rw [affine_apply_eq_matrix_coordinates e p]
  simp [h00, h01, eCoord]
  ring

theorem eCoord_sourceCorner (θ u v : ℝ) :
    eCoord θ (sourceCorner θ u v) = u := by
  have hc := congrArg (fun t : ℝ => u * t) (Real.sin_sq_add_cos_sq θ)
  dsimp [eCoord, sourceCorner]
  nlinarith only [hc]

theorem fCoord_sourceCorner (θ u v : ℝ) :
    fCoord θ (sourceCorner θ u v) = v := by
  have hc := congrArg (fun t : ℝ => v * t) (Real.sin_sq_add_cos_sq θ)
  dsimp [fCoord, sourceCorner]
  nlinarith only [hc]

theorem outgoing_vertical_offset {d : SquareDissection} {θ u v : ℝ}
    (hcfg : Configuration d) (h : SourceData d θ u v)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (he : e '' d.piece 0 = d.piece 3)
    (h10 : linearMatrix e 1 0 = -Real.sin θ)
    (h11 : linearMatrix e 1 1 = Real.cos θ) : (e 0) 1 = 1 - v := by
  have hC : e (sourceCorner θ u v) ∈ d.piece 3 := by
    rw [← he]
    exact mem_image_of_mem e h.sourceCorner_mem
  have hCy := (d.piece_subset 3 hC).2.2
  rw [outgoing_aligned_y θ e h10 h11, fCoord_sourceCorner] at hCy
  obtain ⟨p, hp, hpTop⟩ := he.symm ▸ h.top_midpoint_mem hcfg
  have hpY : (e p) 1 = 1 := by rw [hpTop]; rfl
  rw [outgoing_aligned_y θ e h10 h11] at hpY
  have hpF := (h.projection_bounds hp).2
  linarith only [hCy, hpY, hpF]

theorem outgoing_sourceCorner_top {d : SquareDissection} {θ u v : ℝ}
    (hcfg : Configuration d) (h : SourceData d θ u v)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (he : e '' d.piece 0 = d.piece 3)
    (h10 : linearMatrix e 1 0 = -Real.sin θ)
    (h11 : linearMatrix e 1 1 = Real.cos θ) :
    (e (sourceCorner θ u v)) 1 = 1 := by
  rw [outgoing_aligned_y θ e h10 h11, fCoord_sourceCorner,
    outgoing_vertical_offset hcfg h e he h10 h11]
  ring

end Puzzling139335.N4TwoOneOne
