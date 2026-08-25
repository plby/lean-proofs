import StackExchange.Puzzling139335.SourceFaceBridge.Isometries
import StackExchange.Puzzling139335.SegmentCrossing

/-!
# The actual source base lies in the frontier

Lower-half-square containment supplies its supporting half-plane.  The
affine isometry bundles then transport the whole frontier segment to each
of the actual middle pieces.
-/

open Set

namespace Puzzling139335.SourceFaceBridge

noncomputable section

def negativeY : Plane →L[ℝ] ℝ := -PiLp.proj 2 (fun _ : Fin 2 => ℝ) 1

@[simp] theorem negativeY_apply (p : Plane) : negativeY p = -p 1 := rfl

theorem negativeY_surjective : Function.Surjective negativeY := by
  intro y
  exact ⟨point 0 (-y), by simp⟩

namespace SupportedSource

variable {d : FaceData} {reversed : Bool} {P : Set Plane}

theorem base_segment_subset (h : SupportedSource d reversed P) :
    segment ℝ (point 0 0) (point 1 0) ⊆ P := by
  intro p hp
  rw [segment_eq_image] at hp
  obtain ⟨t, ht, rfl⟩ := hp
  have heq : (1 - t) • point 0 0 + t • point 1 0 = point t 0 := by
    apply point_ext <;> simp [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  change (1 - t) • point 0 0 + t • point 1 0 ∈ P
  rw [heq]
  exact h.base_mem t ht

theorem base_frontier (h : SupportedSource d reversed P) :
    segment ℝ (point 0 0) (point 1 0) ⊆ frontier P := by
  apply SegmentCrossing.segment_subset_frontier_of_linear_support
    negativeY negativeY_surjective (c := 0)
  · intro p hp
    have hy := (h.source_subset hp).2.1
    change -p 1 ≤ 0
    linarith
  · exact h.base_segment_subset
  · simp
  · simp

theorem map_base_frontier (h : SupportedSource d reversed P)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) :
    segment ℝ (e (point 0 0)) (e (point 1 0)) ⊆ frontier (e '' P) := by
  have hs : e '' segment ℝ (point 0 0) (point 1 0) =
      segment ℝ (e (point 0 0)) (e (point 1 0)) :=
    image_segment ℝ e.toAffineEquiv.toAffineMap _ _
  have hf : e '' frontier P = frontier (e '' P) := e.toHomeomorph.image_frontier P
  rw [← hs, ← hf]
  exact image_mono h.base_frontier

theorem right_base_frontier (h : SupportedSource d reversed P) :
    segment ℝ (d.right (point 0 0)) (d.right (point 1 0)) ⊆
      frontier (d.right '' P) := by
  simpa only [FaceData.coe_rightIsometry] using h.map_base_frontier d.rightIsometry

theorem left_base_frontier (h : SupportedSource d reversed P) :
    segment ℝ (d.left reversed (point 0 0)) (d.left reversed (point 1 0)) ⊆
      frontier (d.left reversed '' P) := by
  simpa only [FaceData.coe_leftIsometry] using
    h.map_base_frontier (d.leftIsometry reversed)

theorem leftProper_base_frontier (h : SupportedSource d false P) :
    segment ℝ (d.leftProper (point 0 0)) (d.leftProper (point 1 0)) ⊆
      frontier (d.leftProper '' P) := h.left_base_frontier

theorem leftGlide_base_frontier (h : SupportedSource d true P) :
    segment ℝ (d.leftGlide (point 0 0)) (d.leftGlide (point 1 0)) ⊆
      frontier (d.leftGlide '' P) := h.left_base_frontier

end SupportedSource

end

end Puzzling139335.SourceFaceBridge
