import StackExchange.Puzzling139335.UnitPairs.Defs
import StackExchange.Puzzling139335.CornerSupport.Frames
import StackExchange.Puzzling139335.SquareSymmetry.Basic

/-!
# Membership, support, and transport of full square corners

A full relative corner neighborhood includes its vertex.  Hence every full
square corner is a supporting right corner.  These properties are invariant
under arbitrary Euclidean affine isometries, including reflections.
-/

open Set Metric

namespace Puzzling139335.UnitPairs

variable {P : Set Plane} {a : Plane}

/-- The vertex of a full relative corner neighborhood belongs to the set. -/
theorem IsFullSquareCorner.mem (h : IsFullSquareCorner P a) : a ∈ P := by
  obtain ⟨e, i, ε, hε, _, hea, hnear⟩ := h
  have hc : corner i ∈ e '' P :=
    hnear ⟨mem_ball_self hε, corner_mem_unitSquare i⟩
  obtain ⟨b, hb, heb⟩ := hc
  have hba : b = a := e.injective (heb.trans hea.symm)
  simpa only [hba] using hb

/-- A full square corner is in particular a supporting right corner. -/
theorem IsFullSquareCorner.isSupportCorner (h : IsFullSquareCorner P a) :
    IsSupportCorner P a := by
  obtain ⟨e, i, ε, hε, hsub, hea, hnear⟩ := h
  have hc : corner i ∈ e '' P :=
    hnear ⟨mem_ball_self hε, corner_mem_unitSquare i⟩
  have hs := isSupportCorner_preimage e hsub i hc
  simpa only [← hea, e.symm_apply_apply] using hs

/-- Transport of a full square corner by any Euclidean affine isometry. -/
theorem IsFullSquareCorner.map (h : IsFullSquareCorner P a)
    (g : Plane ≃ᵃⁱ[ℝ] Plane) : IsFullSquareCorner (g '' P) (g a) := by
  obtain ⟨e, i, ε, hε, hsub, hea, hnear⟩ := h
  let f := g.symm.trans e
  have himage : f '' (g '' P) = e '' P := by
    simp only [f, AffineIsometryEquiv.coe_trans, image_image, Function.comp_def,
      g.symm_apply_apply]
  refine ⟨f, i, ε, hε, ?_, ?_, ?_⟩
  · simpa only [himage] using hsub
  · change e (g.symm (g a)) = corner i
    rw [g.symm_apply_apply, hea]
  · simpa only [himage] using hnear

/-- Normalize a full square corner to the origin while retaining both the
global square containment and a full relative neighborhood at the origin. -/
theorem IsFullSquareCorner.exists_normalized (h : IsFullSquareCorner P a) :
    ∃ f : Plane ≃ᵃⁱ[ℝ] Plane, f a = 0 ∧ f '' P ⊆ unitSquare ∧
      ∃ ε : ℝ, 0 < ε ∧ ball 0 ε ∩ unitSquare ⊆ f '' P := by
  obtain ⟨e, i, ε, hε, hsub, hea, hnear⟩ := h
  let f := e.trans (SquareSymmetry.cornerFlip i)
  refine ⟨f, ?_, ?_, ε, hε, ?_⟩
  · change SquareSymmetry.cornerFlip i (e a) = 0
    rw [hea, SquareSymmetry.cornerFlip_corner]
  · rintro _ ⟨x, hx, rfl⟩
    exact (SquareSymmetry.cornerFlip_mem_unitSquare i).mpr
      (hsub (mem_image_of_mem e hx))
  · intro y hy
    have hd : dist (SquareSymmetry.cornerFlip i y) (corner i) = dist y 0 := by
      rw [← SquareSymmetry.cornerFlip_zero i]
      exact (SquareSymmetry.cornerFlip i).isometry.dist_eq y 0
    have hflip : SquareSymmetry.cornerFlip i y ∈ ball (corner i) ε ∩ unitSquare :=
      ⟨mem_ball.mpr (hd ▸ mem_ball.mp hy.1),
        (SquareSymmetry.cornerFlip_mem_unitSquare i).mpr hy.2⟩
    obtain ⟨x, hx, hexy⟩ := hnear hflip
    refine ⟨x, hx, ?_⟩
    change SquareSymmetry.cornerFlip i (e x) = y
    rw [hexy, SquareSymmetry.cornerFlip_involutive]

end Puzzling139335.UnitPairs
