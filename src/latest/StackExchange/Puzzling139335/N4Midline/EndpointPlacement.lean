import StackExchange.Puzzling139335.N4Midline.Endpoint
import StackExchange.Puzzling139335.N4Midline.FrameCoordinates

/-!
# The two placements at the forced endpoint

At the bottom midpoint, the inward frame with angle `π / 2` has
coordinates `(y, 1 / 2 - x)`. A placement sending the frame vertex to the
upper-left corner and its diagonal half-step to the square center is
therefore one of two explicit affine isometries.
-/

namespace Puzzling139335.N4Midline

open ThreeCorners SquareSymmetry

noncomputable section

@[simp] theorem endpoint_frameCoordinates_zero (p : Plane) :
    frameCoordinates bottomMidpoint (Real.pi / 2) p 0 = p 1 := by
  simp [frameCoordinates_zero, Schoenflies.Plane.inner_eq, ray, bottomMidpoint]

@[simp] theorem endpoint_frameCoordinates_one (p : Plane) :
    frameCoordinates bottomMidpoint (Real.pi / 2) p 1 = (1 / 2 : ℝ) - p 0 := by
  simp [frameCoordinates_one, Schoenflies.Plane.inner_eq, perpRay, bottomMidpoint]

/-- The two possible upper-left placements of the forced endpoint
frame, stated in scalar coordinates. -/
theorem endpoint_upperLeft_coordinates (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (hv : e bottomMidpoint = corner 3)
    (hc : e (bottomMidpoint + (1 / 2 : ℝ) •
      (ray (Real.pi / 2) + perpRay (Real.pi / 2))) = squareCenter) :
    (∀ p, (e p) 0 = (1 / 2 : ℝ) - p 0 ∧ (e p) 1 = 1 - p 1) ∨
      (∀ p, (e p) 0 = p 1 ∧ (e p) 1 = p 0 + 1 / 2) := by
  rcases corner_frame_coordinates e bottomMidpoint (Real.pi / 2) 3 hv hc with
    hdirect | hswap
  · right
    intro p
    have hx := congrArg (fun q : Plane => q 0) (hdirect p)
    have hy := congrArg (fun q : Plane => q 1) (hdirect p)
    norm_num [cornerFlipPoint, corner, Fin.ext_iff, Schoenflies.Plane.inner_eq,
      ray, perpRay, bottomMidpoint] at hx hy
    exact ⟨hx, by linarith⟩
  · left
    intro p
    have hx := congrArg (fun q : Plane => q 0) (hswap p)
    have hy := congrArg (fun q : Plane => q 1) (hswap p)
    norm_num [cornerFlipPoint, corner, Fin.ext_iff, Schoenflies.Plane.inner_eq,
      ray, perpRay, bottomMidpoint] at hx hy
    exact ⟨hx, by linarith⟩

/-- The same exhaustive placement alternatives as equalities of points. -/
theorem endpoint_upperLeft_form (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (hv : e bottomMidpoint = corner 3)
    (hc : e (bottomMidpoint + (1 / 2 : ℝ) •
      (ray (Real.pi / 2) + perpRay (Real.pi / 2))) = squareCenter) :
    (∀ p, e p = !₂[(1 / 2 : ℝ) - p 0, 1 - p 1]) ∨
      (∀ p, e p = !₂[p 1, p 0 + 1 / 2]) := by
  rcases endpoint_upperLeft_coordinates e hv hc with hhalfturn | hquarterturn
  · left
    intro p
    ext i
    fin_cases i
    · exact (hhalfturn p).1
    · exact (hhalfturn p).2
  · right
    intro p
    ext i
    fin_cases i
    · exact (hquarterturn p).1
    · exact (hquarterturn p).2

end

end Puzzling139335.N4Midline
