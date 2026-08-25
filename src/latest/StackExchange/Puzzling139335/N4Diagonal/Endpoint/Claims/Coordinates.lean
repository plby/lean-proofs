import StackExchange.Puzzling139335.N4Midline.FrameCoordinates

/-!
# The four actual mixed-endpoint placements

At a bottom supporting endpoint, the inward frame has angle `π / 2`.
Sending this endpoint to corner one or three and the frame's diagonal
half-step to the square center leaves two possible images of the origin.
-/

open Set

namespace Puzzling139335.N4Diagonal.Endpoint

open ThreeCorners N4Midline SquareSymmetry

noncomputable section

private theorem endpoint_frame_origin (u : ℝ) :
    frameCoordinates !₂[u, 0] (Real.pi / 2) 0 = !₂[0, u] := by
  ext i
  fin_cases i <;> simp [Schoenflies.Plane.inner_eq, ray, perpRay]

/-- An endpoint placed at the bottom-right corner sends the origin to
one of the two incident sides at distance `u` from that corner. -/
theorem origin_images_of_endpoint_at_one (e : Plane ≃ᵃⁱ[ℝ] Plane) (u : ℝ)
    (hv : e !₂[u, 0] = corner 1)
    (hc : e (!₂[u, 0] + (1 / 2 : ℝ) •
      (ray (Real.pi / 2) + perpRay (Real.pi / 2))) = squareCenter) :
    e 0 = !₂[1, u] ∨ e 0 = !₂[1 - u, 0] := by
  rcases corner_frame_coordinates e !₂[u, 0] (Real.pi / 2) 1 hv hc with
    hform | hform
  · left
    have h := congrArg (cornerFlip 1) (hform 0)
    rw [cornerFlip_involutive, endpoint_frame_origin] at h
    simpa [cornerFlipPoint, corner, Fin.ext_iff] using h
  · right
    have h := congrArg (cornerFlip 1) (hform 0)
    rw [cornerFlip_involutive, endpoint_frame_origin] at h
    simpa [cornerFlipPoint, corner, Fin.ext_iff] using h

/-- An endpoint placed at the top-left corner sends the origin to
one of the two incident sides at distance `u` from that corner. -/
theorem origin_images_of_endpoint_at_three (e : Plane ≃ᵃⁱ[ℝ] Plane) (u : ℝ)
    (hv : e !₂[u, 0] = corner 3)
    (hc : e (!₂[u, 0] + (1 / 2 : ℝ) •
      (ray (Real.pi / 2) + perpRay (Real.pi / 2))) = squareCenter) :
    e 0 = !₂[0, 1 - u] ∨ e 0 = !₂[u, 1] := by
  rcases corner_frame_coordinates e !₂[u, 0] (Real.pi / 2) 3 hv hc with
    hform | hform
  · left
    have h := congrArg (cornerFlip 3) (hform 0)
    rw [cornerFlip_involutive, endpoint_frame_origin] at h
    simpa [cornerFlipPoint, corner, Fin.ext_iff] using h
  · right
    have h := congrArg (cornerFlip 3) (hform 0)
    rw [cornerFlip_involutive, endpoint_frame_origin] at h
    simpa [cornerFlipPoint, corner, Fin.ext_iff] using h

end

end Puzzling139335.N4Diagonal.Endpoint
