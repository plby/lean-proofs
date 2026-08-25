import StackExchange.Puzzling139335.N4Midline.EndpointMass.Core
import StackExchange.Puzzling139335.N4Midline.EndpointPlacement

/-!
# The mass contradiction after forcing the bottom endpoint

An actual upper-left endpoint placement has one of the two coordinate
forms covered by the half-square and quadrant mass obstructions. For an
upper-right placement, the whole dissection is reflected in the vertical
midline. The repeated-pair relation then identifies reflected piece `1`
with the original left piece. This keeps all mass comparisons in one
common square and one common quadrant.
-/

open Set

namespace Puzzling139335.SquareDissection

noncomputable section

open N4Midline ThreeCorners

/-- An actual upper-left endpoint placement cannot coexist with a
third original piece containing the square center in its interior. -/
theorem false_of_upperLeft_endpoint (d : SquareDissection)
    {i j c : Fin 4} (hij : i ≠ j) (hci : c ≠ i) (hcj : c ≠ j)
    (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (himage : e '' d.piece i = d.piece j)
    (hleft : d.piece i ⊆ leftHalfSquare)
    (hv : e bottomMidpoint = corner 3)
    (hframe : e (bottomMidpoint + (1 / 2 : ℝ) •
      (ray (Real.pi / 2) + perpRay (Real.pi / 2))) = squareCenter)
    (hc : squareCenter ∈ interior (d.piece c)) : False :=
  d.false_of_upperLeft_endpoint_coordinates hij hci hcj e
    (endpoint_upperLeft_coordinates e hv hframe) himage hleft hc

/-- Either upper-corner placement of the forced endpoint contradicts
the protected center in the other upper piece. The right-corner case
reflects the complete dissection and changes the source index to `1`. -/
theorem false_of_upper_endpoint_reflected_pair (d : SquareDissection)
    (hpair : midlineReflection '' d.piece 0 = d.piece 1)
    (hleft : d.piece 0 ⊆ leftHalfSquare)
    {b c : Fin 4} (hb : b = 2 ∨ b = 3) (hcTop : c = 2 ∨ c = 3) (hcb : c ≠ b)
    (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (himage : e '' d.piece 0 = d.piece b)
    (hv : e bottomMidpoint = corner b)
    (hframe : e (bottomMidpoint + (1 / 2 : ℝ) •
      (ray (Real.pi / 2) + perpRay (Real.pi / 2))) = squareCenter)
    (hc : squareCenter ∈ interior (d.piece c)) : False := by
  rcases hb with rfl | rfl
  · have hcThree : c = 3 := hcTop.resolve_left hcb
    subst c
    let d' := d.map midlineReflection (SquareSymmetry.cornerFlip_image_unitSquare 1)
    let f : Plane ≃ᵃⁱ[ℝ] Plane := e.trans midlineReflection
    have hsource : d'.piece 1 = d.piece 0 := by
      change midlineReflection '' d.piece 1 = d.piece 0
      rw [← hpair, image_image]
      simp only [midlineReflection, SquareSymmetry.cornerFlip_involutive, image_id']
    have hleft' : d'.piece 1 ⊆ leftHalfSquare := by
      rw [hsource]
      exact hleft
    have himage' : f '' d'.piece 1 = d'.piece 2 := by
      rw [hsource]
      change (e.trans midlineReflection) '' d.piece 0 = midlineReflection '' d.piece 2
      rw [← himage, image_image]
      rfl
    have hv' : f bottomMidpoint = corner 3 := by
      change midlineReflection (e bottomMidpoint) = corner 3
      rw [hv]
      ext i
      fin_cases i <;> norm_num [midlineReflection_apply, corner, Fin.ext_iff]
    have hreflectionCenter : midlineReflection squareCenter = squareCenter :=
      SquareSymmetry.cornerFlip_center 1
    have hframe' : f (bottomMidpoint + (1 / 2 : ℝ) •
        (ray (Real.pi / 2) + perpRay (Real.pi / 2))) = squareCenter := by
      change midlineReflection (e _) = squareCenter
      rw [hframe, hreflectionCenter]
    have hc' : squareCenter ∈ interior (d'.piece 3) := by
      change squareCenter ∈ interior (midlineReflection '' d.piece 3)
      have hmem := (mem_interior_image_affineIsometry midlineReflection).mpr hc
      simpa only [hreflectionCenter] using hmem
    exact d'.false_of_upperLeft_endpoint
      (by decide : (1 : Fin 4) ≠ 2) (by decide : (3 : Fin 4) ≠ 1)
      (by decide : (3 : Fin 4) ≠ 2) f himage' hleft' hv' hframe' hc'
  · have hcTwo : c = 2 := hcTop.resolve_right hcb
    subst c
    exact d.false_of_upperLeft_endpoint
      (by decide : (0 : Fin 4) ≠ 3) (by decide : (2 : Fin 4) ≠ 0)
      (by decide : (2 : Fin 4) ≠ 3) e himage hleft hv hframe hc

end

end Puzzling139335.SquareDissection
