import StackExchange.Puzzling139335.DoubleCorner

/-!
# Transport of an actual filled forty-five-degree corner

A repeated corner in a two-owner square corner supplies a genuine filled
half-quadrant germ. This file normalizes that germ and transports it through
an arbitrary actual congruence to another square corner.
-/

open Set

namespace Puzzling139335.N6.TwoDouble.UnitRay

open AcuteCorner DoubleCorner SquareSymmetry ReflectionSeparation

noncomputable section

theorem diagonal_image_upperCone45 : diagonal '' upperCone45 = cone45 := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact hq
  · intro hp
    exact ⟨diagonal p, hp, diagonal_involutive p⟩

/-- The source half-quadrant can always be chosen as the lower one by
interchanging the normalized coordinates when necessary. -/
theorem source_normalized_filled45 (d : SquareDissection)
    {i k j : Fin 4} (hik : i ≠ k)
    (hi : corner j ∈ d.piece i) (hk : corner j ∈ d.piece k)
    (hother : ∀ l, l ≠ i → l ≠ k → corner j ∉ d.piece l)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (he : e '' d.piece i = d.piece k)
    (hfix : e (corner j) = corner j) :
    ∃ f : Plane ≃ᵃⁱ[ℝ] Plane, f (corner j) = 0 ∧
      f '' d.piece i ⊆ cone45 ∧ SameBoundaryGerm (f '' d.piece i) cone45 0 := by
  rcases d.double_corner_normalized_halfCones hik hi hk hother e he hfix with h | h
  · exact ⟨cornerFlip j, cornerFlip_corner j, h.1, h.2.2.1⟩
  · let f := (cornerFlip j).trans diagonal
    have himage : f '' d.piece i = diagonal '' (cornerFlip j '' d.piece i) := by
      rw [image_image]
      rfl
    have hfzero : f (corner j) = 0 := by
      change diagonal (cornerFlip j (corner j)) = 0
      rw [cornerFlip_corner]
      ext r
      fin_cases r <;> simp
    refine ⟨f, hfzero, ?_, ?_⟩
    · rw [himage, ← diagonal_image_upperCone45]
      exact image_mono h.1
    · have hg := h.2.2.1.image_affineIsometry diagonal
      have hd0 : diagonal 0 = (0 : Plane) := by ext r; fin_cases r <;> simp
      simpa only [← himage, diagonal_image_upperCone45, hd0] using hg

/-- Transporting a normalized filled cone through the actual region
congruence produces an origin-fixed cone in the target square coordinates. -/
theorem transported_filled45 {P Q : Set Plane} {a : Plane}
    (f : Plane ≃ᵃⁱ[ℝ] Plane) (hfa : f a = 0)
    (hsub : f '' P ⊆ cone45) (hgerm : SameBoundaryGerm (f '' P) cone45 0)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (he : e '' P = Q) (j : Fin 4)
    (hea : e a = corner j) :
    ∃ g : Plane ≃ᵃⁱ[ℝ] Plane, g 0 = 0 ∧
      cornerFlip j '' Q ⊆ g '' cone45 ∧
      SameBoundaryGerm (cornerFlip j '' Q) (g '' cone45) 0 := by
  let g := f.symm.trans (e.trans (cornerFlip j))
  have hf0 : f.symm 0 = a := by rw [← hfa, f.symm_apply_apply]
  have hg0 : g 0 = 0 := by
    change cornerFlip j (e (f.symm 0)) = 0
    rw [hf0, hea, cornerFlip_corner]
  have himage : g '' (f '' P) = cornerFlip j '' Q := by
    rw [image_image, ← he, image_image]
    congr 1
    funext p
    change cornerFlip j (e (f.symm (f p))) = cornerFlip j (e p)
    rw [f.symm_apply_apply]
  refine ⟨g, hg0, ?_, ?_⟩
  · rw [← himage]
    exact image_mono hsub
  · simpa only [himage, hg0] using hgerm.image_affineIsometry g

end

end Puzzling139335.N6.TwoDouble.UnitRay
