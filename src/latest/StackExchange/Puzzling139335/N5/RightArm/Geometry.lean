import StackExchange.Puzzling139335.N5.RightArm.Inverse
import StackExchange.Puzzling139335.N5.Normalized
import StackExchange.Puzzling139335.N5Facet.Elementary

/-!
# The actual right-side contact determines the surviving source arm

The contact point belongs to both physical pieces.  Its preimage therefore
belongs to the source piece, so square containment and the lower-diagonal
bound constrain the actual inverse endpoint.
-/

open Set

namespace Puzzling139335.N5

private theorem rightArm_inverse_mem {P Q : Set Plane}
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (he : e '' P = Q) {q : Plane} (hq : q ∈ Q) :
    e.symm q ∈ P := by
  have hqimage : q ∈ e '' P := by rw [he]; exact hq
  obtain ⟨p, hp, hpq⟩ := hqimage
  rw [← hpq, e.symm_apply_apply]
  exact hp

/-- The direct row order is impossible: the actual inverse endpoint must
fit in the source square, while the actual shared endpoint obeys the first
support inequality of the singleton placement. -/
theorem right_arm_direct_impossible (d : SquareDissection)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (he : e '' d.piece 0 = d.piece 2)
    {C : Plane} {c s b : ℝ}
    (hunit : c ^ 2 + s ^ 2 = 1) (hc : 0 < c) (hs : 0 < s)
    (hc₁ : c < 1) (hb : 0 < b) (hCy : C 1 < c)
    (hform : ∀ p, e p =
      !₂[1 - c * C 0 - s * C 1 + c * p 0 + s * p 1,
         1 + s * C 0 - c * C 1 - s * p 0 + c * p 1])
    (hE₀ : Schoenflies.Plane.mk 1 b ∈ d.piece 0)
    (hE₂ : Schoenflies.Plane.mk 1 b ∈ d.piece 2) : False := by
  have hf : CornerPlacementForm e C c s := Or.inl hform
  have hefit : e '' d.piece 0 ⊆ unitSquare := by
    rw [he]
    exact d.piece_subset 2
  have hsupport := (hf.support hefit hE₀).1
  change c * 1 + s * b ≤ c * C 0 + s * C 1 at hsupport
  have hsupport' : c * (1 - C 0) + s * (b - C 1) ≤ 0 := by
    nlinarith only [hsupport]
  have hpre := rightArm_inverse_mem e he hE₂
  rw [direct_inverse_right_point hunit hform] at hpre
  have hendpoint := (d.piece_subset 0 hpre).1.2
  change C 0 + (1 - b) * s ≤ 1 at hendpoint
  exact N5Facet.wrong_right_arm_impossible hc hs hc₁ hb rfl hCy hendpoint hsupport'

/-- The actual shared right-side point eliminates the direct row order,
leaving the swapped placement formula. -/
theorem right_arm_swapped_form_of_contact (d : SquareDissection)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (he : e '' d.piece 0 = d.piece 2)
    {C : Plane} {c s b : ℝ} (hf : CornerPlacementForm e C c s)
    (hunit : c ^ 2 + s ^ 2 = 1) (hc : 0 < c) (hs : 0 < s)
    (hc₁ : c < 1) (hb : 0 < b) (hCy : C 1 < c)
    (hE₀ : Schoenflies.Plane.mk 1 b ∈ d.piece 0)
    (hE₂ : Schoenflies.Plane.mk 1 b ∈ d.piece 2) :
    ∀ p, e p =
      !₂[1 + s * C 0 - c * C 1 - s * p 0 + c * p 1,
         1 - c * C 0 - s * C 1 + c * p 0 + s * p 1] := by
  rcases hf with hform | hform
  · exact (right_arm_direct_impossible d e he hunit hc hs hc₁ hb hCy
      hform hE₀ hE₂).elim
  · exact hform

/-- The surviving inverse endpoint is an actual point of the prototype. -/
theorem right_arm_source_endpoint_mem_of_contact (d : SquareDissection)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (he : e '' d.piece 0 = d.piece 2)
    {C : Plane} {c s b : ℝ} (hf : CornerPlacementForm e C c s)
    (hunit : c ^ 2 + s ^ 2 = 1) (hc : 0 < c) (hs : 0 < s)
    (hc₁ : c < 1) (hb : 0 < b) (hCy : C 1 < c)
    (hE₀ : Schoenflies.Plane.mk 1 b ∈ d.piece 0)
    (hE₂ : Schoenflies.Plane.mk 1 b ∈ d.piece 2) :
    !₂[C 0 - (1 - b) * c, C 1 - (1 - b) * s] ∈ d.piece 0 := by
  have hform := right_arm_swapped_form_of_contact d e he hf hunit hc hs hc₁ hb hCy
    hE₀ hE₂
  have hpre := rightArm_inverse_mem e he hE₂
  rwa [swapped_inverse_right_point hunit hform] at hpre

/-- Applying the actual lower-diagonal source bound to the surviving
inverse endpoint yields the source-arm inequality. -/
theorem Normalized.right_arm_inequality_of_contact {d : SquareDissection}
    (h : Normalized d) (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (he : e '' d.piece 0 = d.piece 2) {C : Plane} {c s b : ℝ}
    (hf : CornerPlacementForm e C c s)
    (hunit : c ^ 2 + s ^ 2 = 1) (hc : 0 < c) (hs : 0 < s)
    (hc₁ : c < 1) (hb : 0 < b) (hCy : C 1 < c)
    (hE₀ : Schoenflies.Plane.mk 1 b ∈ d.piece 0)
    (hE₂ : Schoenflies.Plane.mk 1 b ∈ d.piece 2) :
    (1 - b) * (c - s) ≤ C 0 - C 1 := by
  have hpre := right_arm_source_endpoint_mem_of_contact d e he hf hunit hc hs hc₁ hb hCy
    hE₀ hE₂
  have hbelow := h.below_diagonal hpre
  change C 1 - (1 - b) * s ≤ C 0 - (1 - b) * c at hbelow
  nlinarith only [hbelow]

/-- The strict source-coordinate and contact-height bounds place the
source corner below the height required by the center's inverse image. -/
theorem Normalized.right_arm_height_bound_of_contact {d : SquareDissection}
    (h : Normalized d) (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (he : e '' d.piece 0 = d.piece 2) {C : Plane} {c s b : ℝ}
    (hf : CornerPlacementForm e C c s)
    (hunit : c ^ 2 + s ^ 2 = 1) (hc : 0 < c) (hs : 0 < s)
    (hsc : s < c) (hc₁ : c < 1) (hCx : C 0 < c) (hCy : C 1 < c)
    (hb : 0 < b) (hbhalf : b < 1 / 2)
    (hE₀ : Schoenflies.Plane.mk 1 b ∈ d.piece 0)
    (hE₂ : Schoenflies.Plane.mk 1 b ∈ d.piece 2) : C 1 < (c + s) / 2 := by
  have hsource := h.right_arm_inequality_of_contact e he hf hunit hc hs hc₁ hb hCy hE₀ hE₂
  exact N5Facet.surviving_right_arm_excludes_center hsc hCx hbhalf rfl hsource

/-- The center is not even a boundary point of the singleton-corner piece:
its actual inverse image has negative second coordinate. -/
theorem Normalized.center_not_mem_singleton_of_right_contact {d : SquareDissection}
    (h : Normalized d) (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (he : e '' d.piece 0 = d.piece 2) {C : Plane} {c s b : ℝ}
    (hf : CornerPlacementForm e C c s)
    (hunit : c ^ 2 + s ^ 2 = 1) (hc : 0 < c) (hs : 0 < s)
    (hsc : s < c) (hc₁ : c < 1) (hCx : C 0 < c) (hCy : C 1 < c)
    (hb : 0 < b) (hbhalf : b < 1 / 2)
    (hE₀ : Schoenflies.Plane.mk 1 b ∈ d.piece 0)
    (hE₂ : Schoenflies.Plane.mk 1 b ∈ d.piece 2) : squareCenter ∉ d.piece 2 := by
  have hheight := h.right_arm_height_bound_of_contact e he hf hunit hc hs hsc hc₁ hCx hCy
    hb hbhalf hE₀ hE₂
  intro hcenter
  have hpre := rightArm_inverse_mem e he hcenter
  have hy := (d.piece_subset 0 hpre).2.1
  rw [hf.inverse_center hunit] at hy
  change 0 ≤ C 1 - (c + s) / 2 at hy
  linarith only [hheight, hy]

end Puzzling139335.N5
