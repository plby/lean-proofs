import StackExchange.Puzzling139335.N5.AlignedFace.Placement
import StackExchange.Puzzling139335.N5.AlignedFace.Translation
import StackExchange.Puzzling139335.N5.AlignedFace.Reflection
import StackExchange.Puzzling139335.N5.RightArm.Inverse
import StackExchange.Puzzling139335.N5.Remainder.Symmetry

/-!
# The incoming-aligned top face is impossible

The hypotheses describe actual placements and their actual top contacts.
The aligned top row forces equal contact lengths and determines the
fourth piece as either a strict horizontal translate of the singleton
piece or its vertical reflection.  Diagonal invariance of their actual
union contradicts both possibilities.

The source arm needed in the reflected case is not an extra support
certificate: its endpoint is the inverse image of the actual right-side
contact `(1,b)`.
-/

open Set

namespace Puzzling139335.N5

open PlaneIsometries

/-- Complete obstruction for an actual fourth placement whose top-side
normal is the incoming singleton-corner normal.  Only the displayed actual
contacts and placements are inputs; their contact lengths are derived. -/
theorem Normalized.incoming_aligned_face_impossible
    {d : SquareDissection} (h : Normalized d)
    (eR eD : Plane ≃ᵃⁱ[ℝ] Plane)
    (heR : eR '' d.piece 0 = d.piece 2)
    (heD : eD '' d.piece 0 = d.piece 3)
    {C : Plane} {c s b m : ℝ}
    (hunit : c ^ 2 + s ^ 2 = 1) (hc : 0 < c) (hs : 0 < s)
    (hbm : b < m) (hm1 : m < 1)
    (hz : 0 < c * C 1 - s * C 0)
    (hRform : ∀ p, eR p =
      !₂[1 + s * C 0 - c * C 1 - s * p 0 + c * p 1,
         1 - c * C 0 - s * C 1 + c * p 0 + s * p 1])
    (hD10 : linearMatrix eD 1 0 = c) (hD11 : linearMatrix eD 1 1 = s)
    (hRtop : ∀ x : ℝ,
      Schoenflies.Plane.mk x 1 ∈ d.piece 2 ↔ m ≤ x ∧ x ≤ 1)
    (hDtop : ∀ x : ℝ,
      Schoenflies.Plane.mk x 1 ∈ d.piece 3 ↔ b ≤ x ∧ x ≤ m)
    (hRb : Schoenflies.Plane.mk 1 b ∈ d.piece 2) : False := by
  have hRfit : eR '' d.piece 0 ⊆ unitSquare := by
    rw [heR]
    exact d.piece_subset 2
  have hDfit : eD '' d.piece 0 ⊆ unitSquare := by
    rw [heD]
    exact d.piece_subset 3
  have hRtop' : ∀ x : ℝ,
      Schoenflies.Plane.mk x 1 ∈ eR '' d.piece 0 ↔ m ≤ x ∧ x ≤ 1 := by
    rw [heR]
    exact hRtop
  have hDtop' : ∀ x : ℝ,
      Schoenflies.Plane.mk x 1 ∈ eD '' d.piece 0 ↔ b ≤ x ∧ x ≤ m := by
    rw [heD]
    exact hDtop
  have hstable : ∀ p ∈ eR '' d.piece 0 ∪ eD '' d.piece 0,
      ReflectionSeparation.diagonal p ∈ eR '' d.piece 0 ∪ eD '' d.piece 0 := by
    intro p hp
    rw [heR, heD] at hp ⊢
    have hmem := mem_image_of_mem ReflectionSeparation.diagonal hp
    rwa [h.remainder_diagonal_image] at hmem
  obtain ⟨_, htranslation | hreflection⟩ :=
    AlignedFace.placement_of_top_intervals eR eD hRform hD10 hD11
      hRfit hDfit hbm hm1 hRtop' hDtop'
  · exact AlignedFace.translation_impossible eR eD
      (d.piece_subset 0) h.bottom_left h.bottom_right hc hs (sub_pos.mpr hm1)
      hRform htranslation hstable
  · have hpre : eR.symm (Schoenflies.Plane.mk 1 b) ∈ d.piece 0 := by
      have hRb' : Schoenflies.Plane.mk 1 b ∈ eR '' d.piece 0 := by
        rwa [heR]
      obtain ⟨p, hp, hpeq⟩ := hRb'
      rw [← hpeq, eR.symm_apply_apply]
      exact hp
    rw [swapped_inverse_right_point hunit hRform] at hpre
    have hRy (p : Plane) :
        eR p 1 = 1 - (c * C 0 + s * C 1) + c * p 0 + s * p 1 := by
      rw [hRform p]
      change 1 - c * C 0 - s * C 1 + c * p 0 + s * p 1 =
        1 - (c * C 0 + s * C 1) + c * p 0 + s * p 1
      ring
    have hTR : Schoenflies.Plane.mk 1 1 ∈ eR '' d.piece 0 ∪ eD '' d.piece 0 :=
      Or.inl ((hRtop' 1).mpr ⟨hm1.le, le_rfl⟩)
    exact AlignedFace.reflection_impossible
      (d.piece_subset 0) h.bottom_left (union_subset hRfit hDfit) hTR
      hRy hreflection hstable hunit hc hs hz hpre

end Puzzling139335.N5
