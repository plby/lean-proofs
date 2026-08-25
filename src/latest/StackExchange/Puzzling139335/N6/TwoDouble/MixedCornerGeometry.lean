import StackExchange.Puzzling139335.N6.TwoDouble.MixedCornerGeometry.ActualSamples
import StackExchange.Puzzling139335.N6.TwoDouble.MixedCornerGeometry.SampleIsometry
import StackExchange.Puzzling139335.N6.TwoDouble.MixedPlacement

/-!
# The actual normalized mixed-singleton branch is impossible

The two outer pieces own the horizontal corner pairs and are horizontal
reflections. The remaining pieces contain the bottom-right and top-right
corners, and an actual congruence matches these two corner occurrences.

Six incidences, weighted half-square mass, and the Jordan axis-contact
theorem supply an actual right-side point of each remaining piece. These
two points classify the relative isometry directly: it fixes the square
center, or it is the explicit strict mixed rotation. Both alternatives are
impossible. In particular, no local sector, straight-germ, intrinsic-type
bound, or source-preimage distinctness is assumed.
-/

open Set

namespace Puzzling139335.N6.TwoDouble.MixedCornerGeometry

noncomputable section

open ReflectionSeparation

/-- The actual right-side samples force the relative isometry to fix the
center or have the explicit mixed rotation form with strictly positive
parameters. -/
theorem normalized_relative_map (d : SquareDissection)
    (hc : d.HasProtectedCenter) (hN : d.cornerIncidenceCount = 6)
    (hBL : corner 0 ∈ d.piece 0) (hBR : corner 1 ∈ d.piece 0)
    (hreflect : horizontal '' d.piece 0 = d.piece 1)
    (hH : corner 1 ∈ d.piece 2) (hG : corner 2 ∈ d.piece 3)
    (g : Plane ≃ᵃⁱ[ℝ] Plane) (hg : g '' d.piece 2 = d.piece 3)
    (hgBR : g (corner 1) = corner 2) :
    g squareCenter = squareCenter ∨
      ∃ s c : ℝ, 0 < s ∧ 0 < c ∧ s ^ 2 + c ^ 2 = 1 ∧
        (∀ p, g p = MixedScalar.rotation s c p) ∧
        d.piece 3 = MixedScalar.rotation s c '' d.piece 2 := by
  obtain ⟨⟨t, ht, hsample⟩, u, hu, htarget⟩ :=
    normalized_right_side_samples d hc hN hBL hBR hreflect hH hG
  exact SampleIsometry.classification_of_side_samples_image
    (d.piece_subset 2) (d.piece_subset 3) (d.jordan 2).interior_nonempty
    g hg hgBR ht hu hsample htarget

/-- The normalized mixed corner pair is excluded using only actual
dissection data and a corner-matching congruence between its two middle
pieces. -/
theorem no_normalized_mixed_pair (d : SquareDissection)
    (hc : d.HasProtectedCenter) (hN : d.cornerIncidenceCount = 6)
    (hBL : corner 0 ∈ d.piece 0) (hBR : corner 1 ∈ d.piece 0)
    (hreflect : horizontal '' d.piece 0 = d.piece 1)
    (hH : corner 1 ∈ d.piece 2) (hG : corner 2 ∈ d.piece 3)
    (g : Plane ≃ᵃⁱ[ℝ] Plane) (hg : g '' d.piece 2 = d.piece 3)
    (hgBR : g (corner 1) = corner 2) : False := by
  rcases normalized_relative_map d hc hN hBL hBR hreflect hH hG g hg hgBR with
    hfix | ⟨s, c, hs, hcos, hcircle, _, himage⟩
  · have hnot := d.center_not_mem_fixed_pair (by decide : (2 : Fin 4) ≠ 3) g hg hfix
    exact (center_mem_mixed_pair d hc hreflect).elim hnot.1 hnot.2
  · obtain ⟨e, he⟩ := d.congruent 0 2
    have hpre := source_corner_preimage_data d hc hN hBR hreflect hH hG g hg hgBR e he
    exact mixed_rotation_placement_impossible d hs hcos hcircle hBL hBR hreflect
      himage.symm hpre.1 hpre.2.1 e he hpre.2.2

/-- Equality of the two intrinsic singleton types supplies the actual
corner-matching congruence, so no relative-map certificate is needed. -/
theorem no_normalized_mixed_same_intrinsic (d : SquareDissection)
    (hc : d.HasProtectedCenter) (hN : d.cornerIncidenceCount = 6)
    (hBL : corner 0 ∈ d.piece 0) (hBR : corner 1 ∈ d.piece 0)
    (hreflect : horizontal '' d.piece 0 = d.piece 1)
    (hH : corner 1 ∈ d.piece 2) (hG : corner 2 ∈ d.piece 3)
    (htype : d.intrinsicCorner 2 1 = d.intrinsicCorner 3 2) : False :=
  no_normalized_mixed_pair d hc hN hBL hBR hreflect hH hG
    (d.relativePlacement 2 3) (d.relativePlacement_image 2 3)
    (d.relativePlacement_corner htype)

end

end Puzzling139335.N6.TwoDouble.MixedCornerGeometry
