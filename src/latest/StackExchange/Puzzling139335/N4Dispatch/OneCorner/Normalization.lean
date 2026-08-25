import StackExchange.Puzzling139335.N4Dispatch.OneCorner.Normalization.Transport
import StackExchange.Puzzling139335.N4Dispatch.OneCorner.Normalization.CornerPair

/-!
# Normalization of an actual pair in the one-corner case

Starting with pieces labeled by their unique square corners and an actual
square-preserving congruence between two distinct pieces, a common change
of coordinates puts the source corner at `0` and the target at `1` or `2`.
All dissection properties, actual pair images, and corner labels survive.
-/

open Set

namespace Puzzling139335.N4Dispatch.OneCorner.Normalization

open DoublePair.Normalize

/-- An actual pair can be placed in one of the two canonical corner positions.
The last clause records explicitly that a normalized central half-turn was
already a central half-turn before the coordinate change. -/
theorem exists_normalized_pair (d : SquareDissection)
    (hc : d.HasProtectedCenter)
    (hcorners : ∀ j i, corner j ∈ d.piece i ↔ j = i)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (heS : e '' unitSquare = unitSquare)
    {a b : Fin 4} (hab : a ≠ b) (he : e '' d.piece a = d.piece b) :
    ∃ (D : SquareDissection) (e' : Plane ≃ᵃⁱ[ℝ] Plane) (k : Fin 4),
      D.HasProtectedCenter ∧
      (∀ j i, corner j ∈ D.piece i ↔ j = i) ∧
      (k = 1 ∨ k = 2) ∧
      e' '' D.piece 0 = D.piece k ∧
      e' (corner 0) = corner k ∧
      e' '' unitSquare = unitSquare ∧
      (e' = AffineIsometryEquiv.pointReflection ℝ squareCenter →
        e = AffineIsometryEquiv.pointReflection ℝ squareCenter) := by
  obtain ⟨g, k, hgS, hga, hgb, hk⟩ := exists_pair_normalizing_isometry a b hab
  have heab := pair_maps_owned_corner d hcorners e heS he
  let D := reoriented d g hgS
  refine ⟨D, conjugate g e, k, (reoriented_hasProtectedCenter d g hgS).mpr hc,
    reoriented_corners d hcorners g hgS, hk, ?_, ?_,
    conjugate_preserves_square g e hgS heS,
    (conjugate_eq_center_reflection_iff g e hgS).mp⟩
  · change conjugate g e '' (reoriented d g hgS).piece 0 =
      (reoriented d g hgS).piece k
    rw [reoriented_piece_of_corner_image d g hgS hga,
      reoriented_piece_of_corner_image d g hgS hgb, conjugate_image_image, he]
  · have hg0 : g.symm (corner 0) = corner a := by
      rw [← hga, g.symm_apply_apply]
    rw [conjugate_apply, hg0, heab, hgb]

/-- Version of the pair normalization with the central half-turn excluded. -/
theorem exists_normalized_pair_of_not_halfturn (d : SquareDissection)
    (hc : d.HasProtectedCenter)
    (hcorners : ∀ j i, corner j ∈ d.piece i ↔ j = i)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (heS : e '' unitSquare = unitSquare)
    {a b : Fin 4} (hab : a ≠ b) (he : e '' d.piece a = d.piece b)
    (henot : e ≠ AffineIsometryEquiv.pointReflection ℝ squareCenter) :
    ∃ (D : SquareDissection) (e' : Plane ≃ᵃⁱ[ℝ] Plane) (k : Fin 4),
      D.HasProtectedCenter ∧
      (∀ j i, corner j ∈ D.piece i ↔ j = i) ∧
      (k = 1 ∨ k = 2) ∧
      e' '' D.piece 0 = D.piece k ∧
      e' (corner 0) = corner k ∧
      e' '' unitSquare = unitSquare ∧
      e' ≠ AffineIsometryEquiv.pointReflection ℝ squareCenter := by
  obtain ⟨D, e', k, hD, hcornersD, hk, hpair, hcorner, heS', hhalf⟩ :=
    exists_normalized_pair d hc hcorners e heS hab he
  exact ⟨D, e', k, hD, hcornersD, hk, hpair, hcorner, heS',
    fun h => henot (hhalf h)⟩

end Puzzling139335.N4Dispatch.OneCorner.Normalization
