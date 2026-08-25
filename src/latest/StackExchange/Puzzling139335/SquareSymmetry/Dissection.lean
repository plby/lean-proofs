import StackExchange.Puzzling139335.SquareSymmetry.CornerRigidity
import StackExchange.Puzzling139335.SquareSymmetry.SideRigidity
import StackExchange.Puzzling139335.DissectionTopology

/-!
# Corner and side rigidity for actual dissection pieces

The topological neighborhood premise is discharged by uniqueness of the
piece at a square corner. No local straightness of a Jordan boundary is
assumed.
-/

open Set

namespace Puzzling139335.SquareDissection

open SquareSymmetry

theorem unique_corner_congruence_preserves_square (d : SquareDissection)
    (i k a b : Fin 4) (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (he : e '' d.piece i = d.piece k) (hab : e (corner a) = corner b)
    (hunique : ∀ j, j ≠ i → corner a ∉ d.piece j) :
    e '' unitSquare = unitSquare := by
  obtain ⟨ε, hε, hsub⟩ := d.unique_piece_relative_neighborhood i hunique
  apply preserves_square_of_corner_neighborhood e a b hab hε
  intro p hp
  apply d.piece_subset k
  rw [← he]
  exact Set.image_mono hsub hp

theorem unique_corner_congruence_fixes_center (d : SquareDissection)
    (i k a b : Fin 4) (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (he : e '' d.piece i = d.piece k) (hab : e (corner a) = corner b)
    (hunique : ∀ j, j ≠ i → corner a ∉ d.piece j) :
    e squareCenter = squareCenter :=
  center_fixed_of_preserves_square e
    (d.unique_corner_congruence_preserves_square i k a b e he hab hunique)

/-- Distinct copies sharing an intrinsic unsplit corner cannot contain
the protected center in either of their interiors. -/
theorem center_not_mem_unique_corner_pair (d : SquareDissection)
    {i k : Fin 4} (hik : i ≠ k) (a b : Fin 4) (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (he : e '' d.piece i = d.piece k) (hab : e (corner a) = corner b)
    (hunique : ∀ j, j ≠ i → corner a ∉ d.piece j) :
    squareCenter ∉ interior (d.piece i) ∧ squareCenter ∉ interior (d.piece k) :=
  d.center_not_mem_fixed_pair hik e he
    (d.unique_corner_congruence_fixes_center i k a b e he hab hunique)

/-- Matching the two endpoints of square sides also forces a congruence
between actual pieces to preserve the square. -/
theorem side_congruence_preserves_square (d : SquareDissection)
    (i k a b : Fin 4) (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (he : e '' d.piece i = d.piece k)
    (hends : e '' {corner a, corner (a + 1)} = {corner b, corner (b + 1)}) :
    e '' unitSquare = unitSquare := by
  apply side_rigidity_unordered e a b hends (d.piece_subset i)
  · rw [he]
    exact d.piece_subset k
  · exact (d.jordan i).interior_nonempty

theorem center_not_mem_side_pair (d : SquareDissection)
    {i k : Fin 4} (hik : i ≠ k) (a b : Fin 4) (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (he : e '' d.piece i = d.piece k)
    (hends : e '' {corner a, corner (a + 1)} = {corner b, corner (b + 1)}) :
    squareCenter ∉ interior (d.piece i) ∧ squareCenter ∉ interior (d.piece k) :=
  d.center_not_mem_fixed_pair hik e he
    (center_fixed_of_preserves_square e
      (d.side_congruence_preserves_square i k a b e he hends))

/-- If every actual placement of one prototype can be chosen to preserve
the square, then the center cannot lie in a piece's interior. -/
theorem not_protectedCenter_of_square_placements (d : SquareDissection)
    (hplacements : ∀ i : Fin 4, ∃ e : Plane ≃ᵃⁱ[ℝ] Plane,
      e '' d.piece 0 = d.piece i ∧ e '' unitSquare = unitSquare) :
    ¬ d.HasProtectedCenter := by
  rintro ⟨k, hk⟩
  obtain ⟨e, he, heSquare⟩ := hplacements k
  have heFix := center_fixed_of_preserves_square e heSquare
  have hzero : squareCenter ∈ interior (d.piece 0) := by
    apply (mem_interior_image_affineIsometry e).mp
    rw [he, heFix]
    exact hk
  obtain ⟨f, hf, hfSquare⟩ := hplacements 1
  have hfFix := center_fixed_of_preserves_square f hfSquare
  have hone : squareCenter ∈ interior (d.piece 1) := by
    have hm := (mem_interior_image_affineIsometry f).mpr hzero
    rwa [hf, hfFix] at hm
  exact Set.disjoint_left.mp
    (d.disjoint_interiors (by decide : (0 : Fin 4) ≠ 1)) hzero hone

end Puzzling139335.SquareDissection
