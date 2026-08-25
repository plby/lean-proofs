import StackExchange.Puzzling139335.GeometricReduction

/-!
# An actual repeated square-corner placement

Four corner-owning pieces and the proved bound of three used intrinsic
types force two actual placements to use the same intrinsic corner. With
four incidences every corner is uniquely owned, so the relative congruence
preserves the whole square.
-/

open Set

namespace Puzzling139335.N4Dispatch.OneCorner

theorem each_tile_one_of_labeled_corners (d : SquareDissection)
    (hcorners : ∀ j i : Fin 4, corner j ∈ d.piece i ↔ j = i) :
    ∀ i, d.tileCornerCount i = 1 := by
  classical
  intro i
  change (Finset.univ.filter fun j => corner j ∈ d.piece i).card = 1
  simp only [hcorners]
  simp [Finset.filter_eq']

theorem exists_repeated_type (d : SquareDissection) (hc : d.HasProtectedCenter)
    (hOwners : ∀ j : Fin 4, corner j ∈ d.piece j) :
    ∃ i j : Fin 4, i ≠ j ∧ d.intrinsicCorner i i = d.intrinsicCorner j j := by
  classical
  let f : Fin 4 → Plane := fun j => d.intrinsicCorner j j
  have hsub : Finset.univ.image f ⊆ d.usedCornerTypes := by
    intro p hp
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hp
    exact d.mem_usedCornerTypes.mpr ⟨j, j, hOwners j, rfl⟩
  have hnot : ¬ Function.Injective f := by
    intro hinj
    have hcard : (Finset.univ.image f).card = 4 := by
      rw [Finset.card_image_of_injective _ hinj]
      simp
    have hle := (Finset.card_le_card hsub).trans (d.usedCornerTypes_card_le_three hc)
    omega
  obtain ⟨i, j, heq, hne⟩ := Function.not_injective_iff.mp hnot
  exact ⟨i, j, hne, heq⟩

theorem exists_square_corner_pair (d : SquareDissection) (hc : d.HasProtectedCenter)
    (hN : d.cornerIncidenceCount = 4)
    (hOwners : ∀ j : Fin 4, corner j ∈ d.piece j) :
    ∃ i j : Fin 4, i ≠ j ∧ ∃ e : Plane ≃ᵃⁱ[ℝ] Plane,
      e '' d.piece i = d.piece j ∧ e (corner i) = corner j ∧
        e '' unitSquare = unitSquare := by
  obtain ⟨i, j, hij, htype⟩ := exists_repeated_type d hc hOwners
  exact ⟨i, j, hij, d.relativePlacement i j, d.relativePlacement_image i j,
    d.relativePlacement_corner htype,
    d.relativePlacement_preserves_square_of_unique_corner
      (d.unique_corner_owner_of_four_incidences hN (hOwners i)) htype⟩

end Puzzling139335.N4Dispatch.OneCorner
