import StackExchange.Puzzling139335.IntrinsicCorners
import StackExchange.Puzzling139335.SquareSymmetry
import StackExchange.Puzzling139335.CornerSupport.Equality

/-!
# Repetition of actual intrinsic corner types

A unique square-corner owner supplies the actual quadrant germ needed by
the rigidity theorem. If another chosen placement uses that same intrinsic
point, its relative map preserves the square, and the two pieces have the
same number of square corners. Neither can own a center neighborhood.
-/

open Set

namespace Puzzling139335.SquareDissection

theorem relativePlacement_preserves_square_of_unique_corner (d : SquareDissection)
    {i j k l : Fin 4}
    (hunique : ∀ m, m ≠ i → corner j ∉ d.piece m)
    (htype : d.intrinsicCorner i j = d.intrinsicCorner k l) :
    d.relativePlacement i k '' unitSquare = unitSquare :=
  d.unique_corner_congruence_preserves_square i k j l (d.relativePlacement i k)
    (d.relativePlacement_image i k) (d.relativePlacement_corner htype) hunique

theorem center_not_mem_of_repeated_unique_corner (d : SquareDissection)
    {i j k l : Fin 4} (hik : i ≠ k)
    (hunique : ∀ m, m ≠ i → corner j ∉ d.piece m)
    (htype : d.intrinsicCorner i j = d.intrinsicCorner k l) :
    squareCenter ∉ interior (d.piece i) ∧ squareCenter ∉ interior (d.piece k) :=
  d.center_not_mem_unique_corner_pair hik j l (d.relativePlacement i k)
    (d.relativePlacement_image i k) (d.relativePlacement_corner htype) hunique

/-- An actual square symmetry between pieces preserves their corner counts. -/
theorem tileCornerCount_eq_of_square_congruence (d : SquareDissection)
    (i k : Fin 4) (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (he : e '' d.piece i = d.piece k) (hS : e '' unitSquare = unitSquare) :
    d.tileCornerCount i = d.tileCornerCount k := by
  classical
  let σ := SquareSymmetry.cornerPermutation e hS.subset
  have hσ (a : Fin 4) : e (corner a) = corner (σ a) :=
    SquareSymmetry.cornerPermutation_apply e hS.subset a
  have hmem (a : Fin 4) : corner a ∈ d.piece i ↔ corner (σ a) ∈ d.piece k := by
    rw [← hσ, ← he]
    constructor
    · exact mem_image_of_mem e
    · rintro ⟨p, hp, hpa⟩
      exact e.injective hpa ▸ hp
  change (Finset.univ.filter fun a => corner a ∈ d.piece i).card =
    (Finset.univ.filter fun a => corner a ∈ d.piece k).card
  apply Finset.card_bij (fun a _ => σ a)
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    exact (hmem a).mp ha
  · intro a _ b _ hab
    exact σ.injective hab
  · intro b hb
    refine ⟨σ.symm b, ?_, σ.apply_symm_apply b⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
    exact (hmem (σ.symm b)).mpr (by simpa using hb)

theorem tileCornerCount_eq_of_repeated_unique_corner (d : SquareDissection)
    {i j k l : Fin 4}
    (hunique : ∀ m, m ≠ i → corner j ∉ d.piece m)
    (htype : d.intrinsicCorner i j = d.intrinsicCorner k l) :
    d.tileCornerCount i = d.tileCornerCount k :=
  d.tileCornerCount_eq_of_square_congruence i k (d.relativePlacement i k)
    (d.relativePlacement_image i k)
    (d.relativePlacement_preserves_square_of_unique_corner hunique htype)

/-- Equality in the intrinsic-corner bound is a genuine rectangular hull. -/
theorem hasRectangularHull_of_four_usedCornerTypes (d : SquareDissection)
    (hfour : d.usedCornerTypes.card = 4) :
    HasRectangularHull (d.piece 0) :=
  CornerSupport.Equality.hasRectangularHull_of_card_four d.usedCornerTypes hfour
    (fun _ hv => d.isSupportCorner_of_mem_usedCornerTypes hv)

theorem usedCornerTypes_card_le_three_of_not_rectangular (d : SquareDissection)
    (hnot : ¬ HasRectangularHull (d.piece 0)) :
    d.usedCornerTypes.card ≤ 3 := by
  have hle := d.usedCornerTypes_card_le_four
  have hne : d.usedCornerTypes.card ≠ 4 :=
    fun h => hnot (d.hasRectangularHull_of_four_usedCornerTypes h)
  omega

end Puzzling139335.SquareDissection
