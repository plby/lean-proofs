import StackExchange.Puzzling139335.DissectionTopology
import StackExchange.Puzzling139335.ThreeCorners.FullCorners

/-!
# Full intrinsic corners from actual unique corner ownership

Closedness of the other pieces supplies the full relative square
neighborhood required by the three-corner geometry.
-/

open Set

namespace Puzzling139335.SquareDissection

theorem full_corner_preimage_of_unique_owner (d : SquareDissection)
    (i k j : Fin 4) (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (he : e '' d.piece i = d.piece k)
    (hunique : ∀ l : Fin 4, l ≠ k → corner j ∉ d.piece l) :
    UnitPairs.IsFullSquareCorner (d.piece i) (e.symm (corner j)) := by
  obtain ⟨ε, hε, hnear⟩ := d.unique_piece_relative_neighborhood k hunique
  refine ⟨e, j, ε, hε, ?_, e.apply_symm_apply _, ?_⟩
  · rw [he]
    exact d.piece_subset k
  · rwa [he]

end Puzzling139335.SquareDissection
