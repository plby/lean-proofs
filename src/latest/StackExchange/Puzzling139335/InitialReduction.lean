import StackExchange.Puzzling139335.CornerIncidence
import StackExchange.Puzzling139335.SquareGeometry

/-!
# The first geometric reduction

Under the protected-center assumption, the diameter argument bounds the
number of corners in each piece. The resulting incidence count has only
five possibilities, and no square corner belongs to all four pieces.
-/

open Set

namespace Puzzling139335
namespace SquareDissection

theorem tileCornerCount_le_two (d : SquareDissection) (hc : d.HasProtectedCenter)
    (i : Fin 4) : d.tileCornerCount i ≤ 2 :=
  d.tileCornerCount_le_two_of_no_opposite (d.no_opposite_corners hc) i

theorem cornerIncidenceCount_bounds (d : SquareDissection) (hc : d.HasProtectedCenter) :
    4 ≤ d.cornerIncidenceCount ∧ d.cornerIncidenceCount ≤ 8 :=
  d.cornerIncidenceCount_bounds_of_no_opposite (d.no_opposite_corners hc)

theorem cornerIncidenceCount_cases (d : SquareDissection) (hc : d.HasProtectedCenter) :
    d.cornerIncidenceCount = 4 ∨ d.cornerIncidenceCount = 5 ∨
      d.cornerIncidenceCount = 6 ∨ d.cornerIncidenceCount = 7 ∨
        d.cornerIncidenceCount = 8 := by
  have h := d.cornerIncidenceCount_bounds hc
  omega

theorem not_all_contain_corner (d : SquareDissection) (hc : d.HasProtectedCenter)
    (j : Fin 4) : ¬ ∀ i, corner j ∈ d.piece i := by
  intro hall
  obtain ⟨i, hi⟩ := d.exists_piece_mem (corner_mem_unitSquare (j + 2))
  exact d.no_opposite_corners hc i j ⟨hall i, hi⟩

theorem cornerTileCount_le_three (d : SquareDissection) (hc : d.HasProtectedCenter)
    (j : Fin 4) : d.cornerTileCount j ≤ 3 := by
  classical
  obtain ⟨i, hi⟩ := not_forall.mp (d.not_all_contain_corner hc j)
  let s : Finset (Fin 4) := Finset.univ.filter fun k => corner j ∈ d.piece k
  have hsub : s ⊆ Finset.univ := Finset.subset_univ s
  have hne : s ≠ Finset.univ := by
    intro heq
    have his : i ∈ s := by rw [heq]; exact Finset.mem_univ i
    exact hi (Finset.mem_filter.mp his).2
  have hlt := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩)
  have hcard : d.cornerTileCount j = s.card := rfl
  simp only [Finset.card_univ, Fintype.card_fin] at hlt
  omega

end SquareDissection
end Puzzling139335
