import StackExchange.Puzzling139335.RepeatedCorners
import StackExchange.Puzzling139335.InitialReduction

/-!
# Consequences of exactly four square-corner incidences

Every corner is uniquely owned. A type appearing at a corner of the center
piece cannot occur in any other placement. These facts are derived from
the dissection rather than imposed on its definition.
-/

open Set

namespace Puzzling139335.SquareDissection

theorem cornerTileCount_eq_one_of_four_incidences (d : SquareDissection)
    (hN : d.cornerIncidenceCount = 4) (j : Fin 4) : d.cornerTileCount j = 1 := by
  have hsum : (∑ j, d.cornerTileCount j) = 4 :=
    d.cornerIncidenceCount_eq_sum_cornerTileCount.symm.trans hN
  rw [CornerCounting.sum_fin_four] at hsum
  have h0 := d.cornerTileCount_pos 0
  have h1 := d.cornerTileCount_pos 1
  have h2 := d.cornerTileCount_pos 2
  have h3 := d.cornerTileCount_pos 3
  have heq : d.cornerTileCount 0 = 1 ∧ d.cornerTileCount 1 = 1 ∧
      d.cornerTileCount 2 = 1 ∧ d.cornerTileCount 3 = 1 := by omega
  fin_cases j
  · exact heq.1
  · exact heq.2.1
  · exact heq.2.2.1
  · exact heq.2.2.2

theorem unique_corner_owner_of_four_incidences (d : SquareDissection)
    (hN : d.cornerIncidenceCount = 4) {i j : Fin 4} (hi : corner j ∈ d.piece i) :
    ∀ k, k ≠ i → corner j ∉ d.piece k := by
  classical
  have hcard := d.cornerTileCount_eq_one_of_four_incidences hN j
  change (Finset.univ.filter fun k => corner j ∈ d.piece k).card = 1 at hcard
  intro k hki hk
  apply hki
  exact Finset.card_le_one_iff.mp hcard.le (by simp [hk]) (by simp [hi])

/-- A corner type used by the center piece occurs in no other tile. -/
theorem center_owner_type_unique_of_four_incidences (d : SquareDissection)
    (hN : d.cornerIncidenceCount = 4) {i j : Fin 4}
    (hc : squareCenter ∈ interior (d.piece i)) (hj : corner j ∈ d.piece i)
    {k l : Fin 4} (htype : d.intrinsicCorner i j = d.intrinsicCorner k l) : k = i := by
  by_contra hki
  exact (d.center_not_mem_of_repeated_unique_corner (Ne.symm hki)
    (d.unique_corner_owner_of_four_incidences hN hj) htype).1 hc

theorem tileCornerCount_eq_of_four_incidences_repeated_type (d : SquareDissection)
    (hN : d.cornerIncidenceCount = 4) {i j k l : Fin 4}
    (hj : corner j ∈ d.piece i)
    (htype : d.intrinsicCorner i j = d.intrinsicCorner k l) :
    d.tileCornerCount i = d.tileCornerCount k :=
  d.tileCornerCount_eq_of_repeated_unique_corner
    (d.unique_corner_owner_of_four_incidences hN hj) htype

/-- With eight incidences in a putative counterexample, every tile has two
square corners. This is the other extremal incidence count. -/
theorem tileCornerCount_eq_two_of_eight_incidences (d : SquareDissection)
    (hc : d.HasProtectedCenter) (hN : d.cornerIncidenceCount = 8) (i : Fin 4) :
    d.tileCornerCount i = 2 := by
  have hsum : (∑ j, d.tileCornerCount j) = 8 :=
    d.cornerIncidenceCount_eq_sum_tileCornerCount.symm.trans hN
  rw [CornerCounting.sum_fin_four] at hsum
  have h0 := d.tileCornerCount_le_two hc 0
  have h1 := d.tileCornerCount_le_two hc 1
  have h2 := d.tileCornerCount_le_two hc 2
  have h3 := d.tileCornerCount_le_two hc 3
  have heq : d.tileCornerCount 0 = 2 ∧ d.tileCornerCount 1 = 2 ∧
      d.tileCornerCount 2 = 2 ∧ d.tileCornerCount 3 = 2 := by omega
  fin_cases i
  · exact heq.1
  · exact heq.2.1
  · exact heq.2.2.1
  · exact heq.2.2.2

end Puzzling139335.SquareDissection
