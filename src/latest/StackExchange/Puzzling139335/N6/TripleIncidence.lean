import StackExchange.Puzzling139335.N6.TripleTypes
import StackExchange.Puzzling139335.N6.AcuteIncidence

/-!
# The fourth piece in the triple-corner branch

Once the common intrinsic corner is confined to an acute supporting cone,
the tile at the opposite square corner must be a singleton. It is exactly
the one tile missing the triple corner. This is an actual membership
reduction; the supporting cone is proved separately from the corner germs.
-/

open Set

namespace Puzzling139335.N6

/-- There is exactly one piece absent from a corner of multiplicity three. -/
theorem nonowners_eq_of_triple (d : SquareDissection) {s i j : Fin 4}
    (hs : d.cornerTileCount s = 3)
    (hi : corner s ∉ d.piece i) (hj : corner s ∉ d.piece j) : i = j := by
  classical
  have hsum := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin 4))) (fun k => corner s ∈ d.piece k)
  have howners : (Finset.univ.filter fun k => corner s ∈ d.piece k).card = 3 := hs
  have hnonowners : (Finset.univ.filter fun k => corner s ∉ d.piece k).card ≤ 1 := by
    simp only [Finset.card_univ, Fintype.card_fin] at hsum
    omega
  exact Finset.card_le_one_iff.mp hnonowners (by simp [hi]) (by simp [hj])

/-- The unique piece missing the triple corner owns the opposite corner. -/
theorem opposite_mem_of_triple_not_mem (d : SquareDissection)
    (hc : d.HasProtectedCenter) {s i : Fin 4} (hs : d.cornerTileCount s = 3)
    (hi : corner s ∉ d.piece i) : corner (s + 2) ∈ d.piece i := by
  obtain ⟨j, hj⟩ := d.exists_piece_mem (corner_mem_unitSquare (s + 2))
  have hjs : corner s ∉ d.piece j := fun h => d.no_opposite_corners hc j s ⟨h, hj⟩
  exact nonowners_eq_of_triple d hs hjs hi ▸ hj

/-- Every occurrence of a forty-five-degree support type lies at the
triple corner, because all other square corners have full neighborhoods. -/
theorem supports45_occurrence_at_triple (d : SquareDissection)
    (hN : d.cornerIncidenceCount = 6) {s i j : Fin 4} (hs : d.cornerTileCount s = 3)
    {v : Plane} (hsupport : AcuteCorner.Supports45 (d.piece 0) v)
    (hj : corner j ∈ d.piece i) (htype : d.intrinsicCorner i j = v) : j = s := by
  by_contra hjs
  have hfull : v ∈ N5.fullCornerTypes d :=
    (N5.mem_fullCornerTypes d).mpr
      ⟨i, j, hj, unique_away_from_triple d hN hs hjs, htype⟩
  exact supports45_not_mem_fullCornerTypes d hsupport hfull

/-- Every two-corner piece contains the triple corner. -/
theorem triple_mem_of_two_corners (d : SquareDissection)
    (hc : d.HasProtectedCenter) (hN : d.cornerIncidenceCount = 6)
    {s : Fin 4} (hs : d.cornerTileCount s = 3) (i : Fin 4)
    (hcount : d.tileCornerCount i = 2) {v : Plane}
    (hv : v ∈ d.piece 0) (hsupport : AcuteCorner.Supports45 (d.piece 0) v) :
    corner s ∈ d.piece i := by
  obtain ⟨j, hj, htype⟩ := supports45_occurs_in_two_corner_tile d hc i hcount hv hsupport
  exact supports45_occurrence_at_triple d hN hs hsupport hj htype ▸ hj

/-- The piece absent from the triple corner has exactly one square corner. -/
theorem nonowner_has_one_corner (d : SquareDissection)
    (hc : d.HasProtectedCenter) (hN : d.cornerIncidenceCount = 6)
    {s i : Fin 4} (hs : d.cornerTileCount s = 3) (hi : corner s ∉ d.piece i)
    {v : Plane} (hv : v ∈ d.piece 0)
    (hsupport : AcuteCorner.Supports45 (d.piece 0) v) : d.tileCornerCount i = 1 := by
  classical
  have hle := d.tileCornerCount_le_two hc i
  have hne : d.tileCornerCount i ≠ 2 :=
    fun htwo => hi (triple_mem_of_two_corners d hc hN hs i htwo hv hsupport)
  have hop := opposite_mem_of_triple_not_mem d hc hs hi
  have hpos : 0 < d.tileCornerCount i := by
    change 0 < (Finset.univ.filter fun j => corner j ∈ d.piece i).card
    exact Finset.card_pos.mpr ⟨s + 2, by simp [hop]⟩
  omega

/-- The fourth piece owns only the opposite square corner. -/
theorem nonowner_corner_iff (d : SquareDissection)
    (hc : d.HasProtectedCenter) (hN : d.cornerIncidenceCount = 6)
    {s i : Fin 4} (hs : d.cornerTileCount s = 3) (hi : corner s ∉ d.piece i)
    {v : Plane} (hv : v ∈ d.piece 0)
    (hsupport : AcuteCorner.Supports45 (d.piece 0) v) (j : Fin 4) :
    corner j ∈ d.piece i ↔ j = s + 2 := by
  classical
  have hcount := nonowner_has_one_corner d hc hN hs hi hv hsupport
  change (Finset.univ.filter fun j => corner j ∈ d.piece i).card = 1 at hcount
  have hop := opposite_mem_of_triple_not_mem d hc hs hi
  constructor
  · intro hj
    exact Finset.card_le_one_iff.mp hcount.le (by simp [hj]) (by simp [hop])
  · rintro rfl
    exact hop

/-- All corners other than the opposite one are owned by a member of the
triple-corner group. -/
theorem triple_mem_of_nonopposite_corner (d : SquareDissection)
    (hc : d.HasProtectedCenter) (hN : d.cornerIncidenceCount = 6)
    {s i j : Fin 4} (hs : d.cornerTileCount s = 3)
    {v : Plane} (hv : v ∈ d.piece 0)
    (hsupport : AcuteCorner.Supports45 (d.piece 0) v)
    (hj : corner j ∈ d.piece i) (hjne : j ≠ s + 2) : corner s ∈ d.piece i := by
  by_contra hi
  exact hjne ((nonowner_corner_iff d hc hN hs hi hv hsupport j).mp hj)

end Puzzling139335.N6
