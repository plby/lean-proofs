import StackExchange.Puzzling139335.N7.Incidence

/-!
# Unsplit corners in the seven-incidence case

Every two-corner piece meets each pair of opposite square corners: otherwise
its two corners would be the other opposite pair.  Thus two opposite corners
cannot both have unique owners when there are three two-corner pieces.
-/

open Set

namespace Puzzling139335

private theorem opposite_of_avoids_opposite_pair {a b c : Fin 4}
    (hba : b ≠ a) (hba₂ : b ≠ a + 2)
    (hca : c ≠ a) (hca₂ : c ≠ a + 2) (hbc : b ≠ c) : c = b + 2 := by
  have hbval : b.val ≠ a.val := fun h => hba (Fin.ext h)
  have hbval₂ : b.val ≠ (a.val + 2) % 4 := fun h => hba₂ (Fin.ext h)
  have hcval : c.val ≠ a.val := fun h => hca (Fin.ext h)
  have hcval₂ : c.val ≠ (a.val + 2) % 4 := fun h => hca₂ (Fin.ext h)
  have hbcval : b.val ≠ c.val := fun h => hbc (Fin.ext h)
  have ha4 := a.isLt
  have hb4 := b.isLt
  have hc4 := c.isLt
  apply Fin.ext
  change c.val = (b.val + 2) % 4
  omega

namespace SquareDissection

/-- A two-corner piece in a putative counterexample meets every opposite pair
of square corners.  This uses actual corner membership and the diameter
obstruction, not a convex-hull replacement. -/
theorem two_corner_tile_meets_opposite_pair (d : SquareDissection)
    (hc : d.HasProtectedCenter) (i : Fin 4) (hcount : d.tileCornerCount i = 2)
    (a : Fin 4) : corner a ∈ d.piece i ∨ corner (a + 2) ∈ d.piece i := by
  classical
  by_contra hmeet
  obtain ⟨ha, ha₂⟩ := not_or.mp hmeet
  change (Finset.univ.filter fun j => corner j ∈ d.piece i).card = 2 at hcount
  obtain ⟨b, c, hbc, hpair⟩ := Finset.card_eq_two.mp hcount
  have hb : corner b ∈ d.piece i := by
    have hmem : b ∈ Finset.univ.filter fun j => corner j ∈ d.piece i := by
      rw [hpair]
      simp
    exact (Finset.mem_filter.mp hmem).2
  have hcmem : corner c ∈ d.piece i := by
    have hmem : c ∈ Finset.univ.filter fun j => corner j ∈ d.piece i := by
      rw [hpair]
      simp
    exact (Finset.mem_filter.mp hmem).2
  have hcb : c = b + 2 := opposite_of_avoids_opposite_pair (a := a) (b := b) (c := c)
    (fun h => ha (h ▸ hb)) (fun h => ha₂ (h ▸ hb))
    (fun h => ha (h ▸ hcmem)) (fun h => ha₂ (h ▸ hcmem)) hbc
  exact d.no_opposite_corners hc i b ⟨hb, hcb ▸ hcmem⟩

/-- If both corners of an opposite pair have unique owners, every two-corner
piece is one of those two owners. -/
theorem two_corner_tile_count_le_two_of_opposite_unique (d : SquareDissection)
    (hc : d.HasProtectedCenter) (a : Fin 4)
    (ha : d.cornerTileCount a = 1) (ha₂ : d.cornerTileCount (a + 2) = 1) :
    (Finset.univ.filter fun i => d.tileCornerCount i = 2).card ≤ 2 := by
  classical
  obtain ⟨u, _, hu⟩ := d.existsUnique_corner_owner_of_count_one a ha
  obtain ⟨v, _, hv⟩ := d.existsUnique_corner_owner_of_count_one (a + 2) ha₂
  have hsub : (Finset.univ.filter fun i => d.tileCornerCount i = 2) ⊆ {u, v} := by
    intro i hi
    have hcount : d.tileCornerCount i = 2 := (Finset.mem_filter.mp hi).2
    rcases d.two_corner_tile_meets_opposite_pair hc i hcount a with hia | hia₂
    · simp only [Finset.mem_insert, Finset.mem_singleton]
      exact Or.inl (hu i hia)
    · simp only [Finset.mem_insert, Finset.mem_singleton]
      exact Or.inr (hv i hia₂)
  calc
    _ ≤ ({u, v} : Finset (Fin 4)).card := Finset.card_le_card hsub
    _ ≤ 2 := by
      by_cases huv : u = v <;> simp [huv]

end SquareDissection

namespace N7

/-- Opposite square corners cannot both have multiplicity one when the total
incidence count is seven. -/
theorem opposite_corners_not_both_unique (d : SquareDissection)
    (hc : d.HasProtectedCenter) (hN : d.cornerIncidenceCount = 7) (a : Fin 4) :
    ¬ (d.cornerTileCount a = 1 ∧ d.cornerTileCount (a + 2) = 1) := by
  intro h
  have hle := d.two_corner_tile_count_le_two_of_opposite_unique hc a h.1 h.2
  have hthree := (tile_count_cards d hc hN).2
  omega

/-- Any two distinct corners with unique owners are adjacent. -/
theorem two_distinct_unique_corners_adjacent (d : SquareDissection)
    (hc : d.HasProtectedCenter) (hN : d.cornerIncidenceCount = 7)
    {a b : Fin 4} (ha : d.cornerTileCount a = 1) (hb : d.cornerTileCount b = 1)
    (hab : a ≠ b) : b = a + 1 ∨ b = a + 3 := by
  have hbo : b ≠ a + 2 := by
    intro h
    exact opposite_corners_not_both_unique d hc hN a ⟨ha, h ▸ hb⟩
  fin_cases a <;> fin_cases b <;> simp_all

end N7
end Puzzling139335
