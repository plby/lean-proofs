import StackExchange.Puzzling139335.CornerIncidence

/-!
# Corner counting for adjacent outer pieces

Suppose two pieces each have a uniquely owned corner and share a third
corner of multiplicity two. Every other piece misses all three of those
physical corners, so it contains at most the fourth corner. The argument
uses exact corner memberships and does not require any geometric shape
or adjacency hypothesis.
-/

open Set

namespace Puzzling139335.N6.TwoDouble

/-- Two known distinct owners exhaust a corner of multiplicity two. -/
theorem other_not_mem_of_two_owners (d : SquareDissection) {i j k c : Fin 4}
    (hij : i ≠ j) (hci : corner c ∈ d.piece i) (hcj : corner c ∈ d.piece j)
    (hcount : d.cornerTileCount c = 2) (hki : k ≠ i) (hkj : k ≠ j) :
    corner c ∉ d.piece k := by
  classical
  intro hck
  change (Finset.univ.filter fun l => corner c ∈ d.piece l).card = 2 at hcount
  have hsub : ({i, j, k} : Finset (Fin 4)) ⊆
      Finset.univ.filter fun l => corner c ∈ d.piece l := by
    intro l hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl | rfl
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hci
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hcj
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hck
  have hthree : ({i, j, k} : Finset (Fin 4)).card = 3 :=
    Finset.card_triple_eq_three_iff.mpr ⟨hij, hki.symm, hkj.symm⟩
  have hle := Finset.card_le_card hsub
  rw [hthree, hcount] at hle
  omega

/-- A piece missing three distinct physical corners has at most one corner. -/
theorem tile_count_le_one_of_three_corners_missing (d : SquareDissection)
    {k a b c : Fin 4} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : corner a ∉ d.piece k) (hb : corner b ∉ d.piece k)
    (hc : corner c ∉ d.piece k) : d.tileCornerCount k ≤ 1 := by
  classical
  have hsub : (Finset.univ.filter fun l => corner l ∈ d.piece k) ⊆
      Finset.univ \ ({a, b, c} : Finset (Fin 4)) := by
    intro l hl
    have hlmem : corner l ∈ d.piece k := (Finset.mem_filter.mp hl).2
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ l, ?_⟩
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro (rfl | rfl | rfl)
    · exact ha hlmem
    · exact hb hlmem
    · exact hc hlmem
  have hthree : ({a, b, c} : Finset (Fin 4)).card = 3 :=
    Finset.card_triple_eq_three_iff.mpr ⟨hab, hac, hbc⟩
  have hremain : (Finset.univ \ ({a, b, c} : Finset (Fin 4))).card = 1 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, hthree]
    decide
  change (Finset.univ.filter fun l => corner l ∈ d.piece k).card ≤ 1
  rw [← hremain]
  exact Finset.card_le_card hsub

/-- A pair of uniquely owned endpoints and a shared corner of multiplicity
two leave every other piece with at most one physical corner. -/
theorem other_tile_count_le_one_of_unique_ends_and_double_corner
    (d : SquareDissection) {i j k a b c : Fin 4} (hij : i ≠ j)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (haunique : ∀ l, l ≠ i → corner a ∉ d.piece l)
    (hbunique : ∀ l, l ≠ j → corner b ∉ d.piece l)
    (hci : corner c ∈ d.piece i) (hcj : corner c ∈ d.piece j)
    (hcount : d.cornerTileCount c = 2) (hki : k ≠ i) (hkj : k ≠ j) :
    d.tileCornerCount k ≤ 1 :=
  tile_count_le_one_of_three_corners_missing d hab hac hbc
    (haunique k hki) (hbunique k hkj)
    (other_not_mem_of_two_owners d hij hci hcj hcount hki hkj)

/-- In particular, no third two-corner piece can occur in this situation. -/
theorem no_third_double_tile_of_unique_ends_and_double_corner
    (d : SquareDissection) {i j k a b c : Fin 4} (hij : i ≠ j)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (haunique : ∀ l, l ≠ i → corner a ∉ d.piece l)
    (hbunique : ∀ l, l ≠ j → corner b ∉ d.piece l)
    (hci : corner c ∈ d.piece i) (hcj : corner c ∈ d.piece j)
    (hcount : d.cornerTileCount c = 2) (hki : k ≠ i) (hkj : k ≠ j) :
    d.tileCornerCount k ≠ 2 := by
  have hle := other_tile_count_le_one_of_unique_ends_and_double_corner d hij
    hab hac hbc haunique hbunique hci hcj hcount hki hkj
  omega

end Puzzling139335.N6.TwoDouble
