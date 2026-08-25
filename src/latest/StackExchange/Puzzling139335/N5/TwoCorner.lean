import StackExchange.Puzzling139335.N5.TypeReduction
import StackExchange.Puzzling139335.AcuteCorner

/-!
# Two-corner tiles contain the shared corner

A shared intrinsic type with an actual forty-five-degree supporting cone
must occur at one endpoint of every two-corner placement.  Disjointness of
full and shared types then identifies that endpoint as the shared corner.
-/

open Set

namespace Puzzling139335.N5

/-- The two actual corner indices of a tile of corner count two. -/
theorem two_corners_of_count_two (d : SquareDissection) (i : Fin 4)
    (hdeg : d.tileCornerCount i = 2) :
    ∃ a b : Fin 4, a ≠ b ∧
      ∀ j, corner j ∈ d.piece i ↔ j = a ∨ j = b := by
  classical
  change (Finset.univ.filter fun j => corner j ∈ d.piece i).card = 2 at hdeg
  obtain ⟨a, b, hab, hset⟩ := Finset.card_eq_two.mp hdeg
  refine ⟨a, b, hab, ?_⟩
  intro j
  have hj := Finset.ext_iff.mp hset j
  simpa only [Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_insert, Finset.mem_singleton] using hj

/-- A tile with two corners and a specified first corner has a different
second corner. -/
theorem second_corner_of_count_two (d : SquareDissection) (i s : Fin 4)
    (hdeg : d.tileCornerCount i = 2) (hs : corner s ∈ d.piece i) :
    ∃ a : Fin 4, a ≠ s ∧ corner a ∈ d.piece i := by
  obtain ⟨a, b, hab, hcorners⟩ := two_corners_of_count_two d i hdeg
  rcases (hcorners s).mp hs with hsa | hsb
  · refine ⟨b, ?_, (hcorners b).mpr (Or.inr rfl)⟩
    intro hbs
    exact hab (hsa.symm.trans hbs.symm)
  · refine ⟨a, ?_, (hcorners a).mpr (Or.inl rfl)⟩
    intro has
    exact hab (has.trans hsb)

theorem unique_corner_of_tile_count_one (d : SquareDissection) (i : Fin 4)
    (hdeg : d.tileCornerCount i = 1) : ∃! j, corner j ∈ d.piece i := by
  classical
  change (Finset.univ.filter fun j => corner j ∈ d.piece i).card = 1 at hdeg
  simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using
    Finset.card_eq_one_iff_existsUnique.mp hdeg

theorem corner_of_count_one (d : SquareDissection) (i : Fin 4)
    (hdeg : d.tileCornerCount i = 1) : ∃ j, corner j ∈ d.piece i :=
  (unique_corner_of_tile_count_one d i hdeg).exists

theorem no_corner_of_count_zero (d : SquareDissection) (i : Fin 4)
    (hdeg : d.tileCornerCount i = 0) (j : Fin 4) : corner j ∉ d.piece i := by
  classical
  intro hj
  change (Finset.univ.filter fun j => corner j ∈ d.piece i).card = 0 at hdeg
  have hpos : 0 < (Finset.univ.filter fun j => corner j ∈ d.piece i).card :=
    Finset.card_pos.mpr ⟨j, by simp [hj]⟩
  omega

theorem count_two_of_two_corners (d : SquareDissection)
    (hc : d.HasProtectedCenter) (i : Fin 4) {a b : Fin 4}
    (hab : a ≠ b) (ha : corner a ∈ d.piece i) (hb : corner b ∈ d.piece i) :
    d.tileCornerCount i = 2 := by
  classical
  apply le_antisymm (d.tileCornerCount_le_two hc i)
  change 2 ≤ (Finset.univ.filter fun j => corner j ∈ d.piece i).card
  have hsub : ({a, b} : Finset (Fin 4)) ⊆
      Finset.univ.filter fun j => corner j ∈ d.piece i := by
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · simp [ha]
    · have hja := Finset.mem_singleton.mp hj
      subst j
      simp [hb]
  simpa [hab] using Finset.card_le_card hsub

/-- Every actual corner occurrence of a shared type is at the unique
shared physical corner. -/
theorem corner_eq_split_of_type_mem_split (d : SquareDissection)
    (hN : d.cornerIncidenceCount = 5) {s i j : Fin 4}
    (hs : d.cornerTileCount s = 2) (hj : corner j ∈ d.piece i)
    (htype : d.intrinsicCorner i j ∈ splitCornerTypes d) : j = s := by
  classical
  by_contra hjs
  have hcount := count_one_of_ne_split d hN hs hjs
  have hfull : d.intrinsicCorner i j ∈ fullCornerTypes d :=
    (mem_fullCornerTypes d).mpr ⟨i, j, hj, hcount, rfl⟩
  exact Finset.disjoint_left.mp (full_split_disjoint d) hfull htype

/-- The support-cone conclusion with two actual distinct corner memberships
as hypotheses, without a corner-count hypothesis. -/
theorem contains_split_of_two_corners_of_support45 (d : SquareDissection)
    (hc : d.HasProtectedCenter) (hN : d.cornerIncidenceCount = 5)
    {s : Fin 4} {A : Plane} (hs : d.cornerTileCount s = 2)
    (hA : A ∈ splitCornerTypes d)
    (h45 : AcuteCorner.Supports45 (d.piece 0) A)
    (i a b : Fin 4) (hab : a ≠ b)
    (ha : corner a ∈ d.piece i) (hb : corner b ∈ d.piece i) :
    corner s ∈ d.piece i := by
  have hA0 : A ∈ d.piece 0 :=
    d.usedCornerTypes_subset (splitCornerTypes_subset_used d hA)
  have hpair := d.support45_preimage_eq_of_two_corners hc i a b hab ha hb
    (d.placement i) (d.placement_image i) hA0 h45
  change A = d.intrinsicCorner i a ∨ A = d.intrinsicCorner i b at hpair
  rcases hpair with h | h
  · have has := corner_eq_split_of_type_mem_split d hN hs ha (h ▸ hA)
    exact has ▸ ha
  · have hbs := corner_eq_split_of_type_mem_split d hN hs hb (h ▸ hA)
    exact hbs ▸ hb

/-- An actual two-corner tile must contain the unique shared corner whenever
the shared type has a forty-five-degree supporting cone. -/
theorem double_contains_split_of_support45 (d : SquareDissection)
    (hc : d.HasProtectedCenter) (hN : d.cornerIncidenceCount = 5)
    {s : Fin 4} {A : Plane} (hs : d.cornerTileCount s = 2)
    (hA : A ∈ splitCornerTypes d)
    (h45 : AcuteCorner.Supports45 (d.piece 0) A)
    (i : Fin 4) (hdeg : d.tileCornerCount i = 2) : corner s ∈ d.piece i := by
  obtain ⟨a, b, hab, hcorners⟩ := two_corners_of_count_two d i hdeg
  exact contains_split_of_two_corners_of_support45 d hc hN hs hA h45 i a b hab
    ((hcorners a).mpr (Or.inl rfl)) ((hcorners b).mpr (Or.inr rfl))

end Puzzling139335.N5
