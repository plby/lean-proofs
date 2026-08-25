import StackExchange.Puzzling139335.RepeatedCorners
import StackExchange.Puzzling139335.SymmetryOrbit

/-!
# Intrinsic types at unique and shared square corners

These finite sets are extracted from the actual chosen placements.  The
three-copy obstruction is applied only after equality of intrinsic points
has produced actual square symmetries between distinct pieces.
-/

open Set

namespace Puzzling139335.N5

noncomputable section

open scoped Classical in
/-- Intrinsic points occurring at a uniquely owned square corner. -/
def fullCornerTypes (d : SquareDissection) : Finset Plane :=
  (d.cornerOccurrences.filter fun q => d.cornerTileCount q.2 = 1).image
    fun q => d.intrinsicCorner q.1 q.2

open scoped Classical in
/-- Intrinsic points occurring at a square corner shared by multiple tiles. -/
def splitCornerTypes (d : SquareDissection) : Finset Plane :=
  (d.cornerOccurrences.filter fun q => 1 < d.cornerTileCount q.2).image
    fun q => d.intrinsicCorner q.1 q.2

theorem mem_fullCornerTypes (d : SquareDissection) {v : Plane} :
    v ∈ fullCornerTypes d ↔ ∃ i j : Fin 4,
      corner j ∈ d.piece i ∧ d.cornerTileCount j = 1 ∧ d.intrinsicCorner i j = v := by
  classical
  constructor
  · intro hv
    obtain ⟨q, hq, hqv⟩ := Finset.mem_image.mp hv
    obtain ⟨hq, hcount⟩ := Finset.mem_filter.mp hq
    exact ⟨q.1, q.2, (d.mem_cornerOccurrences q).mp hq, hcount, hqv⟩
  · rintro ⟨i, j, hij, hcount, hv⟩
    exact Finset.mem_image.mpr ⟨(i, j),
      Finset.mem_filter.mpr ⟨(d.mem_cornerOccurrences (i, j)).mpr hij, hcount⟩, hv⟩

theorem mem_splitCornerTypes (d : SquareDissection) {v : Plane} :
    v ∈ splitCornerTypes d ↔ ∃ i j : Fin 4,
      corner j ∈ d.piece i ∧ 1 < d.cornerTileCount j ∧ d.intrinsicCorner i j = v := by
  classical
  constructor
  · intro hv
    obtain ⟨q, hq, hqv⟩ := Finset.mem_image.mp hv
    obtain ⟨hq, hcount⟩ := Finset.mem_filter.mp hq
    exact ⟨q.1, q.2, (d.mem_cornerOccurrences q).mp hq, hcount, hqv⟩
  · rintro ⟨i, j, hij, hcount, hv⟩
    exact Finset.mem_image.mpr ⟨(i, j),
      Finset.mem_filter.mpr ⟨(d.mem_cornerOccurrences (i, j)).mpr hij, hcount⟩, hv⟩

theorem fullCornerTypes_subset_used (d : SquareDissection) :
    fullCornerTypes d ⊆ d.usedCornerTypes := by
  intro v hv
  obtain ⟨i, j, hij, _, hv⟩ := (mem_fullCornerTypes d).mp hv
  exact d.mem_usedCornerTypes.mpr ⟨i, j, hij, hv⟩

theorem splitCornerTypes_subset_used (d : SquareDissection) :
    splitCornerTypes d ⊆ d.usedCornerTypes := by
  intro v hv
  obtain ⟨i, j, hij, _, hv⟩ := (mem_splitCornerTypes d).mp hv
  exact d.mem_usedCornerTypes.mpr ⟨i, j, hij, hv⟩

theorem usedCornerTypes_eq_union (d : SquareDissection) :
    d.usedCornerTypes = fullCornerTypes d ∪ splitCornerTypes d := by
  classical
  ext v
  constructor
  · intro hv
    obtain ⟨i, j, hij, hv⟩ := d.mem_usedCornerTypes.mp hv
    by_cases hcount : d.cornerTileCount j = 1
    · exact Finset.mem_union_left _ ((mem_fullCornerTypes d).mpr ⟨i, j, hij, hcount, hv⟩)
    · have hpos := d.cornerTileCount_pos j
      have hgt : 1 < d.cornerTileCount j := by omega
      exact Finset.mem_union_right _ ((mem_splitCornerTypes d).mpr ⟨i, j, hij, hgt, hv⟩)
  · intro hv
    rcases Finset.mem_union.mp hv with hv | hv
    · exact fullCornerTypes_subset_used d hv
    · exact splitCornerTypes_subset_used d hv

/-- One intrinsic unique-corner type cannot account for three different
square corners in a protected-center dissection. -/
theorem not_three_equal_unique_types (d : SquareDissection)
    (hc : d.HasProtectedCenter) {i j k a b c : Fin 4}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hunique : ∀ m, m ≠ i → corner a ∉ d.piece m)
    (ht₁ : d.intrinsicCorner i a = d.intrinsicCorner j b)
    (ht₂ : d.intrinsicCorner i a = d.intrinsicCorner k c) : False := by
  have hij : i ≠ j := by
    intro h
    subst j
    exact hab (d.intrinsicCorner_injective i ht₁)
  have hik : i ≠ k := by
    intro h
    subst k
    exact hac (d.intrinsicCorner_injective i ht₂)
  have hjk : j ≠ k := by
    intro h
    subst k
    exact hbc (d.intrinsicCorner_injective j (ht₁.symm.trans ht₂))
  exact d.not_hasProtectedCenter_of_three_square_symmetry_copies hij hik hjk
    (d.relativePlacement i j) (d.relativePlacement i k)
    (d.relativePlacement_preserves_square_of_unique_corner hunique ht₁).subset
    (d.relativePlacement_preserves_square_of_unique_corner hunique ht₂).subset
    (d.relativePlacement_image i j) (d.relativePlacement_image i k) hc

end

end Puzzling139335.N5
