import StackExchange.Puzzling139335.N5.FullType
import StackExchange.Puzzling139335.N5.FullCount

/-!
# The three intrinsic types in the five-incidence case

Actual full neighborhoods separate the types occurring at unique corners
from those occurring at shared corners.  With three uniquely owned
physical corners, the square-symmetry orbit obstruction requires two full
types.  The upper bound of three types then leaves exactly one shared type.
-/

open Set

namespace Puzzling139335.N5

theorem unique_corner_of_count_one (d : SquareDissection) {i j : Fin 4}
    (hcount : d.cornerTileCount j = 1) (hi : corner j ∈ d.piece i) :
    ∀ m, m ≠ i → corner j ∉ d.piece m := by
  obtain ⟨k, _, hk⟩ := unique_owner_of_count_one d j hcount
  intro m hmi hm
  exact hmi ((hk m hm).trans (hk i hi).symm)

theorem corner_count_one_of_unique_owner (d : SquareDissection) {i j : Fin 4}
    (hi : corner j ∈ d.piece i)
    (hunique : ∀ m, m ≠ i → corner j ∉ d.piece m) : d.cornerTileCount j = 1 := by
  classical
  change (Finset.univ.filter fun k => corner j ∈ d.piece k).card = 1
  apply Finset.card_eq_one_iff_existsUnique.mpr
  refine ⟨i, by simp [hi], ?_⟩
  intro m hm
  by_contra hmi
  exact hunique m hmi (Finset.mem_filter.mp hm).2

/-- A point occurring at a unique corner cannot also occur at any shared
corner, regardless of the total incidence count. -/
theorem full_split_disjoint (d : SquareDissection) :
    Disjoint (fullCornerTypes d) (splitCornerTypes d) := by
  classical
  apply Finset.disjoint_left.mpr
  intro v hvFull hvSplit
  obtain ⟨i, j, hij, hcount, hv⟩ := (mem_fullCornerTypes d).mp hvFull
  obtain ⟨k, l, hkl, hshared, hv'⟩ := (mem_splitCornerTypes d).mp hvSplit
  have hunique := unique_corner_of_equal_intrinsicCorner d
    (unique_corner_of_count_one d hcount hij) (hv.trans hv'.symm)
  have hone := corner_count_one_of_unique_owner d hkl hunique
  omega

theorem isFullSquareCorner_of_mem_fullCornerTypes (d : SquareDissection) {v : Plane}
    (hv : v ∈ fullCornerTypes d) : UnitPairs.IsFullSquareCorner (d.piece 0) v := by
  obtain ⟨i, j, hij, hcount, rfl⟩ := (mem_fullCornerTypes d).mp hv
  exact isFullSquareCorner_of_unique_corner d i j
    (unique_corner_of_count_one d hcount hij)

/-- Any placement of a type known to be full has a uniquely owned target
corner; the uniqueness is not merely a property of its first occurrence. -/
theorem unique_corner_of_type_mem_full (d : SquareDissection) {i j : Fin 4}
    (hfull : d.intrinsicCorner i j ∈ fullCornerTypes d) :
    ∀ m, m ≠ i → corner j ∉ d.piece m := by
  obtain ⟨k, l, hkl, hcount, htype⟩ := (mem_fullCornerTypes d).mp hfull
  exact unique_corner_of_equal_intrinsicCorner d
    (unique_corner_of_count_one d hcount hkl) htype

theorem tileCornerCount_eq_of_full_type (d : SquareDissection) {i j k l : Fin 4}
    (hfull : d.intrinsicCorner i j ∈ fullCornerTypes d)
    (htype : d.intrinsicCorner i j = d.intrinsicCorner k l) :
    d.tileCornerCount i = d.tileCornerCount k :=
  d.tileCornerCount_eq_of_repeated_unique_corner
    (unique_corner_of_type_mem_full d hfull) htype

/-- The type counts forced by five incidences and the three-type bound. -/
theorem type_cardinalities_of_five (d : SquareDissection)
    (hc : d.HasProtectedCenter) (hN : d.cornerIncidenceCount = 5)
    (htypes : d.usedCornerTypes.card ≤ 3) :
    (fullCornerTypes d).card = 2 ∧ (splitCornerTypes d).card = 1 ∧
      d.usedCornerTypes.card = 3 := by
  classical
  have hfull := two_le_fullCornerTypes_card_of_five d hc hN
  have hsplit := Finset.card_pos.mpr (splitCornerTypes_nonempty_of_five d hN)
  have hsum := Finset.card_union_of_disjoint (full_split_disjoint d)
  rw [← usedCornerTypes_eq_union d] at hsum
  omega

theorem intrinsicCorners_eq_at_split (d : SquareDissection)
    (hc : d.HasProtectedCenter) (hN : d.cornerIncidenceCount = 5)
    (htypes : d.usedCornerTypes.card ≤ 3) {s i j : Fin 4}
    (hs : d.cornerTileCount s = 2) (hi : corner s ∈ d.piece i)
    (hj : corner s ∈ d.piece j) :
    d.intrinsicCorner i s = d.intrinsicCorner j s := by
  classical
  have hcard := (type_cardinalities_of_five d hc hN htypes).2.1
  exact Finset.card_le_one_iff.mp hcard.le
    ((mem_splitCornerTypes d).mpr ⟨i, s, hi, by omega, rfl⟩)
    ((mem_splitCornerTypes d).mpr ⟨j, s, hj, by omega, rfl⟩)

/-- The two full types and the single shared type are three distinct
actual prototype points, not labels added to the dissection data. -/
theorem exists_three_types (d : SquareDissection)
    (hc : d.HasProtectedCenter) (hN : d.cornerIncidenceCount = 5)
    (htypes : d.usedCornerTypes.card ≤ 3) :
    ∃ A B C : Plane, A ≠ B ∧ A ≠ C ∧ B ≠ C ∧
      splitCornerTypes d = {A} ∧ fullCornerTypes d = {B, C} ∧
      d.usedCornerTypes = {A, B, C} ∧
      UnitPairs.IsFullSquareCorner (d.piece 0) B ∧
      UnitPairs.IsFullSquareCorner (d.piece 0) C := by
  classical
  obtain ⟨hfull, hsplit, _⟩ := type_cardinalities_of_five d hc hN htypes
  obtain ⟨A, hA⟩ := Finset.card_eq_one.mp hsplit
  obtain ⟨B, C, hBC, hBCset⟩ := Finset.card_eq_two.mp hfull
  have hBmem : B ∈ fullCornerTypes d := by rw [hBCset]; simp
  have hCmem : C ∈ fullCornerTypes d := by rw [hBCset]; simp
  have hAmem : A ∈ splitCornerTypes d := by rw [hA]; simp
  have hAB : A ≠ B := by
    intro h
    exact Finset.disjoint_left.mp (full_split_disjoint d) (h.symm ▸ hBmem) hAmem
  have hAC : A ≠ C := by
    intro h
    exact Finset.disjoint_left.mp (full_split_disjoint d) (h.symm ▸ hCmem) hAmem
  refine ⟨A, B, C, hAB, hAC, hBC, hA, hBCset, ?_,
    isFullSquareCorner_of_mem_fullCornerTypes d hBmem,
    isFullSquareCorner_of_mem_fullCornerTypes d hCmem⟩
  rw [usedCornerTypes_eq_union, hA, hBCset]
  ext v
  simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
  tauto

end Puzzling139335.N5
