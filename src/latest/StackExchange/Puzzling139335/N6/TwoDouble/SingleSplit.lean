import StackExchange.Puzzling139335.N6.TwoDouble.TypeReduction
import StackExchange.Puzzling139335.DoubleCorner

/-!
# A single split-corner type excludes the center

Each of the two double corners is a repeated intrinsic corner. The
arbitrary-Jordan double-corner theorem excludes both owners, and the
finite owner-set argument shows that this accounts for all four pieces.
-/

open Set

namespace Puzzling139335.N6.TwoDouble

theorem center_excluded_of_one_split_type (d : SquareDissection)
    (hcard : (N5.splitCornerTypes d).card ≤ 1) {s : Fin 4}
    (hs : d.cornerTileCount s = 2) :
    ∀ k : Fin 4, corner s ∈ d.piece k → squareCenter ∉ interior (d.piece k) := by
  obtain ⟨i, j, hij, howners⟩ := N5.split_corner_owners d s hs
  have hi : corner s ∈ d.piece i := (howners i).mpr (Or.inl rfl)
  have hj : corner s ∈ d.piece j := (howners j).mpr (Or.inr rfl)
  have hother : ∀ l, l ≠ i → l ≠ j → corner s ∉ d.piece l := by
    intro l hli hlj hl
    exact ((howners l).mp hl).elim hli hlj
  have htype := intrinsic_eq_of_one_split_type d hcard hs hi hj
  have h := d.same_intrinsic_double_corner hij hi hj hother htype
  intro k hk
  rcases (howners k).mp hk with rfl | rfl
  · exact h.2.2.1
  · exact h.2.2.2

/-- Two double corners cannot be supplied by just one intrinsic split
type in a dissection with a protected center. -/
theorem not_protected_of_one_split_type (d : SquareDissection)
    (hD : HasTwoDoubleCorners d) (hcard : (N5.splitCornerTypes d).card ≤ 1) :
    ¬ d.HasProtectedCenter := by
  obtain ⟨s, t, hst, hs, ht, _⟩ := hD
  rintro ⟨i, hi⟩
  rcases all_pieces_own_split_of_one_type d hst hs ht hcard i with his | hit
  · exact center_excluded_of_one_split_type d hcard hs i his hi
  · exact center_excluded_of_one_split_type d hcard ht i hit hi

/-- Thus the two-double-corner branch has exactly one full type and two
split types; all three are actual prototype points. -/
theorem type_cardinalities (d : SquareDissection) (hc : d.HasProtectedCenter)
    (hU : d.usedCornerTypes.card ≤ 3) (hD : HasTwoDoubleCorners d) :
    (N5.fullCornerTypes d).card = 1 ∧ (N5.splitCornerTypes d).card = 2 ∧
      d.usedCornerTypes.card = 3 := by
  have hnot : ¬ (N5.splitCornerTypes d).card ≤ 1 :=
    fun h => not_protected_of_one_split_type d hD h hc
  exact one_full_type_of_two_split_types d hU hD (by omega)

/-- The full unit-pair reduction now has only the original geometric
and incidence assumptions, with no separate type-case premise. -/
theorem exists_actual_full_pair (d : SquareDissection) (hc : d.HasProtectedCenter)
    (hN : d.cornerIncidenceCount = 6) (hU : d.usedCornerTypes.card ≤ 3)
    (hD : HasTwoDoubleCorners d) :
    ∃ i j : Fin 4, i ≠ j ∧ ∃ r v : Plane, r ≠ v ∧
      UnitPairs.IsFullSquareCorner (d.piece 0) r ∧
      N8.intrinsicPair d i = {r, v} ∧ N8.intrinsicPair d j = {r, v} ∧
      d.relativePlacement i j '' unitSquare = unitSquare ∧
      squareCenter ∉ interior (d.piece i) ∧ squareCenter ∉ interior (d.piece j) :=
  exists_full_pair_of_one_full_type d hc hN hU hD (type_cardinalities d hc hU hD).1.le

/-- The full-pair reduction retaining the two physical uniquely owned
corners. This form supports normalization without identifying a chosen
prototype placement with the identity. -/
theorem exists_actual_full_pair_with_unique (d : SquareDissection)
    (hc : d.HasProtectedCenter) (hN : d.cornerIncidenceCount = 6)
    (hU : d.usedCornerTypes.card ≤ 3) (hD : HasTwoDoubleCorners d) :
    ∃ i j a b : Fin 4, i ≠ j ∧ a ≠ b ∧
      corner a ∈ d.piece i ∧ corner b ∈ d.piece j ∧
      d.cornerTileCount a = 1 ∧ d.cornerTileCount b = 1 ∧
      d.intrinsicCorner i a = d.intrinsicCorner j b ∧
      ∃ v : Plane, d.intrinsicCorner i a ≠ v ∧
        d.intrinsicCorner i a ∈ N5.fullCornerTypes d ∧
        UnitPairs.IsFullSquareCorner (d.piece 0) (d.intrinsicCorner i a) ∧
        N8.intrinsicPair d i = {d.intrinsicCorner i a, v} ∧
        N8.intrinsicPair d j = {d.intrinsicCorner i a, v} ∧
        d.relativePlacement i j '' unitSquare = unitSquare ∧
        squareCenter ∉ interior (d.piece i) ∧ squareCenter ∉ interior (d.piece j) := by
  classical
  have hfullCount := (type_cardinalities d hc hU hD).1.le
  obtain ⟨a, b, hab, hac, hbc⟩ := exists_two_unique_corners d hD
  obtain ⟨i, hi, hui⟩ := N5.unique_owner_of_count_one d a hac
  obtain ⟨j, hj, _⟩ := N5.unique_owner_of_count_one d b hbc
  have hri : d.intrinsicCorner i a ∈ N5.fullCornerTypes d :=
    (N5.mem_fullCornerTypes d).mpr ⟨i, a, hi, hac, rfl⟩
  have hrj : d.intrinsicCorner j b ∈ N5.fullCornerTypes d :=
    (N5.mem_fullCornerTypes d).mpr ⟨j, b, hj, hbc, rfl⟩
  have htype : d.intrinsicCorner i a = d.intrinsicCorner j b :=
    Finset.card_le_one_iff.mp hfullCount hri hrj
  have hij : i ≠ j := by
    intro heq
    subst j
    exact hab (d.intrinsicCorner_injective i htype)
  have hunique : ∀ l, l ≠ i → corner a ∉ d.piece l := by
    intro l hli hl
    exact hli (hui l hl)
  obtain ⟨v, hv, hfull, hip, hjp, hS, hci, hcj⟩ :=
    repeated_full_pair d hc hN hU hij hi hunique htype
  exact ⟨i, j, a, b, hij, hab, hi, hj, hac, hbc, htype,
    v, hv, hri, hfull, hip, hjp, hS, hci, hcj⟩

end Puzzling139335.N6.TwoDouble
