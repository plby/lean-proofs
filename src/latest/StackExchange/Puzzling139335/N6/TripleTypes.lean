import StackExchange.Puzzling139335.N6.Incidence
import StackExchange.Puzzling139335.N5.TypeReduction

/-!
# The intrinsic types at a triple square corner

Three uniquely owned physical corners require at least two full types.
They are disjoint from the types used at the triple corner. Therefore the
three-type bound leaves one common intrinsic point for all three owners
of that corner, without presupposing any local angle.
-/

open Set

namespace Puzzling139335.N6

open N5

theorem two_le_fullCornerTypes_card_of_triple (d : SquareDissection)
    (hc : d.HasProtectedCenter) (htriple : HasTripleCorner d) :
    2 ≤ (fullCornerTypes d).card := by
  obtain ⟨s, _, hother⟩ := htriple
  have h₁ : s + 1 ≠ s := by fin_cases s <;> decide
  have h₂ : s + 2 ≠ s := by fin_cases s <;> decide
  have h₃ : s + 3 ≠ s := by fin_cases s <;> decide
  have h₁₂ : s + 1 ≠ s + 2 := by fin_cases s <;> decide
  have h₁₃ : s + 1 ≠ s + 3 := by fin_cases s <;> decide
  have h₂₃ : s + 2 ≠ s + 3 := by fin_cases s <;> decide
  exact two_le_fullCornerTypes_card_of_three_unique_corners d hc
    (s + 1) (s + 2) (s + 3) h₁₂ h₁₃ h₂₃
    (hother (s + 1) h₁) (hother (s + 2) h₂) (hother (s + 3) h₃)

theorem splitCornerTypes_nonempty_of_triple (d : SquareDissection)
    (htriple : HasTripleCorner d) : (splitCornerTypes d).Nonempty := by
  obtain ⟨s, hs, _⟩ := htriple
  obtain ⟨i, hi⟩ := d.exists_piece_mem (corner_mem_unitSquare s)
  exact ⟨d.intrinsicCorner i s,
    (mem_splitCornerTypes d).mpr ⟨i, s, hi, by omega, rfl⟩⟩

/-- Exactly two full types and one split type occur in the triple-corner branch. -/
theorem type_cardinalities_of_triple (d : SquareDissection)
    (hc : d.HasProtectedCenter) (htriple : HasTripleCorner d)
    (htypes : d.usedCornerTypes.card ≤ 3) :
    (fullCornerTypes d).card = 2 ∧ (splitCornerTypes d).card = 1 ∧
      d.usedCornerTypes.card = 3 := by
  classical
  have hfull := two_le_fullCornerTypes_card_of_triple d hc htriple
  have hsplit := Finset.card_pos.mpr (splitCornerTypes_nonempty_of_triple d htriple)
  have hsum := Finset.card_union_of_disjoint (full_split_disjoint d)
  rw [← usedCornerTypes_eq_union d] at hsum
  omega

/-- The three actual owners of the triple corner use the same prototype point. -/
theorem intrinsicCorners_eq_at_triple (d : SquareDissection)
    (hc : d.HasProtectedCenter) (hN : d.cornerIncidenceCount = 6)
    (htypes : d.usedCornerTypes.card ≤ 3) {s i j : Fin 4}
    (hs : d.cornerTileCount s = 3) (hi : corner s ∈ d.piece i)
    (hj : corner s ∈ d.piece j) :
    d.intrinsicCorner i s = d.intrinsicCorner j s := by
  classical
  have htriple : HasTripleCorner d :=
    ⟨s, hs, fun _ hne => unique_away_from_triple d hN hs hne⟩
  have hcard := (type_cardinalities_of_triple d hc htriple htypes).2.1
  exact Finset.card_le_one_iff.mp hcard.le
    ((mem_splitCornerTypes d).mpr ⟨i, s, hi, by omega, rfl⟩)
    ((mem_splitCornerTypes d).mpr ⟨j, s, hj, by omega, rfl⟩)

/-- A concrete enumeration of the owners and their common intrinsic point,
ready for the boundary-germ parity theorem. -/
theorem triple_owners_common_type (d : SquareDissection)
    (hc : d.HasProtectedCenter) (hN : d.cornerIncidenceCount = 6)
    (htypes : d.usedCornerTypes.card ≤ 3) {s : Fin 4}
    (hs : d.cornerTileCount s = 3) :
    ∃ i j k : Fin 4, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
      (∀ l, corner s ∈ d.piece l ↔ l = i ∨ l = j ∨ l = k) ∧
      d.intrinsicCorner i s = d.intrinsicCorner j s ∧
      d.intrinsicCorner i s = d.intrinsicCorner k s := by
  obtain ⟨i, j, k, hij, hik, hjk, howners⟩ := triple_corner_owners d s hs
  have hi : corner s ∈ d.piece i := (howners i).mpr (Or.inl rfl)
  have hj : corner s ∈ d.piece j := (howners j).mpr (Or.inr (Or.inl rfl))
  have hk : corner s ∈ d.piece k := (howners k).mpr (Or.inr (Or.inr rfl))
  exact ⟨i, j, k, hij, hik, hjk, howners,
    intrinsicCorners_eq_at_triple d hc hN htypes hs hi hj,
    intrinsicCorners_eq_at_triple d hc hN htypes hs hi hk⟩

end Puzzling139335.N6
