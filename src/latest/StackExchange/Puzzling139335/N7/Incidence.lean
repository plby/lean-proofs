import StackExchange.Puzzling139335.InitialReduction
import Mathlib.Data.Fin.Tuple.Sort

/-!
# The incidence patterns when the total is seven

The degrees in this file count actual membership of square corners in the
pieces.  Under the protected-center assumption, exactly one piece has one
corner, and the other three have two.  The corner multiplicities, up to a
permutation, are `2221` or `3211`.
-/

open Set
open scoped BigOperators

namespace Puzzling139335

namespace SquareDissection

/-- A corner of multiplicity one belongs to exactly one piece.  This does not
depend on the total incidence count. -/
theorem existsUnique_corner_owner_of_count_one (d : SquareDissection) (j : Fin 4)
    (hj : d.cornerTileCount j = 1) : ∃! i, corner j ∈ d.piece i := by
  classical
  change (Finset.univ.filter fun i => corner j ∈ d.piece i).card = 1 at hj
  simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using
    Finset.card_eq_one_iff_existsUnique.mp hj

/-- Membership of a corner of multiplicity one excludes every other piece. -/
theorem unique_corner_owner_of_count_one (d : SquareDissection) {i j : Fin 4}
    (hj : d.cornerTileCount j = 1) (hi : corner j ∈ d.piece i) :
    ∀ k, k ≠ i → corner j ∉ d.piece k := by
  obtain ⟨l, _, hl⟩ := d.existsUnique_corner_owner_of_count_one j hj
  intro k hki hk
  exact hki ((hl k hk).trans (hl i hi).symm)

end SquareDissection

namespace N7

/-- The four actual pieces can be ordered with corner counts `2221`. -/
theorem tile_count_pattern (d : SquareDissection)
    (hc : d.HasProtectedCenter) (hN : d.cornerIncidenceCount = 7) :
    ∃ σ : Equiv.Perm (Fin 4),
      d.tileCornerCount (σ 0) = 2 ∧ d.tileCornerCount (σ 1) = 2 ∧
        d.tileCornerCount (σ 2) = 2 ∧ d.tileCornerCount (σ 3) = 1 := by
  let f : Fin 4 → ℕᵒᵈ := fun i => d.tileCornerCount i
  let σ : Equiv.Perm (Fin 4) := Tuple.sort f
  have hmono := Tuple.monotone_sort f
  have hsorted : CornerCounting.SortedFour
      (d.tileCornerCount (σ 0)) (d.tileCornerCount (σ 1))
      (d.tileCornerCount (σ 2)) (d.tileCornerCount (σ 3)) :=
    ⟨hmono (by decide : (0 : Fin 4) ≤ 1),
      hmono (by decide : (1 : Fin 4) ≤ 2),
      hmono (by decide : (2 : Fin 4) ≤ 3)⟩
  have hsum : (∑ i, d.tileCornerCount (σ i)) = 7 := by
    rw [Equiv.sum_comp σ]
    exact d.cornerIncidenceCount_eq_sum_tileCornerCount.symm.trans hN
  rw [CornerCounting.sum_fin_four] at hsum
  exact ⟨σ, CornerCounting.tile_degrees_sum_seven hsorted
    (d.tileCornerCount_le_two hc (σ 0)) hsum⟩

/-- There is a one-corner piece, and every other piece has two corners. -/
theorem exists_one_corner_tile (d : SquareDissection)
    (hc : d.HasProtectedCenter) (hN : d.cornerIncidenceCount = 7) :
    ∃ i : Fin 4, d.tileCornerCount i = 1 ∧
      ∀ k, k ≠ i → d.tileCornerCount k = 2 := by
  obtain ⟨σ, h0, h1, h2, h3⟩ := tile_count_pattern d hc hN
  refine ⟨σ 3, h3, ?_⟩
  intro k hk
  obtain ⟨j, rfl⟩ := σ.surjective k
  fin_cases j <;> simp_all

/-- Every piece has either one or two corners. -/
theorem tileCornerCount_eq_one_or_two (d : SquareDissection)
    (hc : d.HasProtectedCenter) (hN : d.cornerIncidenceCount = 7) (i : Fin 4) :
    d.tileCornerCount i = 1 ∨ d.tileCornerCount i = 2 := by
  obtain ⟨j, hj, hother⟩ := exists_one_corner_tile d hc hN
  by_cases hij : i = j
  · exact Or.inl (hij ▸ hj)
  · exact Or.inr (hother i hij)

/-- Exactly one piece has a single square corner. -/
theorem existsUnique_one_corner_tile (d : SquareDissection)
    (hc : d.HasProtectedCenter) (hN : d.cornerIncidenceCount = 7) :
    ∃! i, d.tileCornerCount i = 1 := by
  obtain ⟨i, hi, hother⟩ := exists_one_corner_tile d hc hN
  refine ⟨i, hi, ?_⟩
  intro j hj
  by_contra hji
  have := hother j hji
  omega

private theorem card_filter_comp (σ : Equiv.Perm (Fin 4))
    (f : Fin 4 → ℕ) (n : ℕ) :
    (Finset.univ.filter fun i => f (σ i) = n).card =
      (Finset.univ.filter fun i => f i = n).card := by
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  exact Equiv.sum_comp σ (fun i => if f i = n then 1 else 0)

/-- The degree-one and degree-two classes contain one and three actual pieces. -/
theorem tile_count_cards (d : SquareDissection)
    (hc : d.HasProtectedCenter) (hN : d.cornerIncidenceCount = 7) :
    (Finset.univ.filter fun i => d.tileCornerCount i = 1).card = 1 ∧
      (Finset.univ.filter fun i => d.tileCornerCount i = 2).card = 3 := by
  classical
  obtain ⟨σ, h0, h1, h2, h3⟩ := tile_count_pattern d hc hN
  constructor
  · rw [← card_filter_comp σ d.tileCornerCount 1]
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter,
      CornerCounting.sum_fin_four, h0, h1, h2, h3]
    norm_num
  · rw [← card_filter_comp σ d.tileCornerCount 2]
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter,
      CornerCounting.sum_fin_four, h0, h1, h2, h3]
    norm_num

/-- The actual corner multiplicities, in decreasing order, are `2221` or
`3211`.  The geometric exclusion of four owners rules out `4111`. -/
theorem corner_count_patterns (d : SquareDissection)
    (hc : d.HasProtectedCenter) (hN : d.cornerIncidenceCount = 7) :
    ∃ σ : Equiv.Perm (Fin 4),
      (d.cornerTileCount (σ 0) = 2 ∧ d.cornerTileCount (σ 1) = 2 ∧
        d.cornerTileCount (σ 2) = 2 ∧ d.cornerTileCount (σ 3) = 1) ∨
      (d.cornerTileCount (σ 0) = 3 ∧ d.cornerTileCount (σ 1) = 2 ∧
        d.cornerTileCount (σ 2) = 1 ∧ d.cornerTileCount (σ 3) = 1) := by
  let f : Fin 4 → ℕᵒᵈ := fun i => d.cornerTileCount i
  let σ : Equiv.Perm (Fin 4) := Tuple.sort f
  have hmono := Tuple.monotone_sort f
  have hsorted : CornerCounting.SortedFour
      (d.cornerTileCount (σ 0)) (d.cornerTileCount (σ 1))
      (d.cornerTileCount (σ 2)) (d.cornerTileCount (σ 3)) :=
    ⟨hmono (by decide : (0 : Fin 4) ≤ 1),
      hmono (by decide : (1 : Fin 4) ≤ 2),
      hmono (by decide : (2 : Fin 4) ≤ 3)⟩
  have hsum : (∑ i, d.cornerTileCount (σ i)) = 7 := by
    rw [Equiv.sum_comp σ]
    exact d.cornerIncidenceCount_eq_sum_cornerTileCount.symm.trans hN
  rw [CornerCounting.sum_fin_four] at hsum
  have hmin : 1 ≤ d.cornerTileCount (σ 3) := d.cornerTileCount_pos (σ 3)
  have hmax := d.cornerTileCount_le_three hc (σ 0)
  rcases CornerCounting.corner_multiplicities_sum_seven hsorted hmin hsum with h | h | h
  · omega
  · exact ⟨σ, Or.inr h⟩
  · exact ⟨σ, Or.inl h⟩

/-- The numbers of corners with one, two, and three owners are respectively
`(1, 3, 0)` or `(2, 1, 1)`. -/
theorem corner_count_card_patterns (d : SquareDissection)
    (hc : d.HasProtectedCenter) (hN : d.cornerIncidenceCount = 7) :
    ((Finset.univ.filter fun j => d.cornerTileCount j = 1).card = 1 ∧
      (Finset.univ.filter fun j => d.cornerTileCount j = 2).card = 3 ∧
      (Finset.univ.filter fun j => d.cornerTileCount j = 3).card = 0) ∨
    ((Finset.univ.filter fun j => d.cornerTileCount j = 1).card = 2 ∧
      (Finset.univ.filter fun j => d.cornerTileCount j = 2).card = 1 ∧
      (Finset.univ.filter fun j => d.cornerTileCount j = 3).card = 1) := by
  classical
  obtain ⟨σ, h | h⟩ := corner_count_patterns d hc hN
  · left
    obtain ⟨h0, h1, h2, h3⟩ := h
    rw [← card_filter_comp σ d.cornerTileCount 1,
      ← card_filter_comp σ d.cornerTileCount 2,
      ← card_filter_comp σ d.cornerTileCount 3]
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter,
      CornerCounting.sum_fin_four, h0, h1, h2, h3]
    norm_num
  · right
    obtain ⟨h0, h1, h2, h3⟩ := h
    rw [← card_filter_comp σ d.cornerTileCount 1,
      ← card_filter_comp σ d.cornerTileCount 2,
      ← card_filter_comp σ d.cornerTileCount 3]
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter,
      CornerCounting.sum_fin_four, h0, h1, h2, h3]
    norm_num

/-- At least one corner has multiplicity one in either pattern. -/
theorem exists_count_one_corner (d : SquareDissection)
    (hc : d.HasProtectedCenter) (hN : d.cornerIncidenceCount = 7) :
    ∃ j : Fin 4, d.cornerTileCount j = 1 := by
  obtain ⟨σ, h | h⟩ := corner_count_patterns d hc hN
  · exact ⟨σ 3, h.2.2.2⟩
  · exact ⟨σ 3, h.2.2.2⟩

/-- At least one actual square corner has a unique owner in either pattern. -/
theorem exists_corner_unique_owner (d : SquareDissection)
    (hc : d.HasProtectedCenter) (hN : d.cornerIncidenceCount = 7) :
    ∃ j : Fin 4, ∃! i, corner j ∈ d.piece i := by
  obtain ⟨j, hj⟩ := exists_count_one_corner d hc hN
  exact ⟨j, d.existsUnique_corner_owner_of_count_one j hj⟩

end N7
end Puzzling139335
