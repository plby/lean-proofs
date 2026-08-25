import StackExchange.Puzzling139335.InitialReduction
import Mathlib.Data.Fin.Tuple.Sort

/-!
# The incidence patterns when the total is five

These statements concern actual memberships of the four square corners in
the four pieces.  They impose no assumptions on corner angles.
-/

open Set
open scoped BigOperators

namespace Puzzling139335.N5

/-- With five incidences, one corner has two owners and every other corner
has exactly one owner. -/
theorem exists_split_corner (d : SquareDissection)
    (hN : d.cornerIncidenceCount = 5) :
    ∃ s : Fin 4, d.cornerTileCount s = 2 ∧
      ∀ j, j ≠ s → d.cornerTileCount j = 1 := by
  have hsum : (∑ j, d.cornerTileCount j) = 5 :=
    d.cornerIncidenceCount_eq_sum_cornerTileCount.symm.trans hN
  rw [CornerCounting.sum_fin_four] at hsum
  have h0 := d.cornerTileCount_pos 0
  have h1 := d.cornerTileCount_pos 1
  have h2 := d.cornerTileCount_pos 2
  have h3 := d.cornerTileCount_pos 3
  have hcases :
      (d.cornerTileCount 0 = 2 ∧ d.cornerTileCount 1 = 1 ∧
        d.cornerTileCount 2 = 1 ∧ d.cornerTileCount 3 = 1) ∨
      (d.cornerTileCount 0 = 1 ∧ d.cornerTileCount 1 = 2 ∧
        d.cornerTileCount 2 = 1 ∧ d.cornerTileCount 3 = 1) ∨
      (d.cornerTileCount 0 = 1 ∧ d.cornerTileCount 1 = 1 ∧
        d.cornerTileCount 2 = 2 ∧ d.cornerTileCount 3 = 1) ∨
      (d.cornerTileCount 0 = 1 ∧ d.cornerTileCount 1 = 1 ∧
        d.cornerTileCount 2 = 1 ∧ d.cornerTileCount 3 = 2) := by omega
  rcases hcases with h | h | h | h
  · refine ⟨0, h.1, ?_⟩
    intro j hj
    fin_cases j <;> simp_all
  · refine ⟨1, h.2.1, ?_⟩
    intro j hj
    fin_cases j <;> simp_all
  · refine ⟨2, h.2.2.1, ?_⟩
    intro j hj
    fin_cases j <;> simp_all
  · refine ⟨3, h.2.2.2, ?_⟩
    intro j hj
    fin_cases j <;> simp_all

/-- A corner of multiplicity one has a unique actual owner. -/
theorem unique_owner_of_count_one (d : SquareDissection) (j : Fin 4)
    (hj : d.cornerTileCount j = 1) : ∃! i, corner j ∈ d.piece i := by
  classical
  change (Finset.univ.filter fun i => corner j ∈ d.piece i).card = 1 at hj
  simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using
    Finset.card_eq_one_iff_existsUnique.mp hj

/-- The two owners of a corner of multiplicity two are distinct, and no
other piece contains that corner. -/
theorem split_corner_owners (d : SquareDissection) (s : Fin 4)
    (hs : d.cornerTileCount s = 2) :
    ∃ i j : Fin 4, i ≠ j ∧
      ∀ k, corner s ∈ d.piece k ↔ k = i ∨ k = j := by
  classical
  change (Finset.univ.filter fun i => corner s ∈ d.piece i).card = 2 at hs
  obtain ⟨i, j, hij, hset⟩ := Finset.card_eq_two.mp hs
  refine ⟨i, j, hij, ?_⟩
  intro k
  have hk := Finset.ext_iff.mp hset k
  simpa only [Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_insert, Finset.mem_singleton] using hk

theorem count_one_of_ne_split (d : SquareDissection)
    (hN : d.cornerIncidenceCount = 5) {s j : Fin 4}
    (hs : d.cornerTileCount s = 2) (hjs : j ≠ s) :
    d.cornerTileCount j = 1 := by
  obtain ⟨t, ht, hother⟩ := exists_split_corner d hN
  have hst : s = t := by
    by_contra hne
    have := hother s hne
    omega
  exact hother j (by simpa [← hst] using hjs)

theorem unique_owner_away_from_split (d : SquareDissection)
    (hN : d.cornerIncidenceCount = 5) {s j : Fin 4}
    (hs : d.cornerTileCount s = 2) (hjs : j ≠ s) :
    ∃! i, corner j ∈ d.piece i :=
  unique_owner_of_count_one d j (count_one_of_ne_split d hN hs hjs)

/-- Up to a permutation of the four actual tiles, their corner counts are
`2111` or `2210`.  The bound of two comes from the protected center. -/
theorem tile_count_patterns (d : SquareDissection)
    (hc : d.HasProtectedCenter) (hN : d.cornerIncidenceCount = 5) :
    ∃ σ : Equiv.Perm (Fin 4),
      (d.tileCornerCount (σ 0) = 2 ∧ d.tileCornerCount (σ 1) = 1 ∧
        d.tileCornerCount (σ 2) = 1 ∧ d.tileCornerCount (σ 3) = 1) ∨
      (d.tileCornerCount (σ 0) = 2 ∧ d.tileCornerCount (σ 1) = 2 ∧
        d.tileCornerCount (σ 2) = 1 ∧ d.tileCornerCount (σ 3) = 0) := by
  let f : Fin 4 → ℕᵒᵈ := fun i => d.tileCornerCount i
  let σ : Equiv.Perm (Fin 4) := Tuple.sort f
  have hmono := Tuple.monotone_sort f
  have hsorted : CornerCounting.SortedFour
      (d.tileCornerCount (σ 0)) (d.tileCornerCount (σ 1))
      (d.tileCornerCount (σ 2)) (d.tileCornerCount (σ 3)) :=
    ⟨hmono (by decide : (0 : Fin 4) ≤ 1),
      hmono (by decide : (1 : Fin 4) ≤ 2),
      hmono (by decide : (2 : Fin 4) ≤ 3)⟩
  have hsum : (∑ i, d.tileCornerCount (σ i)) = 5 := by
    rw [Equiv.sum_comp σ]
    exact d.cornerIncidenceCount_eq_sum_tileCornerCount.symm.trans hN
  rw [CornerCounting.sum_fin_four] at hsum
  exact ⟨σ, CornerCounting.tile_degrees_sum_five hsorted
    (d.tileCornerCount_le_two hc (σ 0)) hsum⟩

end Puzzling139335.N5
