import StackExchange.Puzzling139335.InitialReduction
import StackExchange.Puzzling139335.N5.Incidence

/-!
# The two actual six-incidence corner patterns

The corner multiplicities are either `3111` or `2211`; the piece degrees
are either `2211` or `2220`. These statements are obtained from the actual
corner memberships, before any angle or boundary-germ analysis.
-/

open Set
open scoped BigOperators

namespace Puzzling139335.N6

/-- One square corner has three owners; all the other corners are unique. -/
def HasTripleCorner (d : SquareDissection) : Prop :=
  ∃ s : Fin 4, d.cornerTileCount s = 3 ∧
    ∀ j, j ≠ s → d.cornerTileCount j = 1

/-- Two square corners have two owners, and the other two are unique. -/
def HasTwoDoubleCorners (d : SquareDissection) : Prop :=
  ∃ s t : Fin 4, s ≠ t ∧ d.cornerTileCount s = 2 ∧
    d.cornerTileCount t = 2 ∧
      ∀ j, j ≠ s → j ≠ t → d.cornerTileCount j = 1

/-- A sorted permutation of the actual corner multiplicities. -/
theorem corner_pattern (d : SquareDissection) (hN : d.cornerIncidenceCount = 6) :
    ∃ σ : Equiv.Perm (Fin 4),
      (d.cornerTileCount (σ 0) = 1 ∧ d.cornerTileCount (σ 1) = 1 ∧
        d.cornerTileCount (σ 2) = 1 ∧ d.cornerTileCount (σ 3) = 3) ∨
      (d.cornerTileCount (σ 0) = 1 ∧ d.cornerTileCount (σ 1) = 1 ∧
        d.cornerTileCount (σ 2) = 2 ∧ d.cornerTileCount (σ 3) = 2) := by
  let σ := Tuple.sort d.cornerTileCount
  have hsort := Tuple.monotone_sort d.cornerTileCount
  have h01 : d.cornerTileCount (σ 0) ≤ d.cornerTileCount (σ 1) :=
    hsort (by decide : (0 : Fin 4) ≤ 1)
  have h12 : d.cornerTileCount (σ 1) ≤ d.cornerTileCount (σ 2) :=
    hsort (by decide : (1 : Fin 4) ≤ 2)
  have h23 : d.cornerTileCount (σ 2) ≤ d.cornerTileCount (σ 3) :=
    hsort (by decide : (2 : Fin 4) ≤ 3)
  have hsum : (∑ j, d.cornerTileCount (σ j)) = 6 := by
    rw [Equiv.sum_comp σ, ← d.cornerIncidenceCount_eq_sum_cornerTileCount, hN]
  rw [CornerCounting.sum_fin_four] at hsum
  have hpos := d.cornerTileCount_pos (σ 0)
  refine ⟨σ, ?_⟩
  omega

/-- Exactly six incidences give precisely the two multiplicity branches. -/
theorem corner_cases (d : SquareDissection) (hN : d.cornerIncidenceCount = 6) :
    HasTripleCorner d ∨ HasTwoDoubleCorners d := by
  obtain ⟨σ, h | h⟩ := corner_pattern d hN
  · left
    refine ⟨σ 3, h.2.2.2, ?_⟩
    intro j hj
    obtain ⟨k, rfl⟩ := σ.surjective j
    fin_cases k
    · exact h.1
    · exact h.2.1
    · exact h.2.2.1
    · exact (hj rfl).elim
  · right
    refine ⟨σ 2, σ 3, σ.injective.ne (by decide), h.2.2.1, h.2.2.2, ?_⟩
    intro j hj2 hj3
    obtain ⟨k, rfl⟩ := σ.surjective j
    fin_cases k
    · exact h.1
    · exact h.2.1
    · exact (hj2 rfl).elim
    · exact (hj3 rfl).elim

/-- Sorted piece degrees, using the protected-center diameter exclusion. -/
theorem tile_pattern (d : SquareDissection) (hc : d.HasProtectedCenter)
    (hN : d.cornerIncidenceCount = 6) :
    ∃ σ : Equiv.Perm (Fin 4),
      (d.tileCornerCount (σ 0) = 1 ∧ d.tileCornerCount (σ 1) = 1 ∧
        d.tileCornerCount (σ 2) = 2 ∧ d.tileCornerCount (σ 3) = 2) ∨
      (d.tileCornerCount (σ 0) = 0 ∧ d.tileCornerCount (σ 1) = 2 ∧
        d.tileCornerCount (σ 2) = 2 ∧ d.tileCornerCount (σ 3) = 2) := by
  let σ := Tuple.sort d.tileCornerCount
  have hsort := Tuple.monotone_sort d.tileCornerCount
  have h01 : d.tileCornerCount (σ 0) ≤ d.tileCornerCount (σ 1) :=
    hsort (by decide : (0 : Fin 4) ≤ 1)
  have h12 : d.tileCornerCount (σ 1) ≤ d.tileCornerCount (σ 2) :=
    hsort (by decide : (1 : Fin 4) ≤ 2)
  have h23 : d.tileCornerCount (σ 2) ≤ d.tileCornerCount (σ 3) :=
    hsort (by decide : (2 : Fin 4) ≤ 3)
  have hsum : (∑ j, d.tileCornerCount (σ j)) = 6 := by
    rw [Equiv.sum_comp σ, ← d.cornerIncidenceCount_eq_sum_tileCornerCount, hN]
  rw [CornerCounting.sum_fin_four] at hsum
  have hmax := d.tileCornerCount_le_two hc (σ 3)
  refine ⟨σ, ?_⟩
  omega

/-- A triple corner has three distinct actual owners and no fourth owner. -/
theorem triple_corner_owners (d : SquareDissection) (s : Fin 4)
    (hs : d.cornerTileCount s = 3) :
    ∃ i j k : Fin 4, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
      ∀ l, corner s ∈ d.piece l ↔ l = i ∨ l = j ∨ l = k := by
  classical
  change (Finset.univ.filter fun i => corner s ∈ d.piece i).card = 3 at hs
  obtain ⟨i, j, k, hij, hik, hjk, hset⟩ := Finset.card_eq_three.mp hs
  refine ⟨i, j, k, hij, hik, hjk, ?_⟩
  intro l
  have hl := Finset.ext_iff.mp hset l
  simpa only [Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_insert, Finset.mem_singleton] using hl

/-- A particular corner of multiplicity three is the only split corner. -/
theorem unique_away_from_triple (d : SquareDissection)
    (hN : d.cornerIncidenceCount = 6) {s j : Fin 4}
    (hs : d.cornerTileCount s = 3) (hjs : j ≠ s) : d.cornerTileCount j = 1 := by
  rcases corner_cases d hN with ⟨t, ht, hother⟩ | ⟨t, u, _, ht, hu, hother⟩
  · have hst : s = t := by
      by_contra hne
      have := hother s hne
      omega
    exact hother j (by simpa only [← hst] using hjs)
  · by_cases hst : s = t
    · subst s
      omega
    by_cases hsu : s = u
    · subst s
      omega
    have := hother s hst hsu
    omega

end Puzzling139335.N6
