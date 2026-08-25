import StackExchange.Puzzling139335.Basic
import StackExchange.Puzzling139335.InitialReduction
import Mathlib.Data.Fin.Tuple.Sort

/-!
# Exhaustive routing of the four-incidence case

The decreasing order used to list the three degree patterns is obtained by
an actual permutation of the four pieces.  The final normalization also
labels the one-corner pieces by their actual corners; neither ordering is
an extra geometric assumption.
-/

open Set
open scoped BigOperators

namespace Puzzling139335

namespace SquareDissection

@[simp] theorem reindex_tileCornerCount (d : SquareDissection)
    (σ : Equiv.Perm (Fin 4)) (i : Fin 4) :
    (d.reindex σ).tileCornerCount i = d.tileCornerCount (σ i) := rfl

@[simp] theorem reindex_cornerTileCount (d : SquareDissection)
    (σ : Equiv.Perm (Fin 4)) (j : Fin 4) :
    (d.reindex σ).cornerTileCount j = d.cornerTileCount j := by
  classical
  change (Finset.univ.filter fun i => corner j ∈ d.piece (σ i)).card =
    (Finset.univ.filter fun i => corner j ∈ d.piece i).card
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  exact Equiv.sum_comp σ (fun i => if corner j ∈ d.piece i then 1 else 0)

@[simp] theorem reindex_cornerIncidenceCount (d : SquareDissection)
    (σ : Equiv.Perm (Fin 4)) :
    (d.reindex σ).cornerIncidenceCount = d.cornerIncidenceCount := by
  rw [(d.reindex σ).cornerIncidenceCount_eq_sum_tileCornerCount,
    d.cornerIncidenceCount_eq_sum_tileCornerCount]
  simp only [reindex_tileCornerCount, Equiv.sum_comp]

theorem cornerIncidenceCount_eq_four_of_each_tile_one (d : SquareDissection)
    (hdeg : ∀ i, d.tileCornerCount i = 1) : d.cornerIncidenceCount = 4 := by
  rw [d.cornerIncidenceCount_eq_sum_tileCornerCount]
  simp only [hdeg, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
    Nat.mul_one]

end SquareDissection

namespace N4Dispatch

/-- All four-incidence degree patterns, with the sorting permutation supplied. -/
theorem tile_pattern (d : SquareDissection) (hc : d.HasProtectedCenter)
    (hN : d.cornerIncidenceCount = 4) :
    ∃ σ : Equiv.Perm (Fin 4),
      (d.tileCornerCount (σ 0) = 1 ∧ d.tileCornerCount (σ 1) = 1 ∧
        d.tileCornerCount (σ 2) = 1 ∧ d.tileCornerCount (σ 3) = 1) ∨
      (d.tileCornerCount (σ 0) = 2 ∧ d.tileCornerCount (σ 1) = 1 ∧
        d.tileCornerCount (σ 2) = 1 ∧ d.tileCornerCount (σ 3) = 0) ∨
      (d.tileCornerCount (σ 0) = 2 ∧ d.tileCornerCount (σ 1) = 2 ∧
        d.tileCornerCount (σ 2) = 0 ∧ d.tileCornerCount (σ 3) = 0) := by
  let f : Fin 4 → ℕᵒᵈ := fun i => d.tileCornerCount i
  let σ := Tuple.sort f
  have hsort := Tuple.monotone_sort f
  have h10 : d.tileCornerCount (σ 1) ≤ d.tileCornerCount (σ 0) :=
    hsort (by decide : (0 : Fin 4) ≤ 1)
  have h21 : d.tileCornerCount (σ 2) ≤ d.tileCornerCount (σ 1) :=
    hsort (by decide : (1 : Fin 4) ≤ 2)
  have h32 : d.tileCornerCount (σ 3) ≤ d.tileCornerCount (σ 2) :=
    hsort (by decide : (2 : Fin 4) ≤ 3)
  have hsum : (∑ j, d.tileCornerCount (σ j)) = 4 := by
    rw [Equiv.sum_comp σ, ← d.cornerIncidenceCount_eq_sum_tileCornerCount, hN]
  rw [CornerCounting.sum_fin_four] at hsum
  exact ⟨σ, CornerCounting.tile_degrees_sum_four ⟨h10, h21, h32⟩
    (d.tileCornerCount_le_two hc (σ 0)) hsum⟩

/-- An exhaustive branch statement which does not require sorting in the
one-corner branch. -/
theorem corner_pattern_cases (d : SquareDissection) (hc : d.HasProtectedCenter)
    (hN : d.cornerIncidenceCount = 4) :
    (∀ i, d.tileCornerCount i = 1) ∨
      (∃ σ : Equiv.Perm (Fin 4),
        d.tileCornerCount (σ 0) = 2 ∧ d.tileCornerCount (σ 1) = 1 ∧
          d.tileCornerCount (σ 2) = 1 ∧ d.tileCornerCount (σ 3) = 0) ∨
      (∃ σ : Equiv.Perm (Fin 4),
        d.tileCornerCount (σ 0) = 2 ∧ d.tileCornerCount (σ 1) = 2 ∧
          d.tileCornerCount (σ 2) = 0 ∧ d.tileCornerCount (σ 3) = 0) := by
  obtain ⟨σ, h | h | h⟩ := tile_pattern d hc hN
  · left
    intro i
    obtain ⟨j, rfl⟩ := σ.surjective i
    fin_cases j
    · exact h.1
    · exact h.2.1
    · exact h.2.2.1
    · exact h.2.2.2
  · exact Or.inr (Or.inl ⟨σ, h⟩)
  · exact Or.inr (Or.inr ⟨σ, h⟩)

/-- A dispatch interface which selects the two double-corner pieces directly
in the `2200` branch. -/
theorem corner_pattern_cases_selected (d : SquareDissection) (hc : d.HasProtectedCenter)
    (hN : d.cornerIncidenceCount = 4) :
    (∀ i, d.tileCornerCount i = 1) ∨
      (∃ σ : Equiv.Perm (Fin 4),
        d.tileCornerCount (σ 0) = 2 ∧ d.tileCornerCount (σ 1) = 1 ∧
          d.tileCornerCount (σ 2) = 1 ∧ d.tileCornerCount (σ 3) = 0) ∨
      (∃ i j : Fin 4, i ≠ j ∧ d.tileCornerCount i = 2 ∧ d.tileCornerCount j = 2) := by
  rcases corner_pattern_cases d hc hN with h | h | ⟨σ, h⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr ⟨σ 0, σ 1, σ.injective.ne (by decide), h.1, h.2.1⟩)

/-- When each piece has one corner, an actual permutation labels each piece
by that corner. The incidence count need not be supplied separately. -/
theorem one_corner_normalization (d : SquareDissection)
    (hdeg : ∀ i, d.tileCornerCount i = 1) :
    ∃ σ : Equiv.Perm (Fin 4),
      ∀ j i, corner j ∈ (d.reindex σ).piece i ↔ j = i := by
  classical
  have hsingle (i : Fin 4) {j k : Fin 4}
      (hj : corner j ∈ d.piece i) (hk : corner k ∈ d.piece i) : j = k := by
    have hcard := hdeg i
    change (Finset.univ.filter fun a => corner a ∈ d.piece i).card = 1 at hcard
    exact Finset.card_le_one_iff.mp hcard.le (by simp [hj]) (by simp [hk])
  choose owner howner using d.incidence_covers
  have hinj : Function.Injective owner := by
    intro j k hjk
    exact hsingle (owner k) (hjk ▸ howner j) (howner k)
  let σ : Equiv.Perm (Fin 4) := Equiv.ofBijective owner
    ⟨hinj, Finite.surjective_of_injective hinj⟩
  refine ⟨σ, ?_⟩
  intro j i
  constructor
  · intro hj
    exact hsingle (owner i) hj (howner i)
  · intro hji
    subst j
    exact howner i

/-- The one-corner normalization preserves the protected-center assumption. -/
theorem one_corner_normalization_protected (d : SquareDissection)
    (hc : d.HasProtectedCenter) (hdeg : ∀ i, d.tileCornerCount i = 1) :
    ∃ σ : Equiv.Perm (Fin 4),
      (d.reindex σ).HasProtectedCenter ∧
        ∀ j i, corner j ∈ (d.reindex σ).piece i ↔ j = i := by
  obtain ⟨σ, hσ⟩ := one_corner_normalization d hdeg
  exact ⟨σ, (d.reindex_hasProtectedCenter σ).mpr hc, hσ⟩

end N4Dispatch
end Puzzling139335
