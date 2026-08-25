import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Fin
import Lean.Elab.Tactic.Omega

/-!
# Counting incidences between four tiles and four corners

This file contains only finite combinatorics.  The geometric development can
instantiate `Incidence` with membership of a square corner in a tile.

The pattern lemmas list entries in decreasing order.  They do not assume that
tiles are connected, or that any particular geometric incidence is possible.
-/

namespace Puzzling139335.CornerCounting

open scoped BigOperators

/-- An incidence relation between four tile indices and four corner indices. -/
abbrev Incidence := Fin 4 → Fin 4 → Prop

/-- The number of corners incident with a tile. -/
def tileDegree (I : Incidence) [DecidableRel I] (i : Fin 4) : ℕ :=
  (Finset.univ.filter (I i)).card

/-- The number of tiles incident with a corner. -/
def cornerMultiplicity (I : Incidence) [DecidableRel I] (j : Fin 4) : ℕ :=
  (Finset.univ.filter fun i => I i j).card

/-- The total number of tile-corner incidences. -/
def totalIncidences (I : Incidence) [DecidableRel I] : ℕ :=
  ∑ i, tileDegree I i

/-- Counting by tiles or by corners gives the same total. -/
theorem incidence_double_count (I : Incidence) [DecidableRel I] :
    (∑ i, tileDegree I i) = ∑ j, cornerMultiplicity I j := by
  simp only [tileDegree, cornerMultiplicity, Finset.card_eq_sum_ones, Finset.sum_filter]
  exact Finset.sum_comm

theorem totalIncidences_eq_sum_cornerMultiplicity (I : Incidence) [DecidableRel I] :
    totalIncidences I = ∑ j, cornerMultiplicity I j :=
  incidence_double_count I

theorem tileDegree_le_four (I : Incidence) [DecidableRel I] (i : Fin 4) :
    tileDegree I i ≤ 4 := by
  simpa [tileDegree] using Finset.card_filter_le (Finset.univ : Finset (Fin 4)) (I i)

theorem cornerMultiplicity_le_four (I : Incidence) [DecidableRel I] (j : Fin 4) :
    cornerMultiplicity I j ≤ 4 := by
  simpa [cornerMultiplicity] using
    Finset.card_filter_le (Finset.univ : Finset (Fin 4)) (fun i => I i j)

/-- A corner incident with some tile has positive multiplicity. -/
theorem cornerMultiplicity_pos (I : Incidence) [DecidableRel I] (j : Fin 4)
    (hj : ∃ i, I i j) : 0 < cornerMultiplicity I j := by
  obtain ⟨i, hi⟩ := hj
  exact Finset.card_pos.mpr ⟨i, by simpa using hi⟩

/-- Four degrees bounded by two, and four positive multiplicities with the same
total, force that total to lie between four and eight. -/
theorem incidence_sum_bounds {tileDegrees cornerDegrees : Fin 4 → ℕ} {N : ℕ}
    (hTile : ∀ i, tileDegrees i ≤ 2)
    (hCorner : ∀ j, 1 ≤ cornerDegrees j)
    (hTileSum : (∑ i, tileDegrees i) = N)
    (hCornerSum : (∑ j, cornerDegrees j) = N) : 4 ≤ N ∧ N ≤ 8 := by
  constructor
  · calc
      4 = ∑ _j : Fin 4, (1 : ℕ) := by simp
      _ ≤ ∑ j, cornerDegrees j := Finset.sum_le_sum fun j _ => hCorner j
      _ = N := hCornerSum
  · calc
      N = ∑ i, tileDegrees i := hTileSum.symm
      _ ≤ ∑ _i : Fin 4, (2 : ℕ) := Finset.sum_le_sum fun i _ => hTile i
      _ = 8 := by simp

theorem totalIncidences_bounds (I : Incidence) [DecidableRel I]
    (hTile : ∀ i, tileDegree I i ≤ 2)
    (hCorner : ∀ j, 1 ≤ cornerMultiplicity I j) :
    4 ≤ totalIncidences I ∧ totalIncidences I ≤ 8 :=
  incidence_sum_bounds hTile hCorner rfl (incidence_double_count I).symm

/-- The incidence bound when coverage is stated directly as an existence
condition for each corner. -/
theorem totalIncidences_bounds_of_cover (I : Incidence) [DecidableRel I]
    (hTile : ∀ i, tileDegree I i ≤ 2)
    (hCover : ∀ j, ∃ i, I i j) :
    4 ≤ totalIncidences I ∧ totalIncidences I ≤ 8 := by
  apply totalIncidences_bounds I hTile
  intro j
  exact cornerMultiplicity_pos I j (hCover j)

/-- Four natural numbers, listed in decreasing order. -/
def SortedFour (a b c d : ℕ) : Prop := b ≤ a ∧ c ≤ b ∧ d ≤ c

/-- Expanding a sum indexed by four elements. -/
theorem sum_fin_four (f : Fin 4 → ℕ) :
    (∑ i, f i) = f 0 + f 1 + f 2 + f 3 := by
  simp [Fin.sum_univ_succ, Nat.add_assoc]

/-- With four incidences, the tile degrees are `1111`, `2110`, or `2200`. -/
theorem tile_degrees_sum_four {a b c d : ℕ} (hSorted : SortedFour a b c d)
    (hMax : a ≤ 2) (hSum : a + b + c + d = 4) :
    (a = 1 ∧ b = 1 ∧ c = 1 ∧ d = 1) ∨
      (a = 2 ∧ b = 1 ∧ c = 1 ∧ d = 0) ∨
      (a = 2 ∧ b = 2 ∧ c = 0 ∧ d = 0) := by
  obtain ⟨hab, hbc, hcd⟩ := hSorted
  omega

/-- With five incidences, the tile degrees are `2111` or `2210`. -/
theorem tile_degrees_sum_five {a b c d : ℕ} (hSorted : SortedFour a b c d)
    (hMax : a ≤ 2) (hSum : a + b + c + d = 5) :
    (a = 2 ∧ b = 1 ∧ c = 1 ∧ d = 1) ∨
      (a = 2 ∧ b = 2 ∧ c = 1 ∧ d = 0) := by
  obtain ⟨hab, hbc, hcd⟩ := hSorted
  omega

/-- With six incidences, the tile degrees are `2211` or `2220`. -/
theorem tile_degrees_sum_six {a b c d : ℕ} (hSorted : SortedFour a b c d)
    (hMax : a ≤ 2) (hSum : a + b + c + d = 6) :
    (a = 2 ∧ b = 2 ∧ c = 1 ∧ d = 1) ∨
      (a = 2 ∧ b = 2 ∧ c = 2 ∧ d = 0) := by
  obtain ⟨hab, hbc, hcd⟩ := hSorted
  omega

/-- With seven incidences, the tile degrees are `2221`. -/
theorem tile_degrees_sum_seven {a b c d : ℕ} (hSorted : SortedFour a b c d)
    (hMax : a ≤ 2) (hSum : a + b + c + d = 7) :
    a = 2 ∧ b = 2 ∧ c = 2 ∧ d = 1 := by
  obtain ⟨hab, hbc, hcd⟩ := hSorted
  omega

/-- With eight incidences, all four tile degrees equal two. -/
theorem tile_degrees_sum_eight {a b c d : ℕ} (hSorted : SortedFour a b c d)
    (hMax : a ≤ 2) (hSum : a + b + c + d = 8) :
    a = 2 ∧ b = 2 ∧ c = 2 ∧ d = 2 := by
  obtain ⟨hab, hbc, hcd⟩ := hSorted
  omega

/-- Four positive corner multiplicities with total four all equal one. -/
theorem corner_multiplicities_sum_four {a b c d : ℕ}
    (hSorted : SortedFour a b c d) (hMin : 1 ≤ d) (hSum : a + b + c + d = 4) :
    a = 1 ∧ b = 1 ∧ c = 1 ∧ d = 1 := by
  obtain ⟨hab, hbc, hcd⟩ := hSorted
  omega

/-- With five incidences, the positive corner multiplicities are `2111`. -/
theorem corner_multiplicities_sum_five {a b c d : ℕ}
    (hSorted : SortedFour a b c d) (hMin : 1 ≤ d) (hSum : a + b + c + d = 5) :
    a = 2 ∧ b = 1 ∧ c = 1 ∧ d = 1 := by
  obtain ⟨hab, hbc, hcd⟩ := hSorted
  omega

/-- With six incidences, the positive corner multiplicities are `3111` or `2211`. -/
theorem corner_multiplicities_sum_six {a b c d : ℕ}
    (hSorted : SortedFour a b c d) (hMin : 1 ≤ d) (hSum : a + b + c + d = 6) :
    (a = 3 ∧ b = 1 ∧ c = 1 ∧ d = 1) ∨
      (a = 2 ∧ b = 2 ∧ c = 1 ∧ d = 1) := by
  obtain ⟨hab, hbc, hcd⟩ := hSorted
  omega

/-- With seven incidences, the positive corner multiplicities are `4111`,
`3211`, or `2221`. -/
theorem corner_multiplicities_sum_seven {a b c d : ℕ}
    (hSorted : SortedFour a b c d) (hMin : 1 ≤ d) (hSum : a + b + c + d = 7) :
    (a = 4 ∧ b = 1 ∧ c = 1 ∧ d = 1) ∨
      (a = 3 ∧ b = 2 ∧ c = 1 ∧ d = 1) ∨
      (a = 2 ∧ b = 2 ∧ c = 2 ∧ d = 1) := by
  obtain ⟨hab, hbc, hcd⟩ := hSorted
  omega

/-- Among four cyclically indexed corners, a set with no opposite pair has
at most two elements.  Reduction modulo two injects it into two parity classes. -/
theorem card_le_two_of_no_opposite (s : Finset (Fin 4))
    (hOpposite : ∀ j, ¬ (j ∈ s ∧ j + 2 ∈ s)) : s.card ≤ 2 := by
  have hinj : Set.InjOn (fun j : Fin 4 => j.val % 2) s := by
    intro i hi j hj heq
    change i.val % 2 = j.val % 2 at heq
    by_contra hne
    have hvne : i.val ≠ j.val := fun h => hne (Fin.ext h)
    have hi4 := i.isLt
    have hj4 := j.isLt
    have hij : i + 2 = j := by
      apply Fin.ext
      change (i.val + 2) % 4 = j.val
      omega
    exact hOpposite i ⟨hi, hij.symm ▸ hj⟩
  calc
    s.card = (s.image fun j => j.val % 2).card :=
      (Finset.card_image_iff.mpr hinj).symm
    _ ≤ (Finset.range 2).card := Finset.card_le_card (by
      intro k hk
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hk
      exact Finset.mem_range.mpr (Nat.mod_lt _ (by omega)))
    _ = 2 := Finset.card_range 2

end Puzzling139335.CornerCounting
