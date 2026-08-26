import ErdosProblems.Erdos327.Analytic.SourceBoxAssembly

/-!
# Exact finite dyadic covers

Every positive natural coordinate belongs to the block indexed by its
base-two floor logarithm.  This file packages that elementary fact for
finite coordinate sets.
-/

namespace Erdos327.Analytic

open Finset

/-- The slice of `S` on which a positive natural coordinate lies in
`[2^j,2^(j+1))`. -/
def dyadicSlice {α : Type*} [DecidableEq α]
    (S : Finset α) (coord : α → ℕ) (j : ℕ) : Finset α :=
  S.filter fun x ↦
    2 ^ j ≤ coord x ∧ coord x < 2 * 2 ^ j

/-- A finite set whose selected coordinates lie in `[1,N]` is exactly the
union of its dyadic slices through `⌊log₂ N⌋`. -/
theorem biUnion_dyadicSlice_eq
    {α : Type*} [DecidableEq α]
    {S : Finset α} {coord : α → ℕ} {N : ℕ}
    (hpos : ∀ x ∈ S, 1 ≤ coord x)
    (hupper : ∀ x ∈ S, coord x ≤ N) :
    (range (Nat.log 2 N + 1)).biUnion
        (dyadicSlice S coord) = S := by
  ext x
  constructor
  · intro hx
    rcases mem_biUnion.mp hx with ⟨j, _hj, hxj⟩
    exact (mem_filter.mp hxj).1
  · intro hx
    let j := Nat.log 2 (coord x)
    have hcoord0 : coord x ≠ 0 :=
      Nat.one_le_iff_ne_zero.mp (hpos x hx)
    have hjle : j ≤ Nat.log 2 N :=
      Nat.log_mono_right (hupper x hx)
    have hlower : 2 ^ j ≤ coord x := by
      exact Nat.pow_log_le_self 2 hcoord0
    have hupperBlock : coord x < 2 * 2 ^ j := by
      have h :=
        Nat.lt_pow_succ_log_self Nat.one_lt_two (coord x)
      simpa [j, pow_succ, Nat.mul_comm] using h
    apply mem_biUnion.mpr
    exact ⟨j, mem_range.mpr (by omega),
      mem_filter.mpr ⟨hx, hlower, hupperBlock⟩⟩

/-- Cardinality is bounded by the sum of the dyadic slice cardinalities. -/
theorem card_le_sum_card_dyadicSlice
    {α : Type*} [DecidableEq α]
    {S : Finset α} {coord : α → ℕ} {N : ℕ}
    (hpos : ∀ x ∈ S, 1 ≤ coord x)
    (hupper : ∀ x ∈ S, coord x ≤ N) :
    S.card ≤
      ∑ j ∈ range (Nat.log 2 N + 1),
        (dyadicSlice S coord j).card := by
  calc
    S.card =
        ((range (Nat.log 2 N + 1)).biUnion
          (dyadicSlice S coord)).card := by
      rw [biUnion_dyadicSlice_eq hpos hupper]
    _ ≤ ∑ j ∈ range (Nat.log 2 N + 1),
          (dyadicSlice S coord j).card :=
      card_biUnion_le

/-- Real-cast form of the dyadic cardinality bound. -/
theorem card_real_le_sum_card_dyadicSlice
    {α : Type*} [DecidableEq α]
    {S : Finset α} {coord : α → ℕ} {N : ℕ}
    (hpos : ∀ x ∈ S, 1 ≤ coord x)
    (hupper : ∀ x ∈ S, coord x ≤ N) :
    (S.card : ℝ) ≤
      ∑ j ∈ range (Nat.log 2 N + 1),
        ((dyadicSlice S coord j).card : ℝ) := by
  exact_mod_cast card_le_sum_card_dyadicSlice hpos hupper

/-- The source-specific dyadic slice is the generic slice at scale `2^j`. -/
theorem dyadicSlice_sourceCoordinateSet_eq
    (L N : ℕ) (A K : ℝ) (j : ℕ) :
    dyadicSlice (sourceCoordinateSet L N A K) sourceU j =
      sourceDyadicCoordinateSet L N A K (2 ^ j) := by
  ext q
  simp [dyadicSlice, sourceDyadicCoordinateSet]

/-- The source coordinate set is bounded by the sum of the block
cardinalities used by `SourceBoxAssembly`. -/
theorem card_sourceCoordinateSet_le_sum_dyadic
    (L N : ℕ) (A K : ℝ) :
    ((sourceCoordinateSet L N A K).card : ℝ) ≤
      ∑ j ∈ range (Nat.log 2 N + 1),
        ((sourceDyadicCoordinateSet L N A K (2 ^ j)).card : ℝ) := by
  have hpos :
      ∀ q ∈ sourceCoordinateSet L N A K, 1 ≤ sourceU q := by
    intro q hq
    rw [sourceCoordinateSet, mem_filter] at hq
    exact (mem_Icc.mp (mem_product.mp (mem_product.mp hq.1).1).1).1
  have hupper :
      ∀ q ∈ sourceCoordinateSet L N A K, sourceU q ≤ N := by
    intro q hq
    rw [sourceCoordinateSet, mem_filter] at hq
    exact (mem_Icc.mp (mem_product.mp (mem_product.mp hq.1).1).1).2
  simpa only [dyadicSlice_sourceCoordinateSet_eq] using
    (card_real_le_sum_card_dyadicSlice hpos hupper)

end Erdos327.Analytic
