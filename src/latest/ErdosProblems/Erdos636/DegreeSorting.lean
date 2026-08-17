/-
Copyright 2026 The Lean-Proofs Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import Mathlib

/-!
# Deterministic degree sorting

This file isolates the elementary ordering argument used twice in the
Kwan--Sudakov proof.  From a finite population of integer coefficients it
selects equally large bottom and top blocks.  If every coefficient value has
multiplicity at most `Q`, then a large middle block forces a large gap between
every bottom coefficient and every top coefficient.

The statements are deliberately independent of graphs.  The final two
lemmas turn a pointwise gap into an integral sum discrepancy and into its
nonnegative real-weighted version.
-/

open Finset

namespace Erdos636.DegreeSorting

noncomputable section

attribute [local instance] Classical.propDecidable

universe u

variable {I : Type u} [DecidableEq I]

/-! ## Ordered bipartitions -/

/-- Any prescribed number of the lowest elements of a finite population can
be separated from the rest.  Ties may be put on either side. -/
theorem exists_ordered_bipartition
    (S : Finset I) (a : I → ℤ) (m : ℕ) (hm : m ≤ S.card) :
    ∃ lower upper : Finset I,
      Disjoint lower upper ∧
      lower ∪ upper = S ∧
      lower.card = m ∧
      ∀ x ∈ lower, ∀ y ∈ upper, a x ≤ a y := by
  induction m generalizing S with
  | zero =>
      exact ⟨∅, S, by simp⟩
  | succ m ih =>
      have hS : S.Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨x, hxS, hxmin⟩ := S.exists_min_image a hS
      have hmErase : m ≤ (S.erase x).card := by
        rw [Finset.card_erase_of_mem hxS]
        omega
      obtain ⟨lower, upper, hdisj, hunion, hcard, horder⟩ :=
        ih (S.erase x) hmErase
      have hlowerSub : lower ⊆ S.erase x := by
        rw [← hunion]
        exact Finset.subset_union_left
      have hupperSub : upper ⊆ S.erase x := by
        rw [← hunion]
        exact Finset.subset_union_right
      have hxLower : x ∉ lower := fun hx ↦ (Finset.mem_erase.mp (hlowerSub hx)).1 rfl
      have hxUpper : x ∉ upper := fun hx ↦ (Finset.mem_erase.mp (hupperSub hx)).1 rfl
      refine ⟨insert x lower, upper, ?_, ?_, ?_, ?_⟩
      · exact Finset.disjoint_insert_left.mpr ⟨hxUpper, hdisj⟩
      · rw [Finset.insert_union, hunion, Finset.insert_erase hxS]
      · rw [Finset.card_insert_of_notMem hxLower, hcard]
      · intro z hz y hy
        rw [Finset.mem_insert] at hz
        rcases hz with rfl | hz
        · exact hxmin y (Finset.mem_of_mem_erase (hupperSub hy))
        · exact horder z hz y hy

/-- The bottom, middle, and top blocks of an ordered finite population. -/
structure OrderedThreeWaySplit (S : Finset I) (a : I → ℤ) (m : ℕ) where
  low : Finset I
  middle : Finset I
  high : Finset I
  low_disjoint_rest : Disjoint low (middle ∪ high)
  middle_disjoint_high : Disjoint middle high
  union_eq : low ∪ middle ∪ high = S
  low_card : low.card = m
  high_card : high.card = m
  middle_card : middle.card = S.card - 2 * m
  low_le_middle : ∀ x ∈ low, ∀ y ∈ middle, a x ≤ a y
  middle_le_high : ∀ x ∈ middle, ∀ y ∈ high, a x ≤ a y

namespace OrderedThreeWaySplit

variable {S : Finset I} {a : I → ℤ} {m : ℕ}

lemma low_subset (D : OrderedThreeWaySplit S a m) : D.low ⊆ S := by
  intro x hx
  have hx' : x ∈ D.low ∪ D.middle ∪ D.high := by simp [hx]
  exact D.union_eq ▸ hx'

lemma middle_subset (D : OrderedThreeWaySplit S a m) : D.middle ⊆ S := by
  intro x hx
  have hx' : x ∈ D.low ∪ D.middle ∪ D.high := by simp [hx]
  exact D.union_eq ▸ hx'

lemma high_subset (D : OrderedThreeWaySplit S a m) : D.high ⊆ S := by
  intro x hx
  have hx' : x ∈ D.low ∪ D.middle ∪ D.high := by simp [hx]
  exact D.union_eq ▸ hx'

lemma low_le_high (D : OrderedThreeWaySplit S a m)
    (hmid : D.middle.Nonempty) :
    ∀ x ∈ D.low, ∀ y ∈ D.high, a x ≤ a y := by
  obtain ⟨z, hz⟩ := hmid
  intro x hx y hy
  exact (D.low_le_middle x hx z hz).trans (D.middle_le_high z hz y hy)

end OrderedThreeWaySplit

/-- Select the bottom `m` and top `m` elements of `S`, leaving all other
elements in the middle block. -/
theorem exists_orderedThreeWaySplit
    (S : Finset I) (a : I → ℤ) (m : ℕ) (hm : 2 * m ≤ S.card) :
    Nonempty (OrderedThreeWaySplit S a m) := by
  obtain ⟨low, rest, hlowRest, hlowUnion, hlowCard, hlowOrder⟩ :=
    exists_ordered_bipartition S a m (by omega)
  have hrestCard : rest.card = S.card - m := by
    have hcardUnion := Finset.card_union_of_disjoint hlowRest
    rw [hlowUnion, hlowCard] at hcardUnion
    omega
  have hmRest : m ≤ rest.card := by omega
  obtain ⟨high, middle, hhighMiddle, hhighUnion, hhighCard, hnegOrder⟩ :=
    exists_ordered_bipartition rest (fun x ↦ -a x) m hmRest
  have hmiddleCard : middle.card = S.card - 2 * m := by
    have hcardUnion := Finset.card_union_of_disjoint hhighMiddle
    rw [hhighUnion, hhighCard, hrestCard] at hcardUnion
    omega
  have hmiddleHigh : Disjoint middle high := hhighMiddle.symm
  have hrestEq : middle ∪ high = rest := by
    rw [Finset.union_comm, hhighUnion]
  refine ⟨{
    low := low
    middle := middle
    high := high
    low_disjoint_rest := ?_
    middle_disjoint_high := hmiddleHigh
    union_eq := ?_
    low_card := hlowCard
    high_card := hhighCard
    middle_card := hmiddleCard
    low_le_middle := ?_
    middle_le_high := ?_ }⟩
  · simpa [hrestEq] using hlowRest
  · calc
      low ∪ middle ∪ high = low ∪ (middle ∪ high) := Finset.union_assoc ..
      _ = low ∪ rest := by rw [hrestEq]
      _ = S := hlowUnion
  · intro x hx y hy
    apply hlowOrder x hx y
    rw [← hrestEq]
    exact Finset.mem_union_left _ hy
  · intro x hx y hy
    have hneg := hnegOrder y hy x hx
    omega

/-! ## A bounded fibre forces a gap -/

/-- The middle block fits into the integer interval between any chosen low
and high endpoint.  The fibre bound is measured in the original population
`S`, so it can be supplied directly by an application. -/
theorem middle_card_le_fiber_mul_interval
    {S : Finset I} {a : I → ℤ} {m Q : ℕ}
    (D : OrderedThreeWaySplit S a m)
    (hfiber : ∀ z : ℤ, (S.filter fun x ↦ a x = z).card ≤ Q)
    {x y : I} (hx : x ∈ D.low) (hy : y ∈ D.high) :
    D.middle.card ≤ Q * (a y + 1 - a x).toNat := by
  have hmiddleFiber : ∀ z ∈ D.middle.image a,
      (D.middle.filter fun i ↦ a i = z).card ≤ Q := by
    intro z hz
    calc
      (D.middle.filter fun i ↦ a i = z).card ≤
          (S.filter fun i ↦ a i = z).card := by
            apply Finset.card_le_card
            intro i hi
            rw [Finset.mem_filter] at hi ⊢
            exact ⟨D.middle_subset hi.1, hi.2⟩
      _ ≤ Q := hfiber z
  by_cases hmid : D.middle.Nonempty
  · have himage : D.middle.image a ⊆ Finset.Icc (a x) (a y) := by
      intro z hz
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
      exact Finset.mem_Icc.mpr
        ⟨D.low_le_middle x hx i hi, D.middle_le_high i hi y hy⟩
    calc
      D.middle.card ≤ Q * (D.middle.image a).card :=
        Finset.card_le_mul_card_image D.middle Q hmiddleFiber
      _ ≤ Q * (Finset.Icc (a x) (a y)).card :=
        Nat.mul_le_mul_left Q (Finset.card_le_card himage)
      _ = Q * (a y + 1 - a x).toNat := by rw [Int.card_Icc]
  · rw [Finset.not_nonempty_iff_eq_empty.mp hmid]
    exact Nat.zero_le _

/-- If the middle contains more than `Q * (g + 1)` elements, every high
coefficient exceeds every low coefficient by more than `g`. -/
theorem gap_lt_high_sub_low
    {S : Finset I} {a : I → ℤ} {m Q g : ℕ}
    (D : OrderedThreeWaySplit S a m)
    (hfiber : ∀ z : ℤ, (S.filter fun x ↦ a x = z).card ≤ Q)
    (hmiddle : Q * (g + 1) < D.middle.card)
    {x y : I} (hx : x ∈ D.low) (hy : y ∈ D.high) :
    (g : ℤ) < a y - a x := by
  have hcard := middle_card_le_fiber_mul_interval D hfiber hx hy
  by_contra hgap
  push Not at hgap
  have hnat : (a y + 1 - a x).toNat ≤ g + 1 := by
    rw [Int.toNat_le]
    omega
  have : D.middle.card ≤ Q * (g + 1) :=
    hcard.trans (Nat.mul_le_mul_left Q hnat)
  omega

/-- Direct selection-and-gap package.  The numerical hypothesis is phrased
using the exact size `|S| - 2m` of the middle block. -/
theorem exists_orderedThreeWaySplit_with_gap
    (S : Finset I) (a : I → ℤ) (m Q g : ℕ)
    (hsize : 2 * m ≤ S.card)
    (hfiber : ∀ z : ℤ, (S.filter fun x ↦ a x = z).card ≤ Q)
    (hmiddle : Q * (g + 1) < S.card - 2 * m) :
    ∃ D : OrderedThreeWaySplit S a m,
      ∀ x ∈ D.low, ∀ y ∈ D.high, (g : ℤ) < a y - a x := by
  let D := Classical.choice (exists_orderedThreeWaySplit S a m hsize)
  refine ⟨D, ?_⟩
  intro x hx y hy
  apply gap_lt_high_sub_low D hfiber
  · simpa [D.middle_card] using hmiddle
  · exact hx
  · exact hy

/-! ## Summed and weighted discrepancies -/

omit [DecidableEq I] in
/-- A uniform pointwise gap between equally large nonempty blocks sums to
the corresponding cardinality times the gap. -/
theorem card_mul_le_sum_sub_sum_of_pairwise_gap
    {a : I → ℤ} {low high : Finset I} {d : ℤ}
    (hlow : low.Nonempty) (hcard : low.card = high.card)
    (hgap : ∀ x ∈ low, ∀ y ∈ high, a x + d ≤ a y) :
    (low.card : ℤ) * d ≤
      (∑ y ∈ high, a y) - ∑ x ∈ low, a x := by
  obtain ⟨x, hx, hxmax⟩ := low.exists_max_image a hlow
  have hlowSum : (∑ z ∈ low, a z) ≤ (∑ _z ∈ low, (a x)) := by
    exact Finset.sum_le_sum fun z hz ↦ hxmax z hz
  have hhighSum : (∑ _z ∈ high, (a x + d)) ≤ (∑ z ∈ high, a z) := by
    exact Finset.sum_le_sum fun z hz ↦ hgap x hx z hz
  simp only [Finset.sum_const, nsmul_eq_mul] at hlowSum hhighSum
  rw [← hcard] at hhighSum
  calc
    (low.card : ℤ) * d =
        (low.card : ℤ) * (a x + d) - (low.card : ℤ) * a x := by ring
    _ ≤ (∑ y ∈ high, a y) - ∑ z ∈ low, a z :=
      sub_le_sub hhighSum hlowSum

omit [DecidableEq I] in
/-- Real-weighted form of `card_mul_le_sum_sub_sum_of_pairwise_gap`. -/
theorem weighted_card_mul_le_sum_sub_sum_of_pairwise_gap
    {a : I → ℤ} {low high : Finset I} {d : ℤ} {alpha : ℝ}
    (hlow : low.Nonempty) (hcard : low.card = high.card)
    (hgap : ∀ x ∈ low, ∀ y ∈ high, a x + d ≤ a y)
    (halpha : 0 ≤ alpha) :
    alpha * (low.card : ℝ) * (d : ℝ) ≤
      alpha * ((∑ y ∈ high, (a y : ℝ)) - ∑ x ∈ low, (a x : ℝ)) := by
  have hz := card_mul_le_sum_sub_sum_of_pairwise_gap hlow hcard hgap
  have hr : ((low.card : ℤ) * d : ℝ) ≤
      (((∑ y ∈ high, a y) - ∑ x ∈ low, a x : ℤ) : ℝ) := by
    exact_mod_cast hz
  have hweighted := mul_le_mul_of_nonneg_left hr halpha
  simpa only [Int.cast_mul, Int.cast_natCast, Int.cast_sub, Int.cast_sum,
    mul_assoc] using hweighted

/-- Combined selected-block discrepancy.  Integrality upgrades the strict
gap `g < high - low` to the non-strict gap `g + 1 ≤ high - low`. -/
theorem exists_orderedThreeWaySplit_with_sum_gap
    (S : Finset I) (a : I → ℤ) (m Q g : ℕ)
    (hm : 0 < m)
    (hsize : 2 * m ≤ S.card)
    (hfiber : ∀ z : ℤ, (S.filter fun x ↦ a x = z).card ≤ Q)
    (hmiddle : Q * (g + 1) < S.card - 2 * m) :
    ∃ D : OrderedThreeWaySplit S a m,
      ((m : ℕ) : ℤ) * ((g + 1 : ℕ) : ℤ) ≤
        (∑ y ∈ D.high, a y) - ∑ x ∈ D.low, a x := by
  obtain ⟨D, hgap⟩ :=
    exists_orderedThreeWaySplit_with_gap S a m Q g hsize hfiber hmiddle
  refine ⟨D, ?_⟩
  have hlow : D.low.Nonempty := Finset.card_pos.mp (by simpa [D.low_card] using hm)
  have hcard : D.low.card = D.high.card := D.low_card.trans D.high_card.symm
  have hpoint : ∀ x ∈ D.low, ∀ y ∈ D.high,
      a x + ((g + 1 : ℕ) : ℤ) ≤ a y := by
    intro x hx y hy
    have := hgap x hx y hy
    omega
  have hsum := card_mul_le_sum_sub_sum_of_pairwise_gap
    (a := a) (low := D.low) (high := D.high)
    (d := ((g + 1 : ℕ) : ℤ)) hlow hcard hpoint
  simpa [D.low_card] using hsum

/-- One-shot weighted discrepancy for the selected bottom and top blocks. -/
theorem exists_orderedThreeWaySplit_with_weighted_sum_gap
    (S : Finset I) (a : I → ℤ) (m Q g : ℕ) (alpha : ℝ)
    (hm : 0 < m)
    (hsize : 2 * m ≤ S.card)
    (hfiber : ∀ z : ℤ, (S.filter fun x ↦ a x = z).card ≤ Q)
    (hmiddle : Q * (g + 1) < S.card - 2 * m)
    (halpha : 0 ≤ alpha) :
    ∃ D : OrderedThreeWaySplit S a m,
      alpha * (m : ℝ) * (g + 1 : ℝ) ≤
        alpha * ((∑ y ∈ D.high, (a y : ℝ)) -
          ∑ x ∈ D.low, (a x : ℝ)) := by
  obtain ⟨D, hgap⟩ :=
    exists_orderedThreeWaySplit_with_gap S a m Q g hsize hfiber hmiddle
  refine ⟨D, ?_⟩
  have hlow : D.low.Nonempty := Finset.card_pos.mp (by simpa [D.low_card] using hm)
  have hcard : D.low.card = D.high.card := D.low_card.trans D.high_card.symm
  have hpoint : ∀ x ∈ D.low, ∀ y ∈ D.high,
      a x + ((g + 1 : ℕ) : ℤ) ≤ a y := by
    intro x hx y hy
    have := hgap x hx y hy
    omega
  have hweighted := weighted_card_mul_le_sum_sub_sum_of_pairwise_gap
    (a := a) (low := D.low) (high := D.high)
    (d := ((g + 1 : ℕ) : ℤ)) (alpha := alpha)
    hlow hcard hpoint halpha
  simpa [D.low_card] using hweighted

end

end Erdos636.DegreeSorting
