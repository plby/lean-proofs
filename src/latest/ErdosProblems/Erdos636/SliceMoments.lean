/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

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

import ErdosProblems.Erdos636.External.Erdos88.BooleanSlices
import ErdosProblems.Erdos636.External.Erdos88.Richness

/-!
# Exact moments of uniform fixed-cardinality subsets

This file supplies the elementary expectation identities used when the
Kwan--Sudakov argument samples a prescribed number of vertices from one or
more disjoint buckets.  They are proved by finite double counting.  Thus the
results apply directly to the finite uniform spaces in
`Erdos88.BooleanSlices`, without any appeal to independence inside a slice.
-/

open scoped BigOperators

namespace Erdos636
namespace SliceMoments

open Classical
open Erdos88
open Erdos88.BooleanSlices

universe u v

section OneBucket

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- The subtype of fixed-cardinality subsets is inhabited precisely in the
range in which it is used as a finite uniform probability space. -/
lemma nonempty_booleanSlicePoint (I : Finset V) (ell : ℕ)
    (hell : ell ≤ I.card) : Nonempty (BooleanSlicePoint I ell) := by
  obtain ⟨S, hS⟩ := booleanSlice_nonempty_iff.mpr hell
  exact ⟨⟨S, hS⟩⟩

omit [Fintype V] in
/-- Double-counting form of the first moment on a fixed-cardinality layer.
Every coordinate of `I` belongs to exactly
`choose (|I| - 1) (ell - 1)` members of `I.powersetCard ell`. -/
lemma sum_sum_powersetCard (I : Finset V) (ell : ℕ) (a : V → ℝ)
    (hellPos : 1 ≤ ell) :
    ∑ S ∈ I.powersetCard ell, ∑ i ∈ S, a i =
      (I.card - 1).choose (ell - 1) * ∑ i ∈ I, a i := by
  classical
  calc
    ∑ S ∈ I.powersetCard ell, ∑ i ∈ S, a i =
        ∑ S ∈ I.powersetCard ell, ∑ i ∈ I, if i ∈ S then a i else 0 := by
      apply Finset.sum_congr rfl
      intro S hS
      have hSI : S ⊆ I := (Finset.mem_powersetCard.mp hS).1
      apply Finset.sum_subset_zero_on_sdiff hSI
      · intro i hi
        simp only [Finset.mem_sdiff] at hi
        simp [hi.2]
      · intro i hi
        simp [hi]
    _ = ∑ i ∈ I, ∑ S ∈ I.powersetCard ell, if i ∈ S then a i else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ i ∈ I, ((I.card - 1).choose (ell - 1) : ℝ) * a i := by
      apply Finset.sum_congr rfl
      intro i hiI
      have hcount := Finset.card_filter_powersetCard_subset
        ({i} : Finset V) I ell (by simpa using hiI) (by simpa using hellPos)
      rw [Finset.sum_ite]
      simp only [Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
      congr 1
      simpa using hcount
    _ = (I.card - 1).choose (ell - 1) * ∑ i ∈ I, a i := by
      rw [Finset.mul_sum]

/-- Exact mean of a linear statistic on a uniform `ell`-subset of `I`. -/
theorem expectation_sum_booleanSlicePoint (I : Finset V) (ell : ℕ)
    (a : V → ℝ) (hell : ell ≤ I.card) (hI : I.Nonempty) :
    (𝔼 S : BooleanSlicePoint I ell, ∑ i ∈ S.1, a i) =
      (ell : ℝ) / I.card * ∑ i ∈ I, a i := by
  classical
  by_cases hellZero : ell = 0
  · subst ell
    simp only [Nat.cast_zero, zero_div, zero_mul]
    change Finset.univ.expect (fun S : BooleanSlicePoint I 0 ↦
      ∑ i ∈ S.1, a i) = 0
    apply Finset.expect_eq_zero
    intro S _hS
    have hcard : S.1.card = 0 := (mem_booleanSlice.mp S.2).2
    rw [Finset.card_eq_zero.mp hcard]
    simp
  have hellPos : 1 ≤ ell := Nat.one_le_iff_ne_zero.mpr hellZero
  have hcardPos : 0 < I.card := Finset.card_pos.mpr hI
  have hchoosePos : 0 < I.card.choose ell := Nat.choose_pos hell
  have hsum :
      (∑ S : BooleanSlicePoint I ell, ∑ i ∈ S.1, a i) =
        ((I.card - 1).choose (ell - 1) : ℝ) * ∑ i ∈ I, a i := by
    calc
      (∑ S : BooleanSlicePoint I ell, ∑ i ∈ S.1, a i) =
          ∑ S ∈ booleanSlice I ell, ∑ i ∈ S, a i := by
        symm
        exact Finset.sum_subtype (booleanSlice I ell) (fun _ ↦ Iff.rfl)
          (fun S ↦ ∑ i ∈ S, a i)
      _ = _ := sum_sum_powersetCard I ell a hellPos
  have hchoose :
      I.card.choose ell * ell =
        I.card * (I.card - 1).choose (ell - 1) := by
    simpa using (Nat.choose_mul (n := I.card) (k := ell) (s := 1) hellPos)
  rw [Fintype.expect_eq_sum_div_card, card_booleanSlicePoint, hsum]
  field_simp [Nat.ne_of_gt hcardPos, Nat.ne_of_gt hchoosePos]
  have hchooseReal :
      (I.card.choose ell : ℝ) * ell =
        I.card * ((I.card - 1).choose (ell - 1) : ℝ) := by
    exact_mod_cast hchoose
  calc
    ((I.card - 1).choose (ell - 1) : ℝ) * (∑ i ∈ I, a i) * I.card =
        (∑ i ∈ I, a i) *
          (I.card * ((I.card - 1).choose (ell - 1) : ℝ)) := by ring
    _ = (∑ i ∈ I, a i) * ((I.card.choose ell : ℝ) * ell) := by
      rw [hchooseReal]
    _ = (∑ i ∈ I, a i) * (I.card.choose ell : ℝ) * ell := by ring

/-- A single coordinate of a uniform fixed-cardinality subset has inclusion
probability `ell / |I|`. -/
theorem expectation_indicator_booleanSlicePoint (I : Finset V) (ell : ℕ)
    (i : V) (hell : ell ≤ I.card) (hI : I.Nonempty) :
    (𝔼 S : BooleanSlicePoint I ell, if i ∈ S.1 then (1 : ℝ) else 0) =
      if i ∈ I then (ell : ℝ) / I.card else 0 := by
  classical
  by_cases hi : i ∈ I
  · have h := expectation_sum_booleanSlicePoint I ell
        (fun j ↦ if j = i then (1 : ℝ) else 0) hell hI
    simpa [hi] using h
  · have hnever : ∀ S : BooleanSlicePoint I ell, i ∉ S.1 := by
      intro S hiS
      exact hi ((mem_booleanSlice.mp S.2).1 hiS)
    simp [hnever, hi]

/-- Expected size of the part of a uniform slice satisfying a predicate. -/
theorem expectation_card_filter_booleanSlicePoint (I : Finset V) (ell : ℕ)
    (p : V → Prop) [DecidablePred p]
    (hell : ell ≤ I.card) (hI : I.Nonempty) :
    (𝔼 S : BooleanSlicePoint I ell, ((S.1.filter p).card : ℝ)) =
      (ell : ℝ) / I.card * ((I.filter p).card : ℝ) := by
  have h := expectation_sum_booleanSlicePoint I ell
    (fun i ↦ if p i then (1 : ℝ) else 0) hell hI
  calc
    (𝔼 S : BooleanSlicePoint I ell, ((S.1.filter p).card : ℝ)) =
        𝔼 S : BooleanSlicePoint I ell,
          ∑ i ∈ S.1, if p i then (1 : ℝ) else 0 := by
      apply Finset.expect_congr rfl
      intro S _hS
      exact (Finset.sum_boole (R := ℝ) p S.1).symm
    _ = (ell : ℝ) / I.card *
        ∑ i ∈ I, if p i then (1 : ℝ) else 0 := h
    _ = (ell : ℝ) / I.card * ((I.filter p).card : ℝ) := by
      rw [Finset.sum_boole]

end OneBucket

section TwoBuckets

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- Exact bilinear first moment for two independently sampled uniform
slices.  No disjointness assumption on the buckets is needed for the
identity; applications generally use disjoint buckets. -/
theorem expectation_sum_two_booleanSlicePoints
    (I J : Finset V) (r s : ℕ) (a : V → V → ℝ)
    (hr : r ≤ I.card) (hs : s ≤ J.card)
    (hI : I.Nonempty) (hJ : J.Nonempty) :
    (𝔼 S : BooleanSlicePoint I r,
      𝔼 T : BooleanSlicePoint J s,
        ∑ x ∈ S.1, ∑ y ∈ T.1, a x y) =
      ((r : ℝ) / I.card) * ((s : ℝ) / J.card) *
        ∑ x ∈ I, ∑ y ∈ J, a x y := by
  classical
  have hinner (S : BooleanSlicePoint I r) :
      (𝔼 T : BooleanSlicePoint J s,
          ∑ x ∈ S.1, ∑ y ∈ T.1, a x y) =
        (s : ℝ) / J.card * ∑ x ∈ S.1, ∑ y ∈ J, a x y := by
    have hJmean := expectation_sum_booleanSlicePoint J s
      (fun y ↦ ∑ x ∈ S.1, a x y) hs hJ
    calc
      (𝔼 T : BooleanSlicePoint J s,
          ∑ x ∈ S.1, ∑ y ∈ T.1, a x y) =
          𝔼 T : BooleanSlicePoint J s,
            ∑ y ∈ T.1, ∑ x ∈ S.1, a x y := by
        apply Finset.expect_congr rfl
        intro T _hT
        exact Finset.sum_comm
      _ = (s : ℝ) / J.card * ∑ y ∈ J, ∑ x ∈ S.1, a x y := hJmean
      _ = (s : ℝ) / J.card * ∑ x ∈ S.1, ∑ y ∈ J, a x y := by
        rw [Finset.sum_comm]
  calc
    (𝔼 S : BooleanSlicePoint I r,
      𝔼 T : BooleanSlicePoint J s,
        ∑ x ∈ S.1, ∑ y ∈ T.1, a x y) =
        𝔼 S : BooleanSlicePoint I r,
          ((s : ℝ) / J.card) * ∑ x ∈ S.1, ∑ y ∈ J, a x y := by
      apply Finset.expect_congr rfl
      intro S _hS
      exact hinner S
    _ = ((s : ℝ) / J.card) *
        (𝔼 S : BooleanSlicePoint I r, ∑ x ∈ S.1, ∑ y ∈ J, a x y) := by
      exact (Finset.mul_expect Finset.univ
        (fun S : BooleanSlicePoint I r ↦ ∑ x ∈ S.1, ∑ y ∈ J, a x y)
        ((s : ℝ) / J.card)).symm
    _ = ((s : ℝ) / J.card) *
        (((r : ℝ) / I.card) * ∑ x ∈ I, ∑ y ∈ J, a x y) := by
      rw [expectation_sum_booleanSlicePoint I r
        (fun x ↦ ∑ y ∈ J, a x y) hr hI]
    _ = ((r : ℝ) / I.card) * ((s : ℝ) / J.card) *
        ∑ x ∈ I, ∑ y ∈ J, a x y := by ring

omit [Fintype V] [DecidableEq V] in
/-- An oriented graph crossing count is a double sum of adjacency
indicators.  This is valid even when the two vertex sets overlap. -/
lemma card_interedges_eq_sum_indicator (G : SimpleGraph V) (S T : Finset V) :
    ((G.interedges S T).card : ℝ) =
      ∑ x ∈ S, ∑ y ∈ T, if G.Adj x y then (1 : ℝ) else 0 := by
  classical
  calc
    ((G.interedges S T).card : ℝ) =
        ∑ p ∈ S ×ˢ T, if G.Adj p.1 p.2 then (1 : ℝ) else 0 := by
      rw [Finset.sum_boole]
      congr 1
    _ = ∑ x ∈ S, ∑ y ∈ T,
        if G.Adj x y then (1 : ℝ) else 0 :=
      Finset.sum_product' S T
        (fun x y ↦ if G.Adj x y then (1 : ℝ) else 0)

/-- Degree-into-a-slice specialization of the one-bucket first moment. -/
theorem expectation_card_neighborsIn (G : SimpleGraph V) (v : V)
    (I : Finset V) (ell : ℕ) (hell : ell ≤ I.card) (hI : I.Nonempty) :
    (𝔼 S : BooleanSlicePoint I ell,
        ((Erdos88.neighborsIn G v S.1).card : ℝ)) =
      (ell : ℝ) / I.card * ((Erdos88.neighborsIn G v I).card : ℝ) := by
  classical
  simpa only [Erdos88.neighborsIn] using
    expectation_card_filter_booleanSlicePoint I ell (fun w ↦ G.Adj v w) hell hI

/-- The expected total degree of a fixed vertex set into a uniform slice.
This is the exact finite identity used when a Kwan--Sudakov matching edge
is tested against the random augmentation set. -/
theorem expectation_sum_card_neighborsIn (G : SimpleGraph V) (X I : Finset V)
    (ell : ℕ) (hell : ell ≤ I.card) (hI : I.Nonempty) :
    (𝔼 S : BooleanSlicePoint I ell,
        ∑ v ∈ X, ((Erdos88.neighborsIn G v S.1).card : ℝ)) =
      (ell : ℝ) / I.card *
        ∑ v ∈ X, ((Erdos88.neighborsIn G v I).card : ℝ) := by
  classical
  let a : V → ℝ := fun w ↦
    ∑ v ∈ X, if G.Adj v w then (1 : ℝ) else 0
  have hrewrite (S : Finset V) :
      (∑ v ∈ X, ((Erdos88.neighborsIn G v S).card : ℝ)) =
        ∑ w ∈ S, a w := by
    calc
      (∑ v ∈ X, ((Erdos88.neighborsIn G v S).card : ℝ)) =
          ∑ v ∈ X, ∑ w ∈ S,
            if G.Adj v w then (1 : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro v _hv
        simpa only [Erdos88.neighborsIn] using
          (Finset.sum_boole (R := ℝ) (fun w ↦ G.Adj v w) S).symm
      _ = ∑ w ∈ S, ∑ v ∈ X,
          if G.Adj v w then (1 : ℝ) else 0 := Finset.sum_comm
      _ = ∑ w ∈ S, a w := rfl
  have hmean := expectation_sum_booleanSlicePoint I ell a hell hI
  calc
    (𝔼 S : BooleanSlicePoint I ell,
        ∑ v ∈ X, ((Erdos88.neighborsIn G v S.1).card : ℝ)) =
        𝔼 S : BooleanSlicePoint I ell, ∑ w ∈ S.1, a w := by
      apply Finset.expect_congr rfl
      intro S _hS
      exact hrewrite S.1
    _ = (ell : ℝ) / I.card * ∑ w ∈ I, a w := hmean
    _ = (ell : ℝ) / I.card *
        ∑ v ∈ X, ((Erdos88.neighborsIn G v I).card : ℝ) := by
      rw [hrewrite I]

/-- Exact expected number of oriented crossing edges between two independent
uniform fixed-cardinality subsets. -/
theorem expectation_card_interedges (G : SimpleGraph V)
    (I J : Finset V) (r s : ℕ)
    (hr : r ≤ I.card) (hs : s ≤ J.card)
    (hI : I.Nonempty) (hJ : J.Nonempty) :
    (𝔼 S : BooleanSlicePoint I r,
      𝔼 T : BooleanSlicePoint J s,
        ((G.interedges S.1 T.1).card : ℝ)) =
      ((r : ℝ) / I.card) * ((s : ℝ) / J.card) *
        (G.interedges I J).card := by
  classical
  simpa only [card_interedges_eq_sum_indicator] using
    expectation_sum_two_booleanSlicePoints I J r s
      (fun x y ↦ if G.Adj x y then (1 : ℝ) else 0)
      hr hs hI hJ

end TwoBuckets

end SliceMoments
end Erdos636
