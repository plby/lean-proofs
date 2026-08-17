/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import ErdosProblems.Erdos874.RestrictedGrowth

/-!
# Finite Freiman relations and one-dimensional models for Erdős 874

This file isolates elementary, fully finite ingredients used before the deep
`3k-4`/progression part of the Deshouillers--Freiman argument.

* A small fourth restricted layer forces a genuine relation between two
  different four-element subsets (from cardinality eight onward).
* Cancelling the common part turns such a collision into a nonempty,
  disjoint, balanced additive relation.
* `ContainedInAP` packages a concrete one-dimensional arithmetic-progression
  model, and restricted sums of a set in such a model remain in an explicitly
  bounded arithmetic progression with the same common difference.

No inverse-additive theorem is assumed here.  In particular, the converse
step which turns many additive relations into a short progression is kept
separate: that is precisely the substantive Freiman `3k-4` input.
-/

open scoped BigOperators Pointwise

namespace Erdos874

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## Collisions in the fourth restricted layer -/

/-- For at least eight elements, there are at least six times as many
four-element subsets as elements. -/
lemma six_mul_le_choose_four {n : ℕ} (hn : 8 ≤ n) :
    6 * n ≤ n.choose 4 := by
  induction n, hn using Nat.le_induction with
  | base => norm_num [Nat.choose]
  | succ n hn ih =>
      rw [Nat.choose_succ_succ]
      have hsmall : 6 ≤ n.choose 3 := by
        calc
          6 ≤ Nat.choose 8 3 := by norm_num [Nat.choose]
          _ ≤ n.choose 3 := Nat.choose_le_choose 3 hn
      simpa [Nat.mul_succ, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        Nat.add_le_add ih hsmall

/-- A same-cardinality additive relation supported on `A`. -/
structure RestrictedRelation (A : Finset ℤ) (r : ℕ) where
  left : Finset ℤ
  right : Finset ℤ
  left_subset : left ⊆ A
  right_subset : right ⊆ A
  left_card : left.card = r
  right_card : right.card = r
  sum_eq : ∑ x ∈ left, x = ∑ x ∈ right, x

/-- A relation is nontrivial when its two supporting subsets differ. -/
def RestrictedRelation.Nontrivial {A : Finset ℤ} {r : ℕ}
    (R : RestrictedRelation A r) : Prop :=
  R.left ≠ R.right

/-- `r`-restricted Freiman independence means that the subset-sum map is
injective on the family of `r`-element subsets. -/
def RestrictedFreimanIndependent (A : Finset ℤ) (r : ℕ) : Prop :=
  Set.InjOn (fun B : Finset ℤ => ∑ x ∈ B, x) (A.powersetCard r)

/-- Restricted Freiman independence is exactly the absence of nontrivial
relations of the corresponding size. -/
theorem restrictedFreimanIndependent_iff_no_nontrivial_relation
    (A : Finset ℤ) (r : ℕ) :
    RestrictedFreimanIndependent A r ↔
      ∀ R : RestrictedRelation A r, ¬ R.Nontrivial := by
  constructor
  · intro h R hR
    apply hR
    exact h (Finset.mem_powersetCard.mpr ⟨R.left_subset, R.left_card⟩)
      (Finset.mem_powersetCard.mpr ⟨R.right_subset, R.right_card⟩) R.sum_eq
  · intro h U hU V hV hsum
    have hU' := Finset.mem_powersetCard.mp hU
    have hV' := Finset.mem_powersetCard.mp hV
    by_contra hUV
    exact h ⟨U, V, hU'.1, hV'.1, hU'.2, hV'.2, hsum⟩ hUV

/-- Under restricted Freiman independence the restricted layer has the
maximum possible cardinality, namely the relevant binomial coefficient. -/
theorem restrictedSumset_card_eq_choose_of_independent
    {A : Finset ℤ} {r : ℕ} (h : RestrictedFreimanIndependent A r) :
    (restrictedSumset r A).card = A.card.choose r := by
  rw [restrictedSumset, Finset.card_image_iff.mpr h,
    Finset.card_powersetCard]

/-- A strict cardinality deficit in a restricted layer produces a nontrivial
same-cardinality additive relation.  This is the finite pigeonhole step in
its reusable general form. -/
theorem exists_nontrivial_restrictedRelation_of_card_lt_choose
    {A : Finset ℤ} {r : ℕ}
    (hsmall : (restrictedSumset r A).card < A.card.choose r) :
    ∃ R : RestrictedRelation A r, R.Nontrivial := by
  have himage :
      ((A.powersetCard r).image (fun B => ∑ x ∈ B, x)).card <
        (A.powersetCard r).card := by
    simpa [restrictedSumset, Finset.card_powersetCard] using hsmall
  obtain ⟨U, hU, V, hV, hUV, hsum⟩ :=
    Finset.exists_ne_map_eq_of_card_image_lt himage
  have hU' := Finset.mem_powersetCard.mp hU
  have hV' := Finset.mem_powersetCard.mp hV
  exact ⟨⟨U, V, hU'.1, hV'.1, hU'.2, hV'.2, hsum⟩, hUV⟩

/-- In particular, a fourth restricted layer of size strictly below
`6 * |A|` forces a four-term Freiman relation once `|A| ≥ 8`. -/
theorem exists_nontrivial_four_relation_of_small_restrictedSumset
    {A : Finset ℤ} (hcard : 8 ≤ A.card)
    (hsmall : (restrictedSumset 4 A).card < 6 * A.card) :
    ∃ R : RestrictedRelation A 4, R.Nontrivial := by
  apply exists_nontrivial_restrictedRelation_of_card_lt_choose
  exact hsmall.trans_le (six_mul_le_choose_four hcard)

/-- Distinct two-element subsets of the integers with the same sum are
disjoint.  Equivalently, the representations of a fixed restricted pair sum
form a matching on the underlying set. -/
lemma disjoint_of_card_two_of_sum_eq_of_ne {U V : Finset ℤ}
    (hU : U.card = 2) (hV : V.card = 2)
    (hsum : ∑ x ∈ U, x = ∑ x ∈ V, x) (hne : U ≠ V) :
    Disjoint U V := by
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hU
  obtain ⟨c, d, hcd, rfl⟩ := Finset.card_eq_two.mp hV
  simp [hab, hcd] at hsum
  rw [Finset.disjoint_left]
  intro x hxU hxV
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxU hxV
  apply hne
  ext z
  simp only [Finset.mem_insert, Finset.mem_singleton]
  rcases hxU with rfl | rfl <;> rcases hxV with rfl | rfl <;> omega

/-- A pair-rich set of pair sums has its ordinary double sumset inside the
fourth restricted layer.  This is the `n = 2` specialization of the greedy
packing theorem in `RestrictedGrowth`; its uniform packing parameter must be
at least four. -/
theorem pairRich_add_subset_restrictedSumset_four
    {A S : Finset ℤ} {v : ℕ} (hv : 4 ≤ v)
    (hrich : ∀ z ∈ S, v < (pairRepresentations A z).card) :
    S + S ⊆ restrictedSumset 4 A := by
  simpa [two_nsmul] using
    (nsmul_subset_restrictedSumset_two_mul_of_pair_rich
      (B := A) (S := S) (v := v) hrich 2 (by omega))

/-! ## Cancellation to disjoint balanced relations -/

/-- A balanced additive relation with disjoint nonempty supports. -/
structure DisjointBalancedRelation (A : Finset ℤ) where
  left : Finset ℤ
  right : Finset ℤ
  left_subset : left ⊆ A
  right_subset : right ⊆ A
  disjoint : Disjoint left right
  left_nonempty : left.Nonempty
  right_nonempty : right.Nonempty
  card_eq : left.card = right.card
  sum_eq : ∑ x ∈ left, x = ∑ x ∈ right, x

/-- Cancelling the intersection of a nontrivial restricted relation leaves a
nonempty disjoint balanced relation. -/
noncomputable def RestrictedRelation.toDisjointBalanced
    {A : Finset ℤ} {r : ℕ} (R : RestrictedRelation A r)
    (hR : R.Nontrivial) :
    DisjointBalancedRelation A := by
  let I := R.left ∩ R.right
  have hIleft : I ⊆ R.left := Finset.inter_subset_left
  have hIright : I ⊆ R.right := Finset.inter_subset_right
  have hleftsum :
      (∑ x ∈ I, x) + ∑ x ∈ R.left \ I, x = ∑ x ∈ R.left, x := by
    simpa [I, add_comm] using Finset.sum_sdiff hIleft (f := fun x => x)
  have hrightsum :
      (∑ x ∈ I, x) + ∑ x ∈ R.right \ I, x = ∑ x ∈ R.right, x := by
    simpa [I, add_comm] using Finset.sum_sdiff hIright (f := fun x => x)
  have hsum :
      ∑ x ∈ R.left \ I, x = ∑ x ∈ R.right \ I, x := by
    apply add_left_cancel (a := ∑ x ∈ I, x)
    exact hleftsum.trans (R.sum_eq.trans hrightsum.symm)
  have hcard : (R.left \ I).card = (R.right \ I).card := by
    rw [Finset.card_sdiff_of_subset hIleft, Finset.card_sdiff_of_subset hIright,
      R.left_card, R.right_card]
  have hleftne : (R.left \ I).Nonempty := by
    by_contra h
    have hsub : R.left ⊆ R.right := by
      intro x hx
      by_contra hxr
      have : x ∈ R.left \ I := by simp [I, hx, hxr]
      exact h ⟨x, this⟩
    have heq : R.left = R.right :=
      Finset.eq_of_subset_of_card_le hsub (by simp [R.left_card, R.right_card])
    exact hR heq
  have hrightne : (R.right \ I).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    have : (R.left \ I).card = 0 := by rw [hcard, hempty]; simp
    exact (Finset.card_ne_zero.mpr hleftne) this
  refine
    ⟨R.left \ I, R.right \ I, ?_, ?_, ?_, hleftne, hrightne, hcard, hsum⟩
  · exact Finset.sdiff_subset.trans R.left_subset
  · exact Finset.sdiff_subset.trans R.right_subset
  · rw [Finset.disjoint_left]
    intro x hxleft hxright
    apply (Finset.mem_sdiff.mp hxleft).2
    exact Finset.mem_inter.mpr
      ⟨(Finset.mem_sdiff.mp hxleft).1, (Finset.mem_sdiff.mp hxright).1⟩

/-- The `< 6|A|` hypothesis therefore supplies a nonempty, disjoint,
balanced relation inside `A`. -/
theorem exists_disjoint_balanced_relation_of_small_four_restrictedSumset
    {A : Finset ℤ} (hcard : 8 ≤ A.card)
    (hsmall : (restrictedSumset 4 A).card < 6 * A.card) :
    Nonempty (DisjointBalancedRelation A) := by
  obtain ⟨R, hR⟩ :=
    exists_nontrivial_four_relation_of_small_restrictedSumset hcard hsmall
  exact ⟨R.toDisjointBalanced hR⟩

/-- Cast adapter for the form used in inverse-sumset estimates: any real
constant strictly below six yields the strict natural-cardinality deficit. -/
lemma four_restrictedSumset_card_lt_six_mul_of_real_bound
    {A : Finset ℤ} {lambda : ℝ} (hcard : 0 < A.card) (hlambda : lambda < 6)
    (hsmall : ((restrictedSumset 4 A).card : ℝ) ≤ lambda * A.card) :
    (restrictedSumset 4 A).card < 6 * A.card := by
  have hcardR : (0 : ℝ) < A.card := by exact_mod_cast hcard
  have hstrict : ((restrictedSumset 4 A).card : ℝ) < 6 * A.card :=
    hsmall.trans_lt (mul_lt_mul_of_pos_right hlambda hcardR)
  exact_mod_cast hstrict

/-- The real-valued `lambda < 6` hypothesis directly produces a disjoint
balanced relation. -/
theorem exists_disjoint_balanced_relation_of_real_small_four_restrictedSumset
    {A : Finset ℤ} {lambda : ℝ} (hcard : 8 ≤ A.card) (hlambda : lambda < 6)
    (hsmall : ((restrictedSumset 4 A).card : ℝ) ≤ lambda * A.card) :
    Nonempty (DisjointBalancedRelation A) := by
  apply exists_disjoint_balanced_relation_of_small_four_restrictedSumset hcard
  exact four_restrictedSumset_card_lt_six_mul_of_real_bound
    (by omega) hlambda hsmall

/-! ## Concrete one-dimensional arithmetic-progression models -/

/-- `A` is contained in the `length`-term arithmetic progression
`start, start + step, ..., start + (length - 1) * step`.

The common difference is a positive natural number so that the coordinate is
unique. -/
def ContainedInAP (A : Finset ℤ) (start : ℤ) (step length : ℕ) : Prop :=
  0 < step ∧
    ∀ x ∈ A, ∃ i : ℕ, i < length ∧ x = start + (i : ℤ) * (step : ℤ)

lemma ContainedInAP.step_pos {A : Finset ℤ} {start : ℤ} {step length : ℕ}
    (hA : ContainedInAP A start step length) : 0 < step :=
  hA.1

lemma ContainedInAP.exists_coordinate
    {A : Finset ℤ} {start : ℤ} {step length : ℕ}
    (hA : ContainedInAP A start step length) {x : ℤ} (hx : x ∈ A) :
    ∃ i : ℕ, i < length ∧ x = start + (i : ℤ) * (step : ℤ) :=
  hA.2 x hx

/-- Coordinates in a positive-step progression are unique. -/
lemma ap_coordinate_unique {start : ℤ} {step : ℕ} (hstep : 0 < step)
    {i j : ℕ}
    (hij : start + (i : ℤ) * (step : ℤ) =
      start + (j : ℤ) * (step : ℤ)) :
    i = j := by
  have hstepZ : (step : ℤ) ≠ 0 := by exact_mod_cast hstep.ne'
  have hmul : (i : ℤ) * (step : ℤ) = (j : ℤ) * (step : ℤ) :=
    add_left_cancel hij
  have : (i : ℤ) = (j : ℤ) := mul_right_cancel₀ hstepZ hmul
  exact_mod_cast this

/-- Enlarging the number of progression terms preserves containment. -/
lemma ContainedInAP.mono_length
    {A : Finset ℤ} {start : ℤ} {step length length' : ℕ}
    (hA : ContainedInAP A start step length) (hlen : length ≤ length') :
    ContainedInAP A start step length' := by
  refine ⟨hA.1, ?_⟩
  intro x hx
  obtain ⟨i, hi, rfl⟩ := hA.2 x hx
  exact ⟨i, hi.trans_le hlen, rfl⟩

/-- A subset of a progression remains in the same progression. -/
lemma ContainedInAP.mono_subset
    {A B : Finset ℤ} {start : ℤ} {step length : ℕ}
    (hA : ContainedInAP A start step length) (hBA : B ⊆ A) :
    ContainedInAP B start step length := by
  exact ⟨hA.1, fun x hx => hA.2 x (hBA hx)⟩

/-- The progression model is literally one-dimensional: the coordinate map
on members of `A` is injective. -/
theorem ContainedInAP.exists_injective_coordinate
    {A : Finset ℤ} {start : ℤ} {step length : ℕ}
    (hA : ContainedInAP A start step length) :
    ∃ coord : ℤ → ℕ,
      (∀ x ∈ A, coord x < length ∧
        x = start + (coord x : ℤ) * (step : ℤ)) ∧
      Set.InjOn coord A := by
  let coord : ℤ → ℕ := fun x =>
    if hx : x ∈ A then Classical.choose (hA.2 x hx) else 0
  have hcoord : ∀ x ∈ A, coord x < length ∧
      x = start + (coord x : ℤ) * (step : ℤ) := by
    intro x hx
    simpa [coord, hx] using Classical.choose_spec (hA.2 x hx)
  refine ⟨coord, hcoord, ?_⟩
  intro x hx y hy hxy
  have hxrep := (hcoord x hx).2
  have hyrep := (hcoord y hy).2
  rw [hxrep, hyrep]
  exact congrArg (fun n : ℕ => start + (n : ℤ) * (step : ℤ)) hxy

/-- A set in a progression has at most as many elements as the progression
has terms. -/
theorem ContainedInAP.card_le
    {A : Finset ℤ} {start : ℤ} {step length : ℕ}
    (hA : ContainedInAP A start step length) :
    A.card ≤ length := by
  obtain ⟨coord, hcoord, hinj⟩ := hA.exists_injective_coordinate
  have hmaps : Set.MapsTo coord A (Finset.range length) := by
    intro x hx
    exact Finset.mem_range.mpr (hcoord x hx).1
  simpa using Finset.card_le_card_of_injOn coord hmaps hinj

/-- Every restricted sum of a progression-contained set lies in the same
residue class, with a nonnegative coordinate bounded by `r * length`.

The deliberately slightly loose length `r * length + 1` avoids endpoint
subtractions and is the form most convenient for subsequent counting. -/
theorem ContainedInAP.restrictedSumset
    {A : Finset ℤ} {start : ℤ} {step length r : ℕ}
    (hA : ContainedInAP A start step length) :
    ContainedInAP (restrictedSumset r A) ((r : ℤ) * start) step
      (r * length + 1) := by
  obtain ⟨coord, hcoord, hinj⟩ := hA.exists_injective_coordinate
  refine ⟨hA.1, ?_⟩
  intro z hz
  obtain ⟨B, hBA, hBcard, hBsum⟩ := mem_restrictedSumset.mp hz
  let j : ℕ := ∑ x ∈ B, coord x
  refine ⟨j, ?_, ?_⟩
  · have hcoord_le : ∀ x ∈ B, coord x ≤ length := by
      intro x hx
      exact (hcoord x (hBA hx)).1.le
    have hsum_le : j ≤ B.card * length := by
      simpa [j] using B.sum_le_card_nsmul coord length hcoord_le
    rw [hBcard] at hsum_le
    omega
  · calc
      z = ∑ x ∈ B, x := hBsum.symm
      _ = ∑ x ∈ B, (start + (coord x : ℤ) * (step : ℤ)) := by
        apply Finset.sum_congr rfl
        intro x hx
        exact hcoord x (hBA hx) |>.2
      _ = (B.card : ℤ) * start +
          ((∑ x ∈ B, coord x : ℕ) : ℤ) * (step : ℤ) := by
        push_cast
        simp_rw [Finset.sum_add_distrib, Finset.sum_mul]
        simp [mul_comm]
      _ = (r : ℤ) * start + (j : ℤ) * (step : ℤ) := by
        simp [hBcard, j]

end

end Erdos874
