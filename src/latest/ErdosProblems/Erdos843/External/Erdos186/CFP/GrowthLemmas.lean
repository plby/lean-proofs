/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import Mathlib

/-!
# The elementary growth lemmas of Conlon--Fox--Pham

This file formalizes Lemmas 2.39--2.41 of Conlon--Fox--Pham,
*Homogeneous structures in subset sums and non-averaging sets*.  Everything
is stated for literal finite subsets of `ℤ`.  In order not to introduce
fractions into statements about cardinalities, the inequalities
`|∂ₐ S| < |S| / 2` and `|∂ₐ S| ≥ |S| / (2k)` are respectively written as

* `2 * |∂ₐ S| < |S|`, and
* `|S| ≤ 2 * k * |∂ₐ S|`.

Here `∂ₐ S = (a + S) \ S`.  The proof of the shift-counting lemma counts
ordered difference pairs, retaining the multiplicities which would be lost
by passing merely to the difference set.
-/

namespace Erdos186.CFP.GrowthLemmas

open scoped BigOperators

/-! ## Translates, boundaries, and iterated sumsets -/

/-- The pointwise translate `a + S`. -/
def translate (a : ℤ) (S : Finset ℤ) : Finset ℤ :=
  S.image fun x ↦ a + x

@[simp]
theorem mem_translate_iff {a x : ℤ} {S : Finset ℤ} :
    x ∈ translate a S ↔ ∃ y ∈ S, a + y = x := by
  constructor
  · intro hx
    obtain ⟨y, hy, hyx⟩ := Finset.mem_image.mp hx
    exact ⟨y, hy, hyx⟩
  · rintro ⟨y, hy, rfl⟩
    exact Finset.mem_image.mpr ⟨y, hy, rfl⟩

@[simp]
theorem card_translate (a : ℤ) (S : Finset ℤ) :
    (translate a S).card = S.card := by
  exact Finset.card_image_of_injective S (add_right_injective a)

@[simp]
theorem translate_zero (S : Finset ℤ) : translate 0 S = S := by
  ext x
  simp

theorem translate_translate (a b : ℤ) (S : Finset ℤ) :
    translate a (translate b S) = translate (a + b) S := by
  ext x
  simp only [mem_translate_iff]
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨z, hz, by ring⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨b + z, ⟨z, hz, rfl⟩, by ring⟩

/-- The new points created when `S` is shifted by `a`. -/
def boundary (S : Finset ℤ) (a : ℤ) : Finset ℤ :=
  translate a S \ S

@[simp]
theorem mem_boundary_iff {S : Finset ℤ} {a x : ℤ} :
    x ∈ boundary S a ↔ (∃ y ∈ S, a + y = x) ∧ x ∉ S := by
  simp [boundary]

@[simp]
theorem boundary_zero (S : Finset ℤ) : boundary S 0 = ∅ := by
  simp [boundary]

/-- The pointwise sumset `A + B`. -/
def sumset (A B : Finset ℤ) : Finset ℤ :=
  A.biUnion fun a ↦ translate a B

@[simp]
theorem mem_sumset_iff {A B : Finset ℤ} {x : ℤ} :
    x ∈ sumset A B ↔ ∃ a ∈ A, ∃ b ∈ B, a + b = x := by
  simp [sumset]

/-- Pointwise addition of finite integer sets is associative. -/
theorem sumset_assoc (A B C : Finset ℤ) :
    sumset (sumset A B) C = sumset A (sumset B C) := by
  ext x
  simp only [mem_sumset_iff]
  constructor
  · rintro ⟨_, ⟨a, ha, b, hb, rfl⟩, c, hc, rfl⟩
    exact ⟨a, ha, b + c, ⟨b, hb, c, hc, rfl⟩, by ring⟩
  · rintro ⟨a, ha, _, ⟨b, hb, c, hc, rfl⟩, rfl⟩
    exact ⟨a + b, ⟨a, ha, b, hb, rfl⟩, c, hc, by ring⟩

@[simp]
theorem sumset_singleton_zero_right (A : Finset ℤ) :
    sumset A {0} = A := by
  ext x
  simp [mem_sumset_iff]

@[simp]
theorem sumset_singleton_zero_left (A : Finset ℤ) :
    sumset {0} A = A := by
  ext x
  simp [mem_sumset_iff]

/-- The `k`-fold pointwise sumset.  Repetitions of summands are allowed and
the zero-fold sumset is `{0}`. -/
def multifoldSumset : ℕ → Finset ℤ → Finset ℤ
  | 0, _ => {0}
  | k + 1, A => sumset (multifoldSumset k A) A

@[simp]
theorem multifoldSumset_zero (A : Finset ℤ) :
    multifoldSumset 0 A = {0} := rfl

@[simp]
theorem mem_multifoldSumset_succ_iff {k : ℕ} {A : Finset ℤ} {x : ℤ} :
    x ∈ multifoldSumset (k + 1) A ↔
      ∃ y ∈ multifoldSumset k A, ∃ a ∈ A, y + a = x := by
  simp [multifoldSumset, mem_sumset_iff]

/-- Splitting the number of summands splits an iterated sumset as a
pointwise sumset. -/
theorem multifoldSumset_add (m n : ℕ) (A : Finset ℤ) :
    multifoldSumset (m + n) A =
      sumset (multifoldSumset m A) (multifoldSumset n A) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.add_succ, multifoldSumset, ih, multifoldSumset, sumset_assoc]

/-- Membership in a multifold sumset is the existence of an indexed family
of exactly `k` summands from `A`. -/
theorem mem_multifoldSumset_iff {k : ℕ} {A : Finset ℤ} {x : ℤ} :
    x ∈ multifoldSumset k A ↔
      ∃ f : Fin k → ℤ, (∀ i, f i ∈ A) ∧ ∑ i, f i = x := by
  induction k generalizing x with
  | zero =>
      constructor
      · intro hx
        have hx0 : x = 0 := by simpa [multifoldSumset] using hx
        refine ⟨(fun i ↦ Fin.elim0 i), (fun i ↦ Fin.elim0 i), ?_⟩
        simpa using hx0.symm
      · rintro ⟨f, hf, rfl⟩
        simp [multifoldSumset]
  | succ k ih =>
      constructor
      · intro hx
        obtain ⟨y, hy, a, ha, hya⟩ := mem_multifoldSumset_succ_iff.mp hx
        obtain ⟨f, hf, hfsum⟩ := ih.mp hy
        refine ⟨Fin.cons a f, ?_, ?_⟩
        · intro i
          refine Fin.cases ha (fun j ↦ ?_) i
          exact hf j
        · rw [Fin.sum_univ_succ]
          simp only [Fin.cons_zero, Fin.cons_succ]
          rw [hfsum]
          exact (add_comm a y).trans hya
      · rintro ⟨f, hf, rfl⟩
        apply mem_multifoldSumset_succ_iff.mpr
        refine ⟨∑ i : Fin k, f i.succ, ?_, f 0, hf 0, ?_⟩
        · apply ih.mpr
          exact ⟨fun i ↦ f i.succ, fun i ↦ hf i.succ, rfl⟩
        · simp [Fin.sum_univ_succ, add_comm]

/-- If `0 ∈ A`, then zero belongs to every iterated sumset of `A`. -/
theorem zero_mem_multifoldSumset {A : Finset ℤ} (hzero : 0 ∈ A) (k : ℕ) :
    0 ∈ multifoldSumset k A := by
  apply mem_multifoldSumset_iff.mpr
  exact ⟨fun _ ↦ 0, fun _ ↦ hzero, by simp⟩

/-- When `0 ∈ A`, allowing more summands can only enlarge the multifold
sumset. -/
theorem multifoldSumset_mono_index {A : Finset ℤ} (hzero : 0 ∈ A)
    {m n : ℕ} (hmn : m ≤ n) :
    multifoldSumset m A ⊆ multifoldSumset n A := by
  rw [← Nat.add_sub_of_le hmn, multifoldSumset_add]
  intro x hx
  exact mem_sumset_iff.mpr
    ⟨x, hx, 0, zero_mem_multifoldSumset hzero (n - m), by simp⟩

/-! ## Lemma 2.39: telescoping the boundary -/

/-- The boundary of a composite shift is contained in the union of the two
one-step boundaries (with the second one translated). -/
theorem boundary_add_subset (S : Finset ℤ) (a b : ℤ) :
    boundary S (a + b) ⊆
      boundary S a ∪ translate a (boundary S b) := by
  intro x hx
  obtain ⟨⟨z, hzS, habzx⟩, hxS⟩ := mem_boundary_iff.mp hx
  by_cases hbz : b + z ∈ S
  · apply Finset.mem_union_left
    apply mem_boundary_iff.mpr
    exact ⟨⟨b + z, hbz, by omega⟩, hxS⟩
  · apply Finset.mem_union_right
    apply mem_translate_iff.mpr
    refine ⟨b + z, mem_boundary_iff.mpr ?_, by omega⟩
    exact ⟨⟨z, hzS, rfl⟩, hbz⟩

/-- Two-step form of the boundary telescoping inequality. -/
theorem card_boundary_add_le (S : Finset ℤ) (a b : ℤ) :
    (boundary S (a + b)).card ≤
      (boundary S a).card + (boundary S b).card := by
  calc
    (boundary S (a + b)).card ≤
        (boundary S a ∪ translate a (boundary S b)).card :=
      Finset.card_le_card (boundary_add_subset S a b)
    _ ≤ (boundary S a).card + (translate a (boundary S b)).card :=
      Finset.card_union_le _ _
    _ = (boundary S a).card + (boundary S b).card := by simp

/-- **CFP Lemma 2.39.**  The boundary of a sum of shifts is at most the sum
of their individual boundaries. -/
theorem card_boundary_sum_le {k : ℕ} (S : Finset ℤ) (a : Fin k → ℤ) :
    (boundary S (∑ i, a i)).card ≤ ∑ i, (boundary S (a i)).card := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
      exact (card_boundary_add_le S (a 0) (∑ i : Fin k, a i.succ)).trans
        (Nat.add_le_add_left (ih (fun i ↦ a i.succ)) _)

/-! ## Lemma 2.40: there are few small-boundary shifts -/

/-- Ordered pairs in `S × S` whose difference is the prescribed shift. -/
def differenceFiber (S : Finset ℤ) (a : ℤ) : Finset (ℤ × ℤ) :=
  (S.product S).filter fun p ↦ p.1 - p.2 = a

/-- The finite set of all differences of two elements of `S`. -/
def differenceSet (S : Finset ℤ) : Finset ℤ :=
  (S.product S).image fun p ↦ p.1 - p.2

/-- The shifts satisfying the cross-multiplied condition
`|(a + S) \ S| < |S| / 2`.  For nonempty `S`, `mem_smallBoundaryShifts_iff`
shows that the difference-set cutoff in this definition loses no shifts. -/
def smallBoundaryShifts (S : Finset ℤ) : Finset ℤ :=
  (differenceSet S).filter fun a ↦ 2 * (boundary S a).card < S.card

/-- The elements of `S` which are moved out of `S` by the shift `a`. -/
def outgoing (S : Finset ℤ) (a : ℤ) : Finset ℤ :=
  S.filter fun x ↦ a + x ∉ S

/-- The elements of `S` which remain in `S` after the shift `a`. -/
def staying (S : Finset ℤ) (a : ℤ) : Finset ℤ :=
  S.filter fun x ↦ a + x ∈ S

theorem card_boundary_eq_card_outgoing (S : Finset ℤ) (a : ℤ) :
    (boundary S a).card = (outgoing S a).card := by
  symm
  refine Finset.card_bij (fun x _ ↦ a + x) ?_ ?_ ?_
  · intro x hx
    have hx' := Finset.mem_filter.mp hx
    exact mem_boundary_iff.mpr ⟨⟨x, hx'.1, rfl⟩, hx'.2⟩
  · intro x hx y hy hxy
    exact add_left_cancel hxy
  · intro y hy
    obtain ⟨⟨x, hxS, hxy⟩, hyS⟩ := mem_boundary_iff.mp hy
    refine ⟨x, ?_, hxy⟩
    exact Finset.mem_filter.mpr ⟨hxS, by simpa [hxy] using hyS⟩

theorem card_staying_eq_card_differenceFiber (S : Finset ℤ) (a : ℤ) :
    (staying S a).card = (differenceFiber S a).card := by
  refine Finset.card_bij (fun x _ ↦ (a + x, x)) ?_ ?_ ?_
  · intro x hx
    have hx' := Finset.mem_filter.mp hx
    simp [differenceFiber, hx'.1, hx'.2]
  · intro x hx y hy hxy
    exact congrArg Prod.snd hxy
  · intro p hp
    have hp' := Finset.mem_filter.mp hp
    have hpS := Finset.mem_product.mp hp'.1
    refine ⟨p.2, ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      refine ⟨hpS.2, ?_⟩
      have hfirst : a + p.2 = p.1 := by omega
      simpa [hfirst] using hpS.1
    · apply Prod.ext
      · omega
      · rfl

theorem card_outgoing_add_card_staying (S : Finset ℤ) (a : ℤ) :
    (outgoing S a).card + (staying S a).card = S.card := by
  simpa only [outgoing, staying, not_not] using
    (Finset.card_filter_add_card_filter_not (s := S) (fun x ↦ a + x ∉ S))

/-- Every ordered difference fibre accounts for the complement of the
corresponding boundary. -/
theorem card_boundary_add_card_differenceFiber (S : Finset ℤ) (a : ℤ) :
    (boundary S a).card + (differenceFiber S a).card = S.card := by
  rw [card_boundary_eq_card_outgoing, ← card_staying_eq_card_differenceFiber]
  exact card_outgoing_add_card_staying S a

/-- A small-boundary shift of a nonempty set is necessarily a difference of
two elements of the set. -/
theorem mem_differenceSet_of_small_boundary {S : Finset ℤ} (_hS : S.Nonempty)
    {a : ℤ} (ha : 2 * (boundary S a).card < S.card) :
    a ∈ differenceSet S := by
  have hfiber : 0 < (differenceFiber S a).card := by
    have hpartition := card_boundary_add_card_differenceFiber S a
    omega
  obtain ⟨p, hp⟩ := Finset.card_pos.mp hfiber
  have hp' := Finset.mem_filter.mp hp
  exact Finset.mem_image.mpr ⟨p, hp'.1, hp'.2⟩

@[simp]
theorem mem_smallBoundaryShifts_iff {S : Finset ℤ} (hS : S.Nonempty) {a : ℤ} :
    a ∈ smallBoundaryShifts S ↔ 2 * (boundary S a).card < S.card := by
  constructor
  · exact fun ha ↦ (Finset.mem_filter.mp ha).2
  · intro ha
    exact Finset.mem_filter.mpr ⟨mem_differenceSet_of_small_boundary hS ha, ha⟩

/-- The ordered difference fibres over a finite collection of shifts occupy
at most the whole Cartesian square `S × S`. -/
theorem sum_card_differenceFiber_le (S T : Finset ℤ) :
    (∑ a ∈ T, (differenceFiber S a).card) ≤ S.card * S.card := by
  calc
    (∑ a ∈ T, (differenceFiber S a).card) =
        ((S.product S).filter fun p ↦ p.1 - p.2 ∈ T).card := by
      simpa [differenceFiber] using
        (Finset.sum_card_fiberwise_eq_card_filter
          (S.product S) T (fun p : ℤ × ℤ ↦ p.1 - p.2))
    _ ≤ (S.product S).card := Finset.card_filter_le _ _
    _ = S.card * S.card := Finset.card_product S S

/-- **CFP Lemma 2.40.**  Fewer than `2|S|` integer shifts have boundary
strictly smaller than `|S|/2`. -/
theorem card_smallBoundaryShifts_lt (S : Finset ℤ) (hS : S.Nonempty) :
    (smallBoundaryShifts S).card < 2 * S.card := by
  let T := smallBoundaryShifts S
  have hSpos : 0 < S.card := Finset.card_pos.mpr hS
  by_cases hT : T.Nonempty
  · have heach : ∀ a ∈ T, S.card < 2 * (differenceFiber S a).card := by
      intro a ha
      have hsmall : 2 * (boundary S a).card < S.card :=
        (mem_smallBoundaryShifts_iff hS).mp ha
      have hpartition := card_boundary_add_card_differenceFiber S a
      omega
    have hsum :
        T.card * S.card < 2 * ∑ a ∈ T, (differenceFiber S a).card := by
      have h := Finset.sum_lt_sum_of_nonempty hT heach
      simpa [Finset.sum_const, Finset.mul_sum] using h
    have hfibers := sum_card_differenceFiber_le S T
    have hmul : T.card * S.card < (2 * S.card) * S.card := by
      calc
        T.card * S.card < 2 * ∑ a ∈ T, (differenceFiber S a).card := hsum
        _ ≤ 2 * (S.card * S.card) := Nat.mul_le_mul_left 2 hfibers
        _ = (2 * S.card) * S.card := by ring
    exact (Nat.mul_lt_mul_right hSpos).mp hmul
  · have hT0 : T.card = 0 := by simpa [Finset.not_nonempty_iff_eq_empty] using hT
    simpa [T, hT0] using Nat.mul_pos (by decide : 0 < 2) hSpos

/-! ## Lemma 2.41: growth from a large multifold sumset -/

/-- Lemma 2.39 applied to a member of an iterated sumset. -/
theorem card_boundary_le_of_mem_multifoldSumset {S A : Finset ℤ} {k : ℕ}
    {x : ℤ} (hx : x ∈ multifoldSumset k A) :
    ∃ f : Fin k → ℤ, (∀ i, f i ∈ A) ∧ ∑ i, f i = x ∧
      (boundary S x).card ≤ ∑ i, (boundary S (f i)).card := by
  obtain ⟨f, hfA, hfsum⟩ := mem_multifoldSumset_iff.mp hx
  refine ⟨f, hfA, hfsum, ?_⟩
  rw [← hfsum]
  exact card_boundary_sum_le S f

/-- **CFP Lemma 2.41.**  If the `k`-fold sumset of a nonempty finite set
`A` has at least `2|S|` elements, then some shift by an element of `A`
creates at least `|S|/(2k)` new elements.  The conclusion is stated in the
equivalent division-free form. -/
theorem exists_large_boundary_of_two_mul_card_le_multifoldSumset
    (S A : Finset ℤ) (k : ℕ) (hS : S.Nonempty) (_hA : A.Nonempty)
    (hcard : 2 * S.card ≤ (multifoldSumset k A).card) :
    ∃ a ∈ A, S.card ≤ 2 * k * (boundary S a).card := by
  have hSpos : 0 < S.card := Finset.card_pos.mpr hS
  have hk : 0 < k := by
    by_contra hk0
    have hkzero : k = 0 := Nat.eq_zero_of_not_pos hk0
    subst k
    simp [multifoldSumset] at hcard
    omega
  by_contra hlarge
  push Not at hlarge
  have hsmallA : ∀ a ∈ A, 2 * k * (boundary S a).card < S.card := by
    intro a ha
    exact hlarge a ha
  have hsmallAll :
      ∀ x ∈ multifoldSumset k A, 2 * (boundary S x).card < S.card := by
    intro x hx
    obtain ⟨f, hfA, hsum, hboundary⟩ :=
      card_boundary_le_of_mem_multifoldSumset (S := S) hx
    let B : ℕ := ∑ i, (boundary S (f i)).card
    have hterms : ∀ i : Fin k,
        2 * k * (boundary S (f i)).card < S.card := by
      intro i
      exact hsmallA (f i) (hfA i)
    have hsummed :
        k * (2 * B) < k * S.card := by
      have h := Finset.sum_lt_sum_of_nonempty
        (show (Finset.univ : Finset (Fin k)).Nonempty from
          ⟨⟨0, hk⟩, Finset.mem_univ _⟩)
        (fun i _ ↦ hterms i)
      simpa [B, Finset.sum_const, Finset.mul_sum, mul_assoc, mul_left_comm,
        mul_comm] using h
    have hB : 2 * B < S.card := (Nat.mul_lt_mul_left hk).mp hsummed
    exact lt_of_le_of_lt (Nat.mul_le_mul_left 2 hboundary) hB
  have hsubset : multifoldSumset k A ⊆ smallBoundaryShifts S := by
    intro x hx
    exact (mem_smallBoundaryShifts_iff hS).mpr (hsmallAll x hx)
  have hupper : (multifoldSumset k A).card < 2 * S.card :=
    (Finset.card_le_card hsubset).trans_lt (card_smallBoundaryShifts_lt S hS)
  omega

end Erdos186.CFP.GrowthLemmas
