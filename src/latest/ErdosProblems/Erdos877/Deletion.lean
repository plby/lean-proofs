/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import ErdosProblems.Erdos877.Core

/-!
# Erdős 877: maximality witnesses and good deletions

This file contains the finite incidence argument used in the Łuczak--Schoen
count.  A point omitted from a maximal sum-free set is blocked by a fixed
ordered pair of elements of the set.  Consequently, after deleting `B`, every
newly addable point is either in `B` or has a chosen pair hit by `B`.

The last part is deliberately phrased as elementary finite sums.  In
particular, no probability space is needed for the fixed-proportion good
deletion estimate.
-/

open Finset

namespace Erdos877

/-- An ordered pair in `A` witnessing why `i` cannot be adjoined to `A`.

The second alternative is the natural-number version of `i = a - b`.  In the
last alternative the ordered pair repeats the single element `2 * i`.
-/
def IsWitness (A : Finset ℕ) (i : ℕ) (w : ℕ × ℕ) : Prop :=
  w.1 ∈ A ∧ w.2 ∈ A ∧
    (i = w.1 + w.2 ∨ i + w.2 = w.1 ∨ (2 * i = w.1 ∧ w.1 = w.2))

noncomputable instance instDecidableIsWitness (A : Finset ℕ) (i : ℕ) :
    DecidablePred (IsWitness A i) :=
  Classical.decPred _

/-- Maximality supplies a blocking ordered pair for every omitted ambient
point. -/
theorem exists_isWitness_of_maximal {U A : Finset ℕ}
    (hA : MaximalSumFreeIn U A) {i : ℕ} (hiU : i ∈ U) (hiA : i ∉ A)
    (hi0 : 0 < i) :
    ∃ w : ℕ × ℕ, IsWitness A i w := by
  have hnfree : ¬ SumFree (insert i A) := by
    intro hfree
    exact hA.not_addable hiU ⟨hiA, hfree⟩
  unfold SumFree at hnfree
  push Not at hnfree
  obtain ⟨b, c, hb, hc, hsum⟩ := hnfree
  rcases Finset.mem_insert.mp hb with hbi | hbA
  · subst b
    rcases Finset.mem_insert.mp hc with hci | hcA
    · subst c
      have htwo : 2 * i ∈ A := by
        rcases Finset.mem_insert.mp hsum with hii | htwo
        · omega
        · simpa [two_mul] using htwo
      exact ⟨(2 * i, 2 * i), htwo, htwo, Or.inr (Or.inr ⟨rfl, rfl⟩)⟩
    · rcases Finset.mem_insert.mp hsum with hii | hsumA
      · have hc0 : c = 0 := by omega
        subst c
        exact (hA.sumFree.zero_not_mem hcA).elim
      · exact ⟨(i + c, c), hsumA, hcA, Or.inr (Or.inl rfl)⟩
  · rcases Finset.mem_insert.mp hc with hci | hcA
    · subst c
      rcases Finset.mem_insert.mp hsum with hii | hsumA
      · have hb0 : b = 0 := by omega
        subst b
        exact (hA.sumFree.zero_not_mem hbA).elim
      · exact ⟨(b + i, b), hsumA, hbA, Or.inr (Or.inl (by omega))⟩
    · have hnotA : b + c ∉ A := hA.sumFree hbA hcA
      have hei : b + c = i := by
        rcases Finset.mem_insert.mp hsum with hei | hmem
        · exact hei
        · exact (hnotA hmem).elim
      exact ⟨(b, c), hbA, hcA, Or.inl hei.symm⟩

/-- A globally chosen witness.  Outside `interval n \ A` its value is irrelevant. -/
noncomputable def chosenWitness (n : ℕ) (A : Finset ℕ)
    (hA : MaximalSumFreeIn (interval n) A)
    (i : ℕ) : ℕ × ℕ := by
  classical
  by_cases hi : i ∈ interval n ∧ i ∉ A
  · exact Classical.choose
      (exists_isWitness_of_maximal hA hi.1 hi.2 (by
        have := (mem_interval.mp hi.1).1
        omega))
  · exact (0, 0)

theorem chosenWitness_spec {n : ℕ} {A : Finset ℕ}
    (hA : MaximalSumFreeIn (interval n) A)
    {i : ℕ} (hiU : i ∈ interval n) (hiA : i ∉ A) :
    IsWitness A i (chosenWitness n A hA i) := by
  classical
  rw [chosenWitness]
  split
  · exact Classical.choose_spec (exists_isWitness_of_maximal hA hiU hiA
      (by
        have := (mem_interval.mp hiU).1
        omega))
  · rename_i h
    exact (h ⟨hiU, hiA⟩).elim

/-- Ambient points outside `A` whose chosen pair is hit by `B`. -/
noncomputable def hitSet (n : ℕ) (A : Finset ℕ)
    (hA : MaximalSumFreeIn (interval n) A)
    (B : Finset ℕ) : Finset ℕ :=
  (interval n \ A).filter fun i ↦
    (chosenWitness n A hA i).1 ∈ B ∨ (chosenWitness n A hA i).2 ∈ B

/-- The number of omitted ambient points whose chosen pair is hit by `B`. -/
noncomputable def hitCount (n : ℕ) (A : Finset ℕ)
    (hA : MaximalSumFreeIn (interval n) A)
    (B : Finset ℕ) : ℕ :=
  (hitSet n A hA B).card

/-- The finite set of ambient points that can be newly adjoined to `S`. -/
noncomputable def addableSet (U S : Finset ℕ) : Finset ℕ :=
  U.filter (Addable S)

@[simp] theorem mem_addableSet {U S : Finset ℕ} {x : ℕ} :
    x ∈ addableSet U S ↔ x ∈ U ∧ Addable S x := by
  classical
  simp [addableSet]

/-- If the selected witness pair survives a deletion, the omitted point is
still not addable. -/
theorem not_addable_of_witness_survives {A B : Finset ℕ} {i : ℕ × ℕ}
    {x : ℕ} (hw : IsWitness A x i) (hi1 : i.1 ∉ B) (hi2 : i.2 ∉ B) :
    ¬ Addable (A \ B) x := by
  intro hx
  have hi1s : i.1 ∈ A \ B := Finset.mem_sdiff.mpr ⟨hw.1, hi1⟩
  have hi2s : i.2 ∈ A \ B := Finset.mem_sdiff.mpr ⟨hw.2.1, hi2⟩
  rcases hw.2.2 with hsum | hdiff | hdouble
  · exact hx.sumFree_insert
      (Finset.mem_insert_of_mem hi1s) (Finset.mem_insert_of_mem hi2s)
      (by simp [hsum])
  · exact hx.sumFree_insert
      (Finset.mem_insert_self x (A \ B)) (Finset.mem_insert_of_mem hi2s)
      (by simpa [hdiff] using Finset.mem_insert_of_mem hi1s)
  · exact hx.sumFree_insert
      (Finset.mem_insert_self x (A \ B)) (Finset.mem_insert_self x (A \ B))
      (by
        have hxx : x + x = i.1 := by omega
        rw [hxx]
        exact Finset.mem_insert_of_mem hi1s)

/-- Every addable point after deleting `B` is either a deleted point or an
omitted point whose fixed witness was hit. -/
theorem addableSet_subset_union_hitSet {n : ℕ} {A B : Finset ℕ}
    (hA : MaximalSumFreeIn (interval n) A) :
    addableSet (interval n) (A \ B) ⊆ B ∪ hitSet n A hA B := by
  classical
  intro x hx
  have hxdata := mem_addableSet.mp hx
  by_cases hxA : x ∈ A
  · have hxB : x ∈ B := by
      by_contra hxB
      exact hxdata.2.not_mem (Finset.mem_sdiff.mpr ⟨hxA, hxB⟩)
    exact Finset.mem_union_left _ hxB
  · apply Finset.mem_union_right
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_sdiff.mpr ⟨hxdata.1, hxA⟩, ?_⟩
    by_contra hhit
    push Not at hhit
    exact not_addable_of_witness_survives
      (chosenWitness_spec hA hxdata.1 hxA) hhit.1 hhit.2 hxdata.2

/-- Deterministic deletion bound: addable points are controlled by deleted
points and selected witnesses hit by the deletion. -/
theorem addable_card_le_card_add_hitCount {n : ℕ} {A B : Finset ℕ}
    (hA : MaximalSumFreeIn (interval n) A) :
    (addableSet (interval n) (A \ B)).card ≤ B.card + hitCount n A hA B := by
  classical
  calc
    (addableSet (interval n) (A \ B)).card ≤ (B ∪ hitSet n A hA B).card :=
      Finset.card_le_card (addableSet_subset_union_hitSet hA)
    _ ≤ B.card + (hitSet n A hA B).card := Finset.card_union_le _ _
    _ = B.card + hitCount n A hA B := rfl

/-! ## Incidence counting on a uniform layer -/

/-- The uniform layer of `k`-element deletions. -/
def kSubsets (A : Finset ℕ) (k : ℕ) : Finset (Finset ℕ) :=
  A.powersetCard k

@[simp] theorem mem_kSubsets {A B : Finset ℕ} {k : ℕ} :
    B ∈ kSubsets A k ↔ B ⊆ A ∧ B.card = k := by
  simp [kSubsets]

@[simp] theorem card_kSubsets (A : Finset ℕ) (k : ℕ) :
    (kSubsets A k).card = A.card.choose k := by
  simp [kSubsets, Finset.card_powersetCard]

/-- The exact number of members of a uniform layer containing one fixed
element. -/
theorem card_kSubsets_filter_mem {A : Finset ℕ} {a k : ℕ}
    (ha : a ∈ A) (hk : 1 ≤ k) :
    ((kSubsets A k).filter fun B ↦ a ∈ B).card =
      (A.card - 1).choose (k - 1) := by
  classical
  have h := Finset.card_filter_powersetCard_subset ({a} : Finset ℕ) A k
    (by simpa using ha) (by simpa using hk)
  simpa [kSubsets, Finset.singleton_subset_iff] using h

/-- Boolean-sum form of `card_kSubsets_filter_mem`. -/
theorem sum_kSubsets_indicator_mem {A : Finset ℕ} {a k : ℕ}
    (ha : a ∈ A) (hk : 1 ≤ k) :
    (∑ B ∈ kSubsets A k, if a ∈ B then 1 else 0) =
      (A.card - 1).choose (k - 1) := by
  classical
  rw [Finset.sum_boole]
  exact card_kSubsets_filter_mem ha hk

/-- Finite incidence double count: each omitted point has two selected
coordinates, and each coordinate lies in exactly `choose (m-1) (k-1)`
members of the uniform layer. -/
theorem sum_hitCount_le {n k : ℕ} {A : Finset ℕ}
    (hA : MaximalSumFreeIn (interval n) A) (hk : 1 ≤ k) :
    (∑ B ∈ kSubsets A k, hitCount n A hA B) ≤
      2 * (n - A.card) * (A.card - 1).choose (k - 1) := by
  classical
  let D := (A.card - 1).choose (k - 1)
  have hcoord1 (i : ℕ) (hi : i ∈ interval n \ A) :
      (∑ B ∈ kSubsets A k,
        if (chosenWitness n A hA i).1 ∈ B then 1 else 0) = D := by
    have hi' := Finset.mem_sdiff.mp hi
    have hw := chosenWitness_spec hA hi'.1 hi'.2
    simpa [D] using sum_kSubsets_indicator_mem hw.1 hk
  have hcoord2 (i : ℕ) (hi : i ∈ interval n \ A) :
      (∑ B ∈ kSubsets A k,
        if (chosenWitness n A hA i).2 ∈ B then 1 else 0) = D := by
    have hi' := Finset.mem_sdiff.mp hi
    have hw := chosenWitness_spec hA hi'.1 hi'.2
    simpa [D] using sum_kSubsets_indicator_mem hw.2.1 hk
  calc
    (∑ B ∈ kSubsets A k, hitCount n A hA B) =
        ∑ B ∈ kSubsets A k, ∑ i ∈ interval n \ A,
          if (chosenWitness n A hA i).1 ∈ B ∨
              (chosenWitness n A hA i).2 ∈ B then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro B hB
      rw [hitCount, hitSet, Finset.card_filter]
    _ = ∑ i ∈ interval n \ A, ∑ B ∈ kSubsets A k,
          if (chosenWitness n A hA i).1 ∈ B ∨
              (chosenWitness n A hA i).2 ∈ B then 1 else 0 := by
      rw [Finset.sum_comm]
    _ ≤ ∑ i ∈ interval n \ A,
          ((∑ B ∈ kSubsets A k,
              if (chosenWitness n A hA i).1 ∈ B then 1 else 0) +
           (∑ B ∈ kSubsets A k,
              if (chosenWitness n A hA i).2 ∈ B then 1 else 0)) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro B hB
      by_cases h1 : (chosenWitness n A hA i).1 ∈ B <;>
        by_cases h2 : (chosenWitness n A hA i).2 ∈ B <;> simp [h1, h2]
    _ = ∑ i ∈ interval n \ A, (D + D) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hcoord1 i hi, hcoord2 i hi]
    _ = (interval n \ A).card * (D + D) := by simp
    _ = 2 * (n - A.card) * (A.card - 1).choose (k - 1) := by
      rw [Finset.card_sdiff_of_subset hA.subset, interval_card]
      simp only [D]
      ring

/-- The elementary adjacent-binomial identity in the orientation used by the
incidence calculation. -/
theorem choose_pred_mul {m k : ℕ} (hk : 1 ≤ k) :
    (m - 1).choose (k - 1) * m = m.choose k * k := by
  have h := Nat.choose_mul (n := m) (k := k) (s := 1) hk
  simpa [Nat.choose_one_right, mul_comm] using h.symm

/-- Sum of the deterministic addable bounds over a uniform layer. -/
theorem sum_addable_card_le {n k : ℕ} {A : Finset ℕ}
    (hA : MaximalSumFreeIn (interval n) A) (hk : 1 ≤ k) :
    (∑ B ∈ kSubsets A k, (addableSet (interval n) (A \ B)).card) ≤
      A.card.choose k * k +
        2 * (n - A.card) * (A.card - 1).choose (k - 1) := by
  calc
    (∑ B ∈ kSubsets A k, (addableSet (interval n) (A \ B)).card) ≤
        ∑ B ∈ kSubsets A k, (B.card + hitCount n A hA B) := by
      apply Finset.sum_le_sum
      intro B hB
      exact addable_card_le_card_add_hitCount hA
    _ = (∑ B ∈ kSubsets A k, B.card) +
        ∑ B ∈ kSubsets A k, hitCount n A hA B := by
      rw [Finset.sum_add_distrib]
    _ = A.card.choose k * k +
        ∑ B ∈ kSubsets A k, hitCount n A hA B := by
      congr 1
      calc
        (∑ B ∈ kSubsets A k, B.card) =
            ∑ _B ∈ kSubsets A k, k := by
          apply Finset.sum_congr rfl
          intro B hB
          exact (mem_kSubsets.mp hB).2
        _ = (kSubsets A k).card * k := by simp
        _ = A.card.choose k * k := by rw [card_kSubsets]
    _ ≤ A.card.choose k * k +
        2 * (n - A.card) * (A.card - 1).choose (k - 1) :=
      Nat.add_le_add_left (sum_hitCount_le hA hk) _

/-- Cross-multiplied expectation bound.  If `q*k ≤ |A|`, then the
average number of addable points is at most `(2*n-|A|)/q`. -/
theorem q_mul_sum_addable_card_le {n k q : ℕ} {A : Finset ℕ}
    (hA : MaximalSumFreeIn (interval n) A) (hk : 1 ≤ k)
    (hm : 0 < A.card) (hqk : q * k ≤ A.card) :
    q * (∑ B ∈ kSubsets A k,
      (addableSet (interval n) (A \ B)).card) ≤
      A.card.choose k * (2 * n - A.card) := by
  let m := A.card
  let C := m.choose k
  let D := (m - 1).choose (k - 1)
  let r := n - m
  have hmn : m ≤ n := by
    simpa [m] using (Finset.card_le_card hA.subset).trans_eq (interval_card n)
  have hrm : r + m = n := by
    simp only [r]
    omega
  have hCD : D * m = C * k := by
    simpa [C, D, m] using choose_pred_mul (m := m) hk
  have hqCk : q * C * k ≤ C * m := by
    have := Nat.mul_le_mul_left C hqk
    simpa [m, mul_assoc, mul_left_comm, mul_comm] using this
  have hqDm : q * D * m ≤ C * m := by
    calc
      q * D * m = q * (D * m) := by ring
      _ = q * (C * k) := by rw [hCD]
      _ = q * C * k := by ring
      _ ≤ C * m := hqCk
  have harith : q * (C * k + 2 * r * D) ≤ C * (m + 2 * r) := by
    apply Nat.le_of_mul_le_mul_right (c := m) _ hm
    calc
      q * (C * k + 2 * r * D) * m =
          (q * C * k) * m + 2 * r * (q * D * m) := by ring
      _ ≤ (C * m) * m + 2 * r * (C * m) :=
        Nat.add_le_add (Nat.mul_le_mul_right m hqCk)
          (Nat.mul_le_mul_left (2 * r) hqDm)
      _ = C * (m + 2 * r) * m := by ring
  calc
    q * (∑ B ∈ kSubsets A k,
        (addableSet (interval n) (A \ B)).card) ≤
        q * (C * k + 2 * r * D) := by
      apply Nat.mul_le_mul_left
      simpa [C, D, m, r] using sum_addable_card_le hA hk
    _ ≤ C * (m + 2 * r) := harith
    _ = A.card.choose k * (2 * n - A.card) := by
      simp only [C, m, r]
      congr 1
      omega

/-! ## A fixed positive proportion of good deletions -/

/-- The fixed integer denominator used by the counting proof. -/
def deletionDenom : ℕ := 2 ^ 21

theorem deletionDenom_pos : 0 < deletionDenom := by
  norm_num [deletionDenom]

/-- The selected deletion size, namely `floor (|A| / 2^21)`. -/
def deletionSize (A : Finset ℕ) : ℕ := A.card / deletionDenom

/-- Uniform deletions for which the number of addable points obeys the
cross-multiplied estimate `2^21 h ≤ 2n`. -/
noncomputable def goodDeletions (n : ℕ) (A : Finset ℕ) : Finset (Finset ℕ) :=
  (kSubsets A (deletionSize A)).filter fun B ↦
    deletionDenom * (addableSet (interval n) (A \ B)).card ≤ 2 * n

@[simp] theorem mem_goodDeletions {n : ℕ} {A B : Finset ℕ} :
    B ∈ goodDeletions n A ↔
      B ⊆ A ∧ B.card = deletionSize A ∧
        deletionDenom * (addableSet (interval n) (A \ B)).card ≤ 2 * n := by
  classical
  simp [goodDeletions, and_assoc]

/-- Finite Markov/double-counting form of the good-deletion lemma.  At least
one twentieth of the `floor (|A|/2^21)`-subsets are good once `A` has density
at least `1/10` and contains at least `2^21` elements. -/
theorem goodDeletions_card_lower {n : ℕ} {A : Finset ℕ}
    (hA : MaximalSumFreeIn (interval n) A)
    (hdense : n ≤ 10 * A.card) (hlarge : deletionDenom ≤ A.card) :
    A.card.choose (deletionSize A) / 20 ≤ (goodDeletions n A).card := by
  classical
  let k := deletionSize A
  let F := kSubsets A k
  let good := goodDeletions n A
  let bad := F.filter fun B ↦
    2 * n < deletionDenom * (addableSet (interval n) (A \ B)).card
  let C := A.card.choose k
  have hk : 1 ≤ k := by
    change 1 ≤ A.card / deletionDenom
    rw [Nat.le_div_iff_mul_le deletionDenom_pos]
    simpa [mul_comm] using hlarge
  have hm : 0 < A.card := lt_of_lt_of_le deletionDenom_pos hlarge
  have hqk : deletionDenom * k ≤ A.card := by
    simpa [k, deletionSize, mul_comm] using Nat.mul_div_le A.card deletionDenom
  have htotal : deletionDenom *
      (∑ B ∈ F, (addableSet (interval n) (A \ B)).card) ≤
      C * (2 * n - A.card) := by
    simpa [F, C] using
      q_mul_sum_addable_card_le hA hk hm hqk
  have hgood : good = F.filter fun B ↦
      deletionDenom * (addableSet (interval n) (A \ B)).card ≤ 2 * n := by
    rfl
  have hpart : good.card + bad.card = C := by
    have hdisj : Disjoint good bad := by
      rw [Finset.disjoint_left]
      intro B hBg hBb
      rw [hgood] at hBg
      have hg := (Finset.mem_filter.mp hBg).2
      have hb := (Finset.mem_filter.mp hBb).2
      omega
    have hunion : good ∪ bad = F := by
      ext B
      simp only [Finset.mem_union, hgood, good, bad, Finset.mem_filter]
      constructor
      · rintro (⟨hBF, _⟩ | ⟨hBF, _⟩) <;> exact hBF
      · intro hBF
        refine Or.imp (⟨hBF, ·⟩) (⟨hBF, ·⟩) (le_or_gt
          (deletionDenom * (addableSet (interval n) (A \ B)).card) (2 * n))
    have hc := Finset.card_union_of_disjoint hdisj
    rw [hunion, card_kSubsets] at hc
    simpa [F, C, add_comm] using hc.symm
  by_cases hbad0 : bad = ∅
  · have hgoodC : good.card = C := by simp [hbad0] at hpart; omega
    rw [hgoodC]
    exact Nat.div_le_self C 20
  · have hbadne : bad.Nonempty := Finset.nonempty_iff_ne_empty.mpr hbad0
    have hbadlt : 2 * n * bad.card <
        deletionDenom * ∑ B ∈ bad,
          (addableSet (interval n) (A \ B)).card := by
      calc
        2 * n * bad.card = ∑ _B ∈ bad, 2 * n := by simp [mul_comm]
        _ < ∑ B ∈ bad,
            deletionDenom * (addableSet (interval n) (A \ B)).card := by
          apply Finset.sum_lt_sum_of_nonempty hbadne
          intro B hB
          exact (Finset.mem_filter.mp hB).2
        _ = deletionDenom * ∑ B ∈ bad,
            (addableSet (interval n) (A \ B)).card := by
          rw [Finset.mul_sum]
    have hbadF : bad ⊆ F := Finset.filter_subset _ _
    have hbadTotal : deletionDenom * ∑ B ∈ bad,
          (addableSet (interval n) (A \ B)).card ≤
        deletionDenom * ∑ B ∈ F,
          (addableSet (interval n) (A \ B)).card := by
      exact Nat.mul_le_mul_left _ (Finset.sum_le_sum_of_subset hbadF)
    have hmain : 2 * n * bad.card < C * (2 * n - A.card) :=
      hbadlt.trans_le (hbadTotal.trans htotal)
    have hm2n : A.card ≤ 2 * n := by
      have := (Finset.card_le_card hA.subset).trans_eq (interval_card n)
      omega
    have hsplit1 : 2 * n * C = 2 * n * bad.card + 2 * n * good.card := by
      rw [← Nat.mul_add, add_comm bad.card good.card, hpart]
    have hsplit2 : C * (2 * n - A.card) + C * A.card = 2 * n * C := by
      rw [← Nat.mul_add, Nat.sub_add_cancel hm2n]
      ring
    have hCg : C * A.card < 2 * n * good.card := by omega
    have hn10 : 2 * n * good.card ≤ 20 * A.card * good.card := by
      have h := Nat.mul_le_mul_right (2 * good.card) hdense
      nlinarith
    have hcancel : C < 20 * good.card := by
      apply Nat.lt_of_mul_lt_mul_right (a := A.card)
      calc
        C * A.card < 2 * n * good.card := hCg
        _ ≤ 20 * A.card * good.card := hn10
        _ = (20 * good.card) * A.card := by ring
    have hdiv : C / 20 ≤ good.card :=
      Nat.div_le_of_le_mul (Nat.le_of_lt hcancel)
    simpa [good, C] using hdiv

/-! The generic form below also records the denominator `2^23` appearing in
the published normalization and in the detailed write-up. -/

/-- Deletion size for an arbitrary positive integer denominator. -/
def deletionSizeWith (q : ℕ) (A : Finset ℕ) : ℕ := A.card / q

/-- Good uniform deletions for an arbitrary denominator. -/
noncomputable def goodDeletionsWith (q n : ℕ) (A : Finset ℕ) : Finset (Finset ℕ) :=
  (kSubsets A (deletionSizeWith q A)).filter fun B ↦
    q * (addableSet (interval n) (A \ B)).card ≤ 2 * n

/-- Generic fixed-proportion good-deletion lemma.  A density lower bound
`n ≤ d|A|` yields a proportion `1/(2d)`. -/
theorem goodDeletionsWith_card_lower {n q d : ℕ} {A : Finset ℕ}
    (hA : MaximalSumFreeIn (interval n) A) (hq : 0 < q)
    (hdense : n ≤ d * A.card) (hlarge : q ≤ A.card) :
    A.card.choose (deletionSizeWith q A) / (2 * d) ≤
      (goodDeletionsWith q n A).card := by
  classical
  let k := deletionSizeWith q A
  let F := kSubsets A k
  let good := goodDeletionsWith q n A
  let bad := F.filter fun B ↦
    2 * n < q * (addableSet (interval n) (A \ B)).card
  let C := A.card.choose k
  have hk : 1 ≤ k := by
    change 1 ≤ A.card / q
    rw [Nat.le_div_iff_mul_le hq]
    simpa [mul_comm] using hlarge
  have hm : 0 < A.card := lt_of_lt_of_le hq hlarge
  have hqk : q * k ≤ A.card := by
    simpa [k, deletionSizeWith, mul_comm] using Nat.mul_div_le A.card q
  have htotal : q *
      (∑ B ∈ F, (addableSet (interval n) (A \ B)).card) ≤
      C * (2 * n - A.card) := by
    simpa [F, C] using q_mul_sum_addable_card_le hA hk hm hqk
  have hgood : good = F.filter fun B ↦
      q * (addableSet (interval n) (A \ B)).card ≤ 2 * n := by
    rfl
  have hpart : good.card + bad.card = C := by
    have hdisj : Disjoint good bad := by
      rw [Finset.disjoint_left]
      intro B hBg hBb
      rw [hgood] at hBg
      have hg := (Finset.mem_filter.mp hBg).2
      have hb := (Finset.mem_filter.mp hBb).2
      omega
    have hunion : good ∪ bad = F := by
      ext B
      simp only [Finset.mem_union, hgood, good, bad, Finset.mem_filter]
      constructor
      · rintro (⟨hBF, _⟩ | ⟨hBF, _⟩) <;> exact hBF
      · intro hBF
        refine Or.imp (⟨hBF, ·⟩) (⟨hBF, ·⟩) (le_or_gt
          (q * (addableSet (interval n) (A \ B)).card) (2 * n))
    have hc := Finset.card_union_of_disjoint hdisj
    rw [hunion, card_kSubsets] at hc
    simpa [F, C, add_comm] using hc.symm
  by_cases hbad0 : bad = ∅
  · have hgoodC : good.card = C := by simp [hbad0] at hpart; omega
    rw [hgoodC]
    exact Nat.div_le_self C (2 * d)
  · have hbadne : bad.Nonempty := Finset.nonempty_iff_ne_empty.mpr hbad0
    have hbadlt : 2 * n * bad.card <
        q * ∑ B ∈ bad, (addableSet (interval n) (A \ B)).card := by
      calc
        2 * n * bad.card = ∑ _B ∈ bad, 2 * n := by simp [mul_comm]
        _ < ∑ B ∈ bad,
            q * (addableSet (interval n) (A \ B)).card := by
          apply Finset.sum_lt_sum_of_nonempty hbadne
          intro B hB
          exact (Finset.mem_filter.mp hB).2
        _ = q * ∑ B ∈ bad,
            (addableSet (interval n) (A \ B)).card := by
          rw [Finset.mul_sum]
    have hbadF : bad ⊆ F := Finset.filter_subset _ _
    have hbadTotal : q * ∑ B ∈ bad,
          (addableSet (interval n) (A \ B)).card ≤
        q * ∑ B ∈ F,
          (addableSet (interval n) (A \ B)).card := by
      exact Nat.mul_le_mul_left _ (Finset.sum_le_sum_of_subset hbadF)
    have hmain : 2 * n * bad.card < C * (2 * n - A.card) :=
      hbadlt.trans_le (hbadTotal.trans htotal)
    have hm2n : A.card ≤ 2 * n := by
      have := (Finset.card_le_card hA.subset).trans_eq (interval_card n)
      omega
    have hsplit1 : 2 * n * C = 2 * n * bad.card + 2 * n * good.card := by
      rw [← Nat.mul_add, add_comm bad.card good.card, hpart]
    have hsplit2 : C * (2 * n - A.card) + C * A.card = 2 * n * C := by
      rw [← Nat.mul_add, Nat.sub_add_cancel hm2n]
      ring
    have hCg : C * A.card < 2 * n * good.card := by omega
    have hnd : 2 * n * good.card ≤ (2 * d) * A.card * good.card := by
      have h := Nat.mul_le_mul_right (2 * good.card) hdense
      nlinarith
    have hcancel : C < (2 * d) * good.card := by
      apply Nat.lt_of_mul_lt_mul_right (a := A.card)
      calc
        C * A.card < 2 * n * good.card := hCg
        _ ≤ (2 * d) * A.card * good.card := hnd
        _ = ((2 * d) * good.card) * A.card := by ring
    have hdiv : C / (2 * d) ≤ good.card :=
      Nat.div_le_of_le_mul (Nat.le_of_lt hcancel)
    simpa [good, C] using hdiv

/-- The denominator `2^23` from the Łuczak--Schoen normalization. -/
def deletionDenom877 : ℕ := 2 ^ 23

theorem deletionDenom877_pos : 0 < deletionDenom877 := by
  norm_num [deletionDenom877]

def deletionSize877 (A : Finset ℕ) : ℕ :=
  deletionSizeWith deletionDenom877 A

noncomputable def goodDeletions877 (n : ℕ) (A : Finset ℕ) : Finset (Finset ℕ) :=
  goodDeletionsWith deletionDenom877 n A

/-- The exact `β = 1/2^23` good-deletion statement: at density at least
`1/11`, at least one twenty-second of the uniform layer is good. -/
theorem goodDeletions877_card_lower {n : ℕ} {A : Finset ℕ}
    (hA : MaximalSumFreeIn (interval n) A)
    (hdense : n ≤ 11 * A.card) (hlarge : deletionDenom877 ≤ A.card) :
    A.card.choose (deletionSize877 A) / 22 ≤
      (goodDeletions877 n A).card := by
  simpa [deletionSize877, goodDeletions877] using
    goodDeletionsWith_card_lower hA deletionDenom877_pos hdense hlarge

end Erdos877
