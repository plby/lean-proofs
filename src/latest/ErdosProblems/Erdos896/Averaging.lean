/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

/-!
# A finite averaging lemma for Erdős Problem 896

This file contains the powerset double-counting argument used in the lower
bound.  It deliberately avoids probability theory.  An item is successful
for a selection `P ⊆ S` when its distinguished candidate is selected and
all of its (at most one) forbidden candidates are not selected.  At least one
quarter of the selections are successful for each item.  Summing this fact
and exchanging the two finite sums produces a single selection carrying at
least one quarter of the total natural-number weight.
-/

namespace Erdos896

open scoped BigOperators

section FiberCount

variable {C : Type*} [DecidableEq C]

/-- The successful selections for one owner with no forbidden candidate are
in bijection with the powerset after erasing the owner. -/
private lemma ownerFiber_eq_image (S : Finset C) {p : C} (hp : p ∈ S) :
    S.powerset.filter (fun P ↦ p ∈ P) =
      (S.erase p).powerset.image (fun R ↦ insert p R) := by
  ext P
  simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_image]
  constructor
  · rintro ⟨hPS, hpP⟩
    refine ⟨P.erase p, Finset.erase_subset_erase p hPS, ?_⟩
    exact Finset.insert_erase hpP
  · rintro ⟨R, hRS, rfl⟩
    have hRsub : R ⊆ S := hRS.trans (Finset.erase_subset p S)
    exact ⟨Finset.insert_subset hp hRsub, Finset.mem_insert_self p R⟩

/-- The successful selections for an owner `p` and one distinct forbidden
candidate `q` are in bijection with the powerset after erasing both. -/
private lemma ownerAvoidFiber_eq_image (S : Finset C) {p q : C}
    (hp : p ∈ S) (hpq : p ≠ q) :
    S.powerset.filter (fun P ↦ p ∈ P ∧ q ∉ P) =
      ((S.erase p).erase q).powerset.image (fun R ↦ insert p R) := by
  ext P
  simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_image]
  constructor
  · rintro ⟨hPS, hpP, hqP⟩
    refine ⟨P.erase p, ?_, Finset.insert_erase hpP⟩
    rw [Finset.subset_erase]
    exact ⟨Finset.erase_subset_erase p hPS,
      fun hqErase ↦ hqP (Finset.erase_subset p P hqErase)⟩
  · rintro ⟨R, hRS, rfl⟩
    have hRsubErase : R ⊆ (S.erase p).erase q := hRS
    have hRsub : R ⊆ S :=
      hRsubErase.trans
        ((Finset.erase_subset q (S.erase p)).trans (Finset.erase_subset p S))
    have hqR : q ∉ R := by
      intro hq
      exact (Finset.mem_erase.mp (hRsubErase hq)).1 rfl
    refine ⟨Finset.insert_subset hp hRsub, Finset.mem_insert_self p R, ?_⟩
    intro hqInsert
    rcases Finset.mem_insert.mp hqInsert with hqp | hqR'
    · exact hpq hqp.symm
    · exact hqR hqR'

private lemma insert_owner_injOn (S : Finset C) (p : C) :
    Set.InjOn (fun R : Finset C ↦ insert p R) (S.erase p).powerset := by
  intro R hR T hT hEq
  have hpR : p ∉ R := by
    intro hpR
    exact (Finset.mem_erase.mp (Finset.mem_powerset.mp hR hpR)).1 rfl
  have hpT : p ∉ T := by
    intro hpT
    exact (Finset.mem_erase.mp (Finset.mem_powerset.mp hT hpT)).1 rfl
  simpa [Finset.erase_insert hpR, Finset.erase_insert hpT] using
    congrArg (fun U : Finset C ↦ U.erase p) hEq

private lemma insert_owner_injOn_doubleErase (S : Finset C) (p q : C) :
    Set.InjOn (fun R : Finset C ↦ insert p R) ((S.erase p).erase q).powerset := by
  apply (insert_owner_injOn S p).mono
  intro R hR
  exact Finset.mem_powerset.mpr
    ((Finset.mem_powerset.mp hR).trans (Finset.erase_subset q (S.erase p)))

/-- Selecting a specified member occurs in at least one quarter of all
subsets (in fact, in exactly one half). -/
private lemma card_powerset_le_four_mul_ownerFiber (S : Finset C) {p : C}
    (hp : p ∈ S) :
    S.powerset.card ≤
      4 * (S.powerset.filter fun P ↦ p ∈ P).card := by
  have hcard :
      (S.powerset.filter fun P ↦ p ∈ P).card =
        2 ^ (S.erase p).card := by
    rw [ownerFiber_eq_image S hp,
      (Finset.card_image_iff.mpr (insert_owner_injOn S p)), Finset.card_powerset]
  have herase : (S.erase p).card + 1 = S.card := Finset.card_erase_add_one hp
  rw [Finset.card_powerset, hcard, ← herase, pow_add]
  simp only [pow_one]
  omega

/-- Requiring a specified member to be selected and a distinct specified
member not to be selected occurs in exactly one quarter of all subsets. -/
private lemma card_powerset_eq_four_mul_ownerAvoidFiber (S : Finset C) {p q : C}
    (hp : p ∈ S) (hq : q ∈ S) (hpq : p ≠ q) :
    S.powerset.card =
      4 * (S.powerset.filter fun P ↦ p ∈ P ∧ q ∉ P).card := by
  have hqErase : q ∈ S.erase p := Finset.mem_erase.mpr ⟨hpq.symm, hq⟩
  have hcard :
      (S.powerset.filter fun P ↦ p ∈ P ∧ q ∉ P).card =
        2 ^ ((S.erase p).erase q).card := by
    rw [ownerAvoidFiber_eq_image S hp hpq,
      (Finset.card_image_iff.mpr (insert_owner_injOn_doubleErase S p q)),
      Finset.card_powerset]
  have hpErase : (S.erase p).card + 1 = S.card := Finset.card_erase_add_one hp
  have hqEraseCard : ((S.erase p).erase q).card + 1 = (S.erase p).card :=
    Finset.card_erase_add_one hqErase
  rw [Finset.card_powerset, hcard, ← hpErase, ← hqEraseCard, pow_add, pow_add]
  simp only [pow_one]
  omega

/-- For each item, at least one quarter of the subsets select its owner while
avoiding all of its at most one forbidden candidates. -/
lemma card_powerset_le_four_mul_successFiber
    (S forbidden : Finset C) {p : C}
    (hp : p ∈ S) (hforbidden : forbidden ⊆ S)
    (hcard : forbidden.card ≤ 1) (hpFree : p ∉ forbidden) :
    S.powerset.card ≤
      4 * (S.powerset.filter fun P ↦ p ∈ P ∧ Disjoint forbidden P).card := by
  rcases forbidden.eq_empty_or_nonempty with rfl | ⟨q, hq⟩
  · simpa using card_powerset_le_four_mul_ownerFiber S hp
  · have hforbiddenEq : forbidden = {q} := by
      ext r
      constructor
      · intro hr
        simpa [Finset.mem_singleton] using (Finset.card_le_one.mp hcard r hr q hq)
      · intro hr
        have hrq : r = q := by simpa using hr
        subst r
        exact hq
    have hqS : q ∈ S := hforbidden hq
    have hpq : p ≠ q := by
      intro hpq
      apply hpFree
      simpa [hpq] using hq
    subst forbidden
    simpa [Finset.disjoint_left] using
      (card_powerset_eq_four_mul_ownerAvoidFiber S hp hqS hpq).le

end FiberCount

section Averaging

variable {C I : Type*} [DecidableEq C]

/-- Pure finite double counting: some subset carries at least one quarter of
the total weight of items whose owner is selected and whose forbidden
candidates are absent.

The multiplicative form avoids division and is the form needed for natural
cardinalities in the Erdős 896 construction. -/
theorem exists_selection_four_mul_successWeight_ge
    (S : Finset C) (items : Finset I) (weight : I → ℕ)
    (owner : I → C) (forbidden : I → Finset C)
    (howner : ∀ i ∈ items, owner i ∈ S)
    (hforbidden : ∀ i ∈ items, forbidden i ⊆ S)
    (hcard : ∀ i ∈ items, (forbidden i).card ≤ 1)
    (hownerFree : ∀ i ∈ items, owner i ∉ forbidden i) :
    ∃ P ∈ S.powerset,
      items.sum weight ≤
        4 * ((items.filter fun i ↦
          owner i ∈ P ∧ Disjoint (forbidden i) P).sum weight) := by
  let good : Finset C → I → Prop := fun P i ↦
    owner i ∈ P ∧ Disjoint (forbidden i) P
  let goodWeight : Finset C → ℕ := fun P ↦
    (items.filter fun i ↦ good P i).sum weight
  have hitem : ∀ i ∈ items,
      S.powerset.card * weight i ≤
        4 * ∑ P ∈ S.powerset, if good P i then weight i else 0 := by
    intro i hi
    have hfiber := card_powerset_le_four_mul_successFiber
      S (forbidden i) (howner i hi) (hforbidden i hi)
        (hcard i hi) (hownerFree i hi)
    have hmul := Nat.mul_le_mul_right (weight i) hfiber
    calc
      S.powerset.card * weight i ≤
          (4 * (S.powerset.filter fun P ↦ good P i).card) * weight i := hmul
      _ = 4 * ∑ P ∈ S.powerset, if good P i then weight i else 0 := by
        rw [← Finset.sum_filter]
        simp [mul_assoc]
  have hdouble :
      S.powerset.card * items.sum weight ≤
        4 * ∑ P ∈ S.powerset, goodWeight P := by
    rw [Finset.mul_sum]
    calc
      ∑ i ∈ items, S.powerset.card * weight i ≤
          ∑ i ∈ items,
            4 * ∑ P ∈ S.powerset, if good P i then weight i else 0 := by
        exact Finset.sum_le_sum fun i hi ↦ hitem i hi
      _ = 4 * ∑ i ∈ items,
            ∑ P ∈ S.powerset, if good P i then weight i else 0 := by
        rw [Finset.mul_sum]
      _ = 4 * ∑ P ∈ S.powerset,
            ∑ i ∈ items, if good P i then weight i else 0 := by
        rw [Finset.sum_comm]
      _ = 4 * ∑ P ∈ S.powerset, goodWeight P := by
        apply congrArg (fun n : ℕ ↦ 4 * n)
        apply Finset.sum_congr rfl
        intro P hP
        simp only [goodWeight, Finset.sum_filter]
  by_contra hExists
  push Not at hExists
  have hpointwise : ∀ P ∈ S.powerset,
      4 * goodWeight P < items.sum weight := by
    intro P hP
    simpa [goodWeight, good] using hExists P hP
  have hstrict :
      4 * ∑ P ∈ S.powerset, goodWeight P <
        S.powerset.card * items.sum weight := by
    rw [Finset.mul_sum]
    rw [← Finset.sum_const_nat (f := fun _P : Finset C ↦ items.sum weight)
      (fun _ _ ↦ rfl)]
    apply Finset.sum_lt_sum
    · intro P hP
      exact (hpointwise P hP).le
    · refine ⟨∅, by simp, ?_⟩
      exact hpointwise ∅ (by simp)
  exact (Nat.not_lt_of_ge hdouble) hstrict

end Averaging

end Erdos896
