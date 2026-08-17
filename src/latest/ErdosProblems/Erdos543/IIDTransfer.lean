/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, ChatGPT
-/

import Mathlib
import ErdosProblems.Erdos543.Model

/-!
# From independent tuples to uniform subsets

This file contains the exact finite bookkeeping used to pass from an ordered
tuple of independent uniform samples to a uniform subset, after conditioning
on the tuple being injective.  It is entirely generic in the finite target
type.  In particular, no probability measure is hidden in the definitions:
all statements are identities and inequalities between finite cardinalities.
-/

open Finset

namespace Erdos543.IIDTransfer

attribute [local instance] Classical.propDecidable

variable {α : Type*} [Fintype α]
variable {k : ℕ}

/-- The unordered range of an ordered tuple. -/
noncomputable def tupleRange (a : Fin k → α) : Finset α :=
  Finset.univ.image a

/-- All injective ordered `k`-tuples. -/
noncomputable def injectiveTuples (α : Type*) [Fintype α] (k : ℕ) :
    Finset (Fin k → α) := by
  classical
  exact Finset.univ.filter Function.Injective

/-- All ordered `k`-tuples having at least one collision. -/
noncomputable def collisionTuples (α : Type*) [Fintype α] (k : ℕ) :
    Finset (Fin k → α) := by
  classical
  exact Finset.univ.filter (fun a ↦ ¬Function.Injective a)

/-- Number of ordered tuples whose range has property `P`. -/
noncomputable def iidGoodCount (P : Finset α → Prop) (k : ℕ) : ℕ := by
  classical
  exact (Finset.univ.filter (fun a : Fin k → α ↦ P (tupleRange a))).card

/-- Number of injective ordered tuples whose range has property `P`. -/
noncomputable def injectiveGoodCount (P : Finset α → Prop) (k : ℕ) : ℕ := by
  classical
  exact ((injectiveTuples α k).filter (fun a ↦ P (tupleRange a))).card

/-- Number of `k`-element subsets having property `P`. -/
noncomputable def subsetGoodCount (P : Finset α → Prop) (k : ℕ) : ℕ := by
  classical
  exact ((Finset.univ : Finset (Set.powersetCard α k)).filter
    (fun s ↦ P s.1)).card

/-- The subtype presentation of uniform `k`-subsets agrees exactly with the
usual `powersetCard` presentation. -/
lemma subsetGoodCount_eq_powersetCard_filter
    (P : Finset α → Prop) (k : ℕ) :
    subsetGoodCount P k =
      (((Finset.univ : Finset α).powersetCard k).filter P).card := by
  classical
  let valEmb : Set.powersetCard α k ↪ Finset α :=
    ⟨Subtype.val, Subtype.val_injective⟩
  rw [subsetGoodCount, ← Finset.card_map valEmb]
  congr 1
  ext A
  simp [valEmb, Set.powersetCard.mem_iff, and_comm]

/-- Number of all uniform `k`-subsets. -/
lemma card_subsetSpace (α : Type*) [Fintype α] (k : ℕ) :
    Fintype.card (Set.powersetCard α k) = (Fintype.card α).choose k := by
  rw [← Nat.card_eq_fintype_card, Set.powersetCard.card,
    Nat.card_eq_fintype_card]

/-- An injective tuple is the same object as an embedding. -/
def injectiveTupleEquivEmbedding (α : Type*) (k : ℕ) :
    {a : Fin k → α // Function.Injective a} ≃ (Fin k ↪ α) where
  toFun a := ⟨a.1, a.2⟩
  invFun e := ⟨e, e.injective⟩
  left_inv _ := rfl
  right_inv _ := rfl

lemma card_all_tuples (α : Type*) [Fintype α] (k : ℕ) :
    Fintype.card (Fin k → α) = Fintype.card α ^ k := by
  simp

/-- Exact count of injective ordered tuples. -/
lemma card_injectiveTuples (α : Type*) [Fintype α] (k : ℕ) :
    (injectiveTuples α k).card = (Fintype.card α).descFactorial k := by
  classical
  calc
    (injectiveTuples α k).card =
        Fintype.card {a : Fin k → α // Function.Injective a} := by
          rw [injectiveTuples, Fintype.card_subtype]
    _ = Fintype.card (Fin k ↪ α) :=
      Fintype.card_congr (injectiveTupleEquivEmbedding α k)
    _ = (Fintype.card α).descFactorial k := by simp

/-- The collision count is exactly the complement of the falling factorial. -/
lemma card_collisionTuples (α : Type*) [Fintype α] (k : ℕ) :
    (collisionTuples α k).card =
      Fintype.card α ^ k - (Fintype.card α).descFactorial k := by
  classical
  calc
    (collisionTuples α k).card =
        Fintype.card {a : Fin k → α // ¬Function.Injective a} := by
          rw [collisionTuples, Fintype.card_subtype]
    _ = Fintype.card (Fin k → α) -
        Fintype.card {a : Fin k → α // Function.Injective a} := by
          rw [Fintype.card_subtype_compl]
    _ = Fintype.card α ^ k - (Fintype.card α).descFactorial k := by
          rw [card_all_tuples]
          congr 1
          calc
            Fintype.card {a : Fin k → α // Function.Injective a} =
                Fintype.card (Fin k ↪ α) :=
              Fintype.card_congr (injectiveTupleEquivEmbedding α k)
            _ = (Fintype.card α).descFactorial k := by simp

/-- The set of strictly ordered pairs of distinct sample positions. -/
def indexPairs (k : ℕ) : Finset (Fin k × Fin k) :=
  Finset.univ.filter (fun q ↦ q.1 < q.2)

@[simp] lemma card_indexPairs (k : ℕ) :
    (indexPairs k).card = k.choose 2 := by
  simpa [indexPairs] using
    (Fintype.card_product_filter_lt (α := Fin k))

/-- Tuples on which the two specified coordinates collide. -/
noncomputable def pairCollisionTuples (α : Type*) [Fintype α]
    {k : ℕ} (i j : Fin k) : Finset (Fin k → α) := by
  classical
  exact Finset.univ.filter (fun a ↦ a i = a j)

/-- A specified collision costs one free coordinate. -/
lemma card_pairCollisionTuples_le {i j : Fin k} (hij : i ≠ j) :
    (pairCollisionTuples α i j).card ≤ Fintype.card α ^ (k - 1) := by
  classical
  let drop : {a : Fin k → α // a i = a j} →
      ({x : Fin k // x ≠ j} → α) := fun a x ↦ a.1 x.1
  have hdrop : Function.Injective drop := by
    intro a b hab
    apply Subtype.ext
    funext x
    by_cases hx : x = j
    · calc
        a.1 x = a.1 i := by simpa [hx] using a.2.symm
        _ = b.1 i := congrFun hab ⟨i, hij⟩
        _ = b.1 x := by simpa [hx] using b.2
    · exact congrFun hab ⟨x, hx⟩
  calc
    (pairCollisionTuples α i j).card =
        Fintype.card {a : Fin k → α // a i = a j} := by
      rw [pairCollisionTuples, Fintype.card_subtype]
    _ ≤ Fintype.card ({x : Fin k // x ≠ j} → α) :=
      Fintype.card_le_of_injective drop hdrop
    _ = Fintype.card α ^ (k - 1) := by
      rw [Fintype.card_fun]
      congr 1
      simp only [Fintype.card_subtype_compl, Fintype.card_fin,
        Fintype.card_subtype_eq]

/-- The union of all pair-collision events. -/
noncomputable def collisionCover (α : Type*) [Fintype α] (k : ℕ) :
    Finset (Fin k → α) := by
  classical
  exact (indexPairs k).biUnion (fun q ↦ pairCollisionTuples α q.1 q.2)

lemma collisionTuples_subset_collisionCover (α : Type*) [Fintype α] (k : ℕ) :
    collisionTuples α k ⊆ collisionCover α k := by
  classical
  intro a ha
  obtain ⟨_hauniv, hnotinj⟩ := Finset.mem_filter.mp ha
  obtain ⟨i, j, heq, hij⟩ := Function.not_injective_iff.mp hnotinj
  rcases lt_or_gt_of_ne hij with hijlt | hjilt
  · rw [collisionCover, Finset.mem_biUnion]
    exact ⟨(i, j), by simp [indexPairs, hijlt], by simp [pairCollisionTuples, heq]⟩
  · rw [collisionCover, Finset.mem_biUnion]
    exact ⟨(j, i), by simp [indexPairs, hjilt], by simp [pairCollisionTuples, heq.symm]⟩

/-- Union bound for collisions among `k` independent samples from a finite
type of cardinality `n`: at most `choose k 2 * n^(k-1)` tuples collide. -/
lemma card_collisionTuples_le_choose_mul_pow (α : Type*) [Fintype α] (k : ℕ) :
    (collisionTuples α k).card ≤
      k.choose 2 * Fintype.card α ^ (k - 1) := by
  classical
  calc
    (collisionTuples α k).card ≤ (collisionCover α k).card :=
      Finset.card_le_card (collisionTuples_subset_collisionCover α k)
    _ ≤ (indexPairs k).card * Fintype.card α ^ (k - 1) := by
      rw [collisionCover]
      apply Finset.card_biUnion_le_card_mul
      intro q hq
      apply card_pairCollisionTuples_le
      exact ne_of_lt (Finset.mem_filter.mp hq).2
    _ = k.choose 2 * Fintype.card α ^ (k - 1) := by
      rw [card_indexPairs]

/-! ## The constant-size fibers over a subset -/

/-- Embeddings into a fixed combination are precisely the embeddings whose
unordered range is that combination. -/
noncomputable def embeddingsIntoEquivFiber
    (s : Set.powersetCard α k) :
    (Fin k ↪ s.1) ≃
      {e : Fin k ↪ α // Set.powersetCard.ofFinEmb k α e = s} := by
  classical
  let inc : s.1 ↪ α := Function.Embedding.subtype (fun x ↦ x ∈ s.1)
  let forward : (Fin k ↪ s.1) →
      {e : Fin k ↪ α // Set.powersetCard.ofFinEmb k α e = s} := fun e ↦ by
    let f : Fin k ↪ α := e.trans inc
    refine ⟨f, ?_⟩
    apply Subtype.ext
    ext x
    simp only [Set.powersetCard.val_ofFinEmb, Finset.mem_map, Finset.mem_univ,
      true_and]
    constructor
    · rintro ⟨i, rfl⟩
      exact (e i).2
    · intro hx
      have hsurj : Function.Surjective e := by
        exact (Fintype.bijective_iff_injective_and_card e).2
          ⟨e.injective, by simp⟩ |>.2
      obtain ⟨i, hi⟩ := hsurj ⟨x, hx⟩
      exact ⟨i, by simpa [f, inc] using congrArg Subtype.val hi⟩
  let backward :
      {e : Fin k ↪ α // Set.powersetCard.ofFinEmb k α e = s} →
        (Fin k ↪ s.1) := fun e ↦
    { toFun := fun i ↦ ⟨e.1 i, by
        have hi : e.1 i ∈ (Set.powersetCard.ofFinEmb k α e.1).1 := by
          simp
        simpa only [e.2] using hi⟩
      inj' := fun i j hij ↦ e.1.injective (congrArg Subtype.val hij) }
  exact
    { toFun := forward
      invFun := backward
      left_inv := fun e ↦ by ext i; rfl
      right_inv := fun e ↦ by ext i; rfl }

/-- Every fiber of the range map on embeddings has exactly `k!` elements. -/
lemma card_embedding_range_fiber (s : Set.powersetCard α k) :
    Fintype.card
      {e : Fin k ↪ α // Set.powersetCard.ofFinEmb k α e = s} = k.factorial := by
  classical
  rw [← Fintype.card_congr (embeddingsIntoEquivFiber s)]
  rw [Fintype.card_embedding_eq]
  simp [Nat.descFactorial_self]

/-- Exact conditioning identity: every good `k`-subset has `k!` ordered
injective enumerations. -/
lemma injectiveGoodCount_eq_factorial_mul_subsetGoodCount
    (P : Finset α → Prop) (k : ℕ) :
    injectiveGoodCount P k = k.factorial * subsetGoodCount P k := by
  classical
  let goodEquiv :
      {a : Fin k → α // Function.Injective a ∧ P (tupleRange a)} ≃
        {e : Fin k ↪ α // P (Set.powersetCard.ofFinEmb k α e).1} :=
    { toFun := fun a ↦ ⟨⟨a.1, a.2.1⟩, by
          change P (Finset.univ.map (⟨a.1, a.2.1⟩ : Fin k ↪ α))
          rw [Finset.map_eq_image]
          exact a.2.2⟩
      invFun := fun e ↦ ⟨e.1, e.1.injective, by
          change P (Finset.univ.image e.1)
          rw [← Finset.map_eq_image]
          exact e.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  have htuple : injectiveGoodCount P k =
      (Finset.univ.filter
        (fun e : Fin k ↪ α ↦ P (Set.powersetCard.ofFinEmb k α e).1)).card := by
    calc
      injectiveGoodCount P k =
          Fintype.card {a : Fin k → α //
            Function.Injective a ∧ P (tupleRange a)} := by
        rw [injectiveGoodCount, injectiveTuples, Finset.filter_filter,
          Fintype.card_subtype]
      _ = Fintype.card
          {e : Fin k ↪ α // P (Set.powersetCard.ofFinEmb k α e).1} :=
        Fintype.card_congr goodEquiv
      _ = (Finset.univ.filter
          (fun e : Fin k ↪ α ↦ P (Set.powersetCard.ofFinEmb k α e).1)).card := by
        rw [Fintype.card_subtype]
  rw [htuple]
  have hmaps : ∀ e ∈ (Finset.univ.filter
      (fun e : Fin k ↪ α ↦ P (Set.powersetCard.ofFinEmb k α e).1)),
      Set.powersetCard.ofFinEmb k α e ∈
        (Finset.univ.filter (fun s : Set.powersetCard α k ↦ P s.1)) := by
    intro e he
    simpa using he
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  calc
    (∑ s ∈ (Finset.univ.filter
        (fun s : Set.powersetCard α k ↦ P s.1)),
      ((Finset.univ.filter
          (fun e : Fin k ↪ α ↦ P (Set.powersetCard.ofFinEmb k α e).1)).filter
        (fun e ↦ Set.powersetCard.ofFinEmb k α e = s)).card) =
        ∑ _s ∈ (Finset.univ.filter
          (fun s : Set.powersetCard α k ↦ P s.1)), k.factorial := by
      apply Finset.sum_congr rfl
      intro s hs
      have hsP : P s.1 := (Finset.mem_filter.mp hs).2
      have hfiber :
          (Finset.univ.filter
              (fun e : Fin k ↪ α ↦ P (Set.powersetCard.ofFinEmb k α e).1)).filter
            (fun e ↦ Set.powersetCard.ofFinEmb k α e = s) =
          Finset.univ.filter
            (fun e : Fin k ↪ α ↦ Set.powersetCard.ofFinEmb k α e = s) := by
        ext e
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · exact fun h ↦ h.2
        · intro he
          exact ⟨by simpa [he] using hsP, he⟩
      rw [hfiber, ← Fintype.card_subtype]
      exact card_embedding_range_fiber s
    _ = k.factorial * subsetGoodCount P k := by
      simp [subsetGoodCount, Nat.mul_comm]

/-! ## Transfer of a strict sub-half estimate -/

lemma injectiveGoodCount_le_iidGoodCount
    (P : Finset α → Prop) (k : ℕ) :
    injectiveGoodCount P k ≤ iidGoodCount P k := by
  classical
  rw [injectiveGoodCount, iidGoodCount]
  apply Finset.card_le_card
  intro a ha
  obtain ⟨hainj, haP⟩ := Finset.mem_filter.mp ha
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, haP⟩

/-- If fewer than half as many good i.i.d. tuples as injective tuples occur,
then fewer than half of all uniform `k`-subsets are good. -/
lemma two_mul_subsetGoodCount_lt_choose_of_two_mul_iidGoodCount_lt_descFactorial
    (P : Finset α → Prop) (k : ℕ)
    (h : 2 * iidGoodCount P k < (Fintype.card α).descFactorial k) :
    2 * subsetGoodCount P k < (Fintype.card α).choose k := by
  have hinj := injectiveGoodCount_le_iidGoodCount P k
  have hexact := injectiveGoodCount_eq_factorial_mul_subsetGoodCount P k
  have hmul : k.factorial * (2 * subsetGoodCount P k) <
      k.factorial * (Fintype.card α).choose k := by
    calc
      k.factorial * (2 * subsetGoodCount P k) =
          2 * injectiveGoodCount P k := by
        calc
          k.factorial * (2 * subsetGoodCount P k) =
              2 * (k.factorial * subsetGoodCount P k) := by ac_rfl
          _ = 2 * injectiveGoodCount P k := by rw [← hexact]
      _ ≤ 2 * iidGoodCount P k := Nat.mul_le_mul_left 2 hinj
      _ < (Fintype.card α).descFactorial k := h
      _ = k.factorial * (Fintype.card α).choose k :=
        Nat.descFactorial_eq_factorial_mul_choose _ _
  exact (Nat.mul_lt_mul_left (Nat.factorial_pos k)).mp hmul

/-- Count form of conditioning on no collision.  The hypothesis says that
twice the good i.i.d. mass, plus the entire collision mass, is smaller than
the full i.i.d. sample space. -/
lemma two_mul_subsetGoodCount_lt_choose_of_iidGoodCount_add_collision_lt
    (P : Finset α → Prop) (k : ℕ)
    (h : 2 * iidGoodCount P k + (collisionTuples α k).card <
      Fintype.card α ^ k) :
    2 * subsetGoodCount P k < (Fintype.card α).choose k := by
  apply two_mul_subsetGoodCount_lt_choose_of_two_mul_iidGoodCount_lt_descFactorial
  have hcoll := card_collisionTuples α k
  have hdesc := Nat.descFactorial_le_pow (Fintype.card α) k
  omega

/-- A directly checkable sufficient condition obtained by the pairwise union
bound for collisions. -/
lemma two_mul_subsetGoodCount_lt_choose_of_iidGoodCount_add_pairBound_lt
    (P : Finset α → Prop) (k : ℕ)
    (h : 2 * iidGoodCount P k +
        k.choose 2 * Fintype.card α ^ (k - 1) < Fintype.card α ^ k) :
    2 * subsetGoodCount P k < (Fintype.card α).choose k := by
  apply two_mul_subsetGoodCount_lt_choose_of_iidGoodCount_add_collision_lt
  exact lt_of_le_of_lt
    (Nat.add_le_add_left (card_collisionTuples_le_choose_mul_pow α k)
      (2 * iidGoodCount P k)) h

/-- Generic uniform-model conclusion, stated in the repository's exact
`HalfGood` language. -/
theorem not_halfGood_of_iidGoodCount_add_collision_lt
    (P : Finset α → Prop) (k : ℕ)
    (h : 2 * iidGoodCount P k + (collisionTuples α k).card <
      Fintype.card α ^ k) :
    ¬Model.HalfGood (Finset.univ : Finset α) P k := by
  intro hhalf
  have hstrict :=
    two_mul_subsetGoodCount_lt_choose_of_iidGoodCount_add_collision_lt P k h
  have hhalf' : (Fintype.card α).choose k ≤ 2 * subsetGoodCount P k := by
    rw [Model.HalfGood, Finset.card_powersetCard] at hhalf
    rw [subsetGoodCount_eq_powersetCard_filter]
    simpa [Model.goodSets] using hhalf
  omega

/-- Specialized form used for Problem 543: after accounting for collisions,
a strict sub-half estimate for complete i.i.d. tuples disproves half
completeness for uniform subsets. -/
theorem not_halfComplete_of_iidCompleteCount_add_collision_lt
    (G : Type*) [AddCommGroup G] [Fintype G] (k : ℕ)
    (h : 2 * iidGoodCount (α := G) Model.SubsetSumComplete k +
        (collisionTuples G k).card < Fintype.card G ^ k) :
    ¬Model.HalfComplete G k := by
  rw [Model.halfComplete_iff_halfGood]
  exact not_halfGood_of_iidGoodCount_add_collision_lt
    Model.SubsetSumComplete k h

end Erdos543.IIDTransfer
