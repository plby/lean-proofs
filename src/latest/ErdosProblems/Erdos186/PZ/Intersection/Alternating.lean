/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.ConvexCombination

/-!
# Balanced alternating partitions

This file isolates the finite partition step used in the proof of
Pham--Zakharov's intersection lemma.  After distinguishing one element `a`
of a finite set `A`, the remaining elements can be divided into two disjoint
pieces whose sizes differ by at most one.  We construct the first piece with
cardinality `|(A.erase a)| / 2` and take its complement in `A.erase a`.

The second result is the centered balance identity.  It does not depend on
how the balanced partition was chosen: if the full centered weighted sum is
zero, every disjoint two-piece partition of `A.erase a` puts the positive
deviations on one side in exact balance with the reversed deviations on the
other.  The missing summand at `a` vanishes because `v a - v a = 0`.
-/

namespace Erdos186.PZ.Intersection

open scoped BigOperators

set_option autoImplicit false

noncomputable section

/-! ## The finite balanced partition -/

/--
After removing a distinguished member of a finite set, split what remains
into two disjoint pieces, each containing at least `(A.card - 2) / 2`
elements.  The two exact cardinality formulae record the deterministic size
profile of the construction and are often more useful than the lower bounds.
-/
theorem exists_balanced_partition_erase
    {α : Type*} [DecidableEq α] (A : Finset α) (a : α) (ha : a ∈ A) :
    ∃ A₁ A₂ : Finset α,
      A₁ ∪ A₂ = A.erase a ∧
      Disjoint A₁ A₂ ∧
      A₁.card = (A.card - 1) / 2 ∧
      A₂.card = (A.card - 1) - (A.card - 1) / 2 ∧
      (A.card - 2) / 2 ≤ A₁.card ∧
      (A.card - 2) / 2 ≤ A₂.card := by
  let S := A.erase a
  have hhalf : S.card / 2 ≤ S.card := Nat.div_le_self _ _
  obtain ⟨A₁, hA₁S, hA₁card⟩ := Finset.exists_subset_card_eq hhalf
  let A₂ := S \ A₁
  have hScard : S.card = A.card - 1 := Finset.card_erase_of_mem ha
  have hA₂card : A₂.card = S.card - S.card / 2 := by
    simpa [A₂, hA₁card] using Finset.card_sdiff_of_subset hA₁S
  refine ⟨A₁, A₂, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [S, A₂] using Finset.union_sdiff_of_subset hA₁S
  · simpa [A₂] using (Finset.disjoint_sdiff : Disjoint A₁ (S \ A₁))
  · simpa [hScard] using hA₁card
  · simpa [hScard] using hA₂card
  · rw [hA₁card, hScard]
    omega
  · rw [hA₂card, hScard]
    omega

/--
Finite-type form of `exists_balanced_partition_erase`.  This is convenient
when the points are represented by the subtype of a `Finset`, as are the
coefficients produced by the capped convex-combination lemma.
-/
theorem exists_balanced_partition_univ_erase
    {α : Type*} [Fintype α] [DecidableEq α] (a : α) :
    ∃ A₁ A₂ : Finset α,
      A₁ ∪ A₂ = Finset.univ.erase a ∧
      Disjoint A₁ A₂ ∧
      A₁.card = (Fintype.card α - 1) / 2 ∧
      A₂.card = (Fintype.card α - 1) - (Fintype.card α - 1) / 2 ∧
      (Fintype.card α - 2) / 2 ≤ A₁.card ∧
      (Fintype.card α - 2) / 2 ≤ A₂.card := by
  simpa using exists_balanced_partition_erase (Finset.univ : Finset α) a
    (Finset.mem_univ a)

/-! ## Centered balance -/

/--
A zero centered weighted sum balances across every disjoint partition of
the points other than the center.  The statement is module-generic; the PZ
application takes `𝕜 = ℝ` and `E` to be a Euclidean space.
-/
theorem centered_balance_of_partition
    {α 𝕜 E : Type*} [DecidableEq α]
    [Semiring 𝕜] [AddCommGroup E] [Module 𝕜 E]
    {A A₁ A₂ : Finset α} {a : α}
    (ha : a ∈ A)
    (hunion : A₁ ∪ A₂ = A.erase a)
    (hdisj : Disjoint A₁ A₂)
    (c : α → 𝕜) (v : α → E)
    (hzero : (∑ x ∈ A, c x • (v x - v a)) = 0) :
    (∑ x ∈ A₁, c x • (v x - v a)) =
      ∑ x ∈ A₂, c x • (v a - v x) := by
  let f : α → E := fun x ↦ c x • (v x - v a)
  have hcenter : f a = 0 := by simp [f]
  have herase : (∑ x ∈ A.erase a, f x) = 0 := by
    have hsplit := Finset.sum_erase_add A f ha
    rw [hcenter, add_zero] at hsplit
    rw [hsplit]
    exact hzero
  have hparts : (∑ x ∈ A₁, f x) + ∑ x ∈ A₂, f x = 0 := by
    rw [← Finset.sum_union hdisj, hunion]
    exact herase
  calc
    (∑ x ∈ A₁, c x • (v x - v a)) = ∑ x ∈ A₁, f x := rfl
    _ = -(∑ x ∈ A₂, f x) := eq_neg_of_add_eq_zero_left hparts
    _ = ∑ x ∈ A₂, c x • (v a - v x) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro x hx
      dsimp only [f]
      rw [← smul_neg, neg_sub]

/--
Subtype/finite-type version of the centered balance identity.  Its
hypothesis has exactly the shape returned by
`ConvexCombination.exists_capped_centered_combination_of_not_isDeltaConvexPosition`.
-/
theorem centered_balance_of_univ_partition
    {α 𝕜 E : Type*} [Fintype α] [DecidableEq α]
    [Semiring 𝕜] [AddCommGroup E] [Module 𝕜 E]
    {A₁ A₂ : Finset α} {a : α}
    (hunion : A₁ ∪ A₂ = Finset.univ.erase a)
    (hdisj : Disjoint A₁ A₂)
    (c : α → 𝕜) (v : α → E)
    (hzero : (∑ x, c x • (v x - v a)) = 0) :
    (∑ x ∈ A₁, c x • (v x - v a)) =
      ∑ x ∈ A₂, c x • (v a - v x) := by
  apply centered_balance_of_partition (A := Finset.univ) (a := a)
      (Finset.mem_univ a) hunion hdisj c v
  simpa using hzero

/--
Combined finite-type interface: choose a cardinality-balanced partition and
obtain the centered balance identity for that same pair of pieces.  In the
Pham--Zakharov application `α` is the subtype of the original finite point
set, so `Fintype.card α` is definitionally simplified to the cardinality of
that set.
-/
theorem exists_balanced_partition_with_centered_balance
    {α 𝕜 E : Type*} [Fintype α] [DecidableEq α]
    [Semiring 𝕜] [AddCommGroup E] [Module 𝕜 E]
    (a : α) (c : α → 𝕜) (v : α → E)
    (hzero : (∑ x, c x • (v x - v a)) = 0) :
    ∃ A₁ A₂ : Finset α,
      A₁ ∪ A₂ = Finset.univ.erase a ∧
      Disjoint A₁ A₂ ∧
      A₁.card = (Fintype.card α - 1) / 2 ∧
      A₂.card = (Fintype.card α - 1) - (Fintype.card α - 1) / 2 ∧
      (Fintype.card α - 2) / 2 ≤ A₁.card ∧
      (Fintype.card α - 2) / 2 ≤ A₂.card ∧
      (∑ x ∈ A₁, c x • (v x - v a)) =
        ∑ x ∈ A₂, c x • (v a - v x) := by
  obtain ⟨A₁, A₂, hunion, hdisj, hcard₁, hcard₂, hlower₁, hlower₂⟩ :=
    exists_balanced_partition_univ_erase a
  refine ⟨A₁, A₂, hunion, hdisj, hcard₁, hcard₂, hlower₁, hlower₂, ?_⟩
  exact centered_balance_of_univ_partition hunion hdisj c v hzero

end

end Erdos186.PZ.Intersection
