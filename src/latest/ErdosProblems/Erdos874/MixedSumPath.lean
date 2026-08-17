/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import ErdosProblems.Erdos874.ResidueSubgroup

/-!
# Ordered mixed-subset paths

Let `X` and `Y` be disjoint finite sets of integers, both of cardinality
`T`.  For `0 ≤ j ≤ T`, form `W j` from the first `j` elements of `Y`
and the first `T-j` elements of `X`, with both sets written in increasing
order.  Every `W j` has cardinality `T`.  Moreover, if `sigma j` is its sum,
then

`sigma (j+1) - sigma j = Y[j] - X[T-j-1]`.

Consequently these increments are nondecreasing.  The last theorem packages
the construction as a finite convex path, in a form intended for the
translate-packing argument in the modular structure proof.
-/

open scoped BigOperators

namespace Erdos874

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## Increasing prefixes of a finite integer set -/

/-- The increasing enumeration of a finite integer set, extended by zero
past the end. -/
def mixedOrderedEntry (A : Finset ℤ) (i : ℕ) : ℤ :=
  if hi : i < A.card then A.orderEmbOfFin rfl ⟨i, hi⟩ else 0

@[simp] theorem mixedOrderedEntry_of_lt (A : Finset ℤ) {i : ℕ}
    (hi : i < A.card) :
    mixedOrderedEntry A i = A.orderEmbOfFin rfl ⟨i, hi⟩ := by
  simp [mixedOrderedEntry, hi]

theorem mixedOrderedEntry_mem (A : Finset ℤ) {i : ℕ}
    (hi : i < A.card) :
    mixedOrderedEntry A i ∈ A := by
  rw [mixedOrderedEntry_of_lt A hi]
  exact A.orderEmbOfFin_mem rfl _

theorem mixedOrderedEntry_strict {A : Finset ℤ} {i j : ℕ}
    (hij : i < j) (hj : j < A.card) :
    mixedOrderedEntry A i < mixedOrderedEntry A j := by
  have hi : i < A.card := hij.trans hj
  rw [mixedOrderedEntry_of_lt A hi, mixedOrderedEntry_of_lt A hj]
  exact (A.orderEmbOfFin rfl).strictMono (Fin.mk_lt_mk.mpr hij)

/-- The first `n` elements of `A` in increasing order. -/
def orderedPrefix (A : Finset ℤ) (n : ℕ) : Finset ℤ :=
  (Finset.range n).image (mixedOrderedEntry A)

theorem orderedPrefix_subset {A : Finset ℤ} {n : ℕ}
    (hn : n ≤ A.card) :
    orderedPrefix A n ⊆ A := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
  exact mixedOrderedEntry_mem A ((Finset.mem_range.mp hi).trans_le hn)

theorem card_orderedPrefix {A : Finset ℤ} {n : ℕ}
    (hn : n ≤ A.card) :
    (orderedPrefix A n).card = n := by
  rw [orderedPrefix, Finset.card_image_iff.mpr, Finset.card_range]
  intro i hi j hj hij
  by_contra hne
  rcases lt_or_gt_of_ne hne with hij' | hji'
  · have hjA : j < A.card := (Finset.mem_range.mp hj).trans_le hn
    have := mixedOrderedEntry_strict hij' hjA
    omega
  · have hiA : i < A.card := (Finset.mem_range.mp hi).trans_le hn
    have := mixedOrderedEntry_strict hji' hiA
    omega

@[simp] theorem orderedPrefix_card (A : Finset ℤ) :
    orderedPrefix A A.card = A := by
  exact Finset.eq_of_subset_of_card_le (orderedPrefix_subset le_rfl)
    (by rw [card_orderedPrefix le_rfl])

@[simp] theorem orderedPrefix_zero (A : Finset ℤ) :
    orderedPrefix A 0 = ∅ := by
  simp [orderedPrefix]

theorem orderedPrefix_succ {A : Finset ℤ} {n : ℕ}
    (_hn : n < A.card) :
    orderedPrefix A (n + 1) =
      insert (mixedOrderedEntry A n) (orderedPrefix A n) := by
  ext x
  simp only [orderedPrefix, Finset.mem_image, Finset.mem_range,
    Finset.mem_insert]
  constructor
  · rintro ⟨i, hi, rfl⟩
    by_cases hin : i = n
    · exact Or.inl (congrArg (mixedOrderedEntry A) hin)
    · exact Or.inr ⟨i, by omega, rfl⟩
  · rintro (rfl | ⟨i, hi, rfl⟩)
    · exact ⟨n, by omega, rfl⟩
    · exact ⟨i, by omega, rfl⟩

theorem mixedOrderedEntry_not_mem_orderedPrefix {A : Finset ℤ} {n : ℕ}
    (hn : n < A.card) :
    mixedOrderedEntry A n ∉ orderedPrefix A n := by
  intro hmem
  obtain ⟨i, hi, heq⟩ := Finset.mem_image.mp hmem
  have hin : i < n := Finset.mem_range.mp hi
  have hlt := mixedOrderedEntry_strict hin hn
  omega

theorem sum_orderedPrefix_succ {A : Finset ℤ} {n : ℕ}
    (hn : n < A.card) :
    (orderedPrefix A (n + 1)).sum id =
      (orderedPrefix A n).sum id + mixedOrderedEntry A n := by
  rw [orderedPrefix_succ hn, Finset.sum_insert
    (mixedOrderedEntry_not_mem_orderedPrefix hn)]
  simp [add_comm]

theorem mixedOrderedEntry_mono {A : Finset ℤ} {i j : ℕ}
    (hij : i ≤ j) (hj : j < A.card) :
    mixedOrderedEntry A i ≤ mixedOrderedEntry A j := by
  rcases hij.eq_or_lt with rfl | hij
  · exact le_rfl
  · exact (mixedOrderedEntry_strict hij hj).le

/-! ## The mixed path -/

/-- At time `j`, take the first `j` elements of `Y` and the first `T-j`
elements of `X`.  The intended domain is `j ≤ T`; subtraction is truncated
only so the definition is total. -/
def orderedMixedSubset (X Y : Finset ℤ) (T j : ℕ) : Finset ℤ :=
  orderedPrefix Y j ∪ orderedPrefix X (T - j)

/-- The finite, `Fin`-indexed version of `orderedMixedSubset`. -/
def orderedMixedPath (X Y : Finset ℤ) (T : ℕ) :
    Fin (T + 1) → Finset ℤ :=
  fun j ↦ orderedMixedSubset X Y T j

/-- The sum along the ordered mixed-subset path. -/
def orderedMixedSum (X Y : Finset ℤ) (T j : ℕ) : ℤ :=
  (orderedMixedSubset X Y T j).sum id

/-- The finite, `Fin`-indexed sum path. -/
def orderedMixedSumPath (X Y : Finset ℤ) (T : ℕ) :
    Fin (T + 1) → ℤ :=
  fun j ↦ orderedMixedSum X Y T j

theorem orderedMixedSubset_subset
    {X Y : Finset ℤ} {T j : ℕ}
    (hXcard : X.card = T) (hYcard : Y.card = T) (hj : j ≤ T) :
    orderedMixedSubset X Y T j ⊆ X ∪ Y := by
  apply Finset.union_subset
  · exact (orderedPrefix_subset (A := Y) (by omega)).trans
      Finset.subset_union_right
  · exact (orderedPrefix_subset (A := X) (by omega)).trans
      Finset.subset_union_left

theorem card_orderedMixedSubset
    {X Y : Finset ℤ} {T j : ℕ}
    (hXY : Disjoint X Y) (hXcard : X.card = T)
    (hYcard : Y.card = T) (hj : j ≤ T) :
    (orderedMixedSubset X Y T j).card = T := by
  have hpre : Disjoint (orderedPrefix Y j) (orderedPrefix X (T - j)) :=
    hXY.symm.mono (orderedPrefix_subset (A := Y) (by omega))
      (orderedPrefix_subset (A := X) (by omega))
  rw [orderedMixedSubset, Finset.card_union_of_disjoint hpre,
    card_orderedPrefix (A := Y) (by omega),
    card_orderedPrefix (A := X) (by omega)]
  omega

theorem orderedMixedPath_subset
    {X Y : Finset ℤ} {T : ℕ}
    (hXcard : X.card = T) (hYcard : Y.card = T)
    (j : Fin (T + 1)) :
    orderedMixedPath X Y T j ⊆ X ∪ Y := by
  exact orderedMixedSubset_subset hXcard hYcard (by omega)

theorem card_orderedMixedPath
    {X Y : Finset ℤ} {T : ℕ}
    (hXY : Disjoint X Y) (hXcard : X.card = T)
    (hYcard : Y.card = T) (j : Fin (T + 1)) :
    (orderedMixedPath X Y T j).card = T := by
  exact card_orderedMixedSubset hXY hXcard hYcard (by omega)

@[simp] theorem orderedMixedSubset_zero
    {X Y : Finset ℤ} {T : ℕ} (hXcard : X.card = T) :
    orderedMixedSubset X Y T 0 = X := by
  subst T
  simp [orderedMixedSubset]

@[simp] theorem orderedMixedSubset_card
    {X Y : Finset ℤ} {T : ℕ}
    (hYcard : Y.card = T) :
    orderedMixedSubset X Y T T = Y := by
  subst T
  simp [orderedMixedSubset]

@[simp] theorem orderedMixedPath_zero
    {X Y : Finset ℤ} {T : ℕ} (hXcard : X.card = T) :
    orderedMixedPath X Y T ⟨0, by omega⟩ = X := by
  exact orderedMixedSubset_zero hXcard

@[simp] theorem orderedMixedPath_last
    {X Y : Finset ℤ} {T : ℕ} (hYcard : Y.card = T) :
    orderedMixedPath X Y T ⟨T, by omega⟩ = Y := by
  exact orderedMixedSubset_card hYcard

/-- Every value of the sum path is a restricted `T`-sum of any ambient set
containing both fibres.  This is the integration point used by translate
packing: the path supplies actual integer sums, not only residue classes. -/
theorem orderedMixedSumPath_mem_restrictedSumset
    {A X Y : Finset ℤ} {T : ℕ}
    (hXY : Disjoint X Y) (hXcard : X.card = T)
    (hYcard : Y.card = T) (hsub : X ∪ Y ⊆ A)
    (j : Fin (T + 1)) :
    orderedMixedSumPath X Y T j ∈ restrictedSumset T A := by
  apply mem_restrictedSumset.mpr
  exact ⟨orderedMixedPath X Y T j,
    (orderedMixedPath_subset hXcard hYcard j).trans hsub,
    card_orderedMixedPath hXY hXcard hYcard j, rfl⟩

/-! ## Residues along the path -/

theorem cast_sum_orderedPrefix
    {A : Finset ℤ} {q n : ℕ} {g : ZMod q}
    (hn : n ≤ A.card) (hres : ∀ x ∈ A, (x : ZMod q) = g) :
    (((orderedPrefix A n).sum id : ℤ) : ZMod q) = n • g := by
  push_cast
  calc
    ∑ x ∈ orderedPrefix A n, (x : ZMod q) =
        ∑ _x ∈ orderedPrefix A n, g := by
          apply Finset.sum_congr rfl
          intro x hx
          exact hres x (orderedPrefix_subset hn hx)
    _ = n • g := by rw [Finset.sum_const, card_orderedPrefix hn]

theorem orderedMixedSum_residue
    {X Y : Finset ℤ} {T j q : ℕ} {g0 g : ZMod q}
    (hXY : Disjoint X Y) (hXcard : X.card = T)
    (hYcard : Y.card = T) (hj : j ≤ T)
    (hXres : ∀ x ∈ X, (x : ZMod q) = g0)
    (hYres : ∀ y ∈ Y, (y : ZMod q) = g) :
    ((orderedMixedSum X Y T j : ℤ) : ZMod q) =
      T • g0 + j • (g - g0) := by
  have hpre : Disjoint (orderedPrefix Y j) (orderedPrefix X (T - j)) :=
    hXY.symm.mono (orderedPrefix_subset (A := Y) (by omega))
      (orderedPrefix_subset (A := X) (by omega))
  have hYcast := cast_sum_orderedPrefix (A := Y) (q := q)
    (n := j) (g := g) (by omega) hYres
  have hXcast := cast_sum_orderedPrefix (A := X) (q := q)
    (n := T - j) (g := g0) (by omega) hXres
  rw [orderedMixedSum, orderedMixedSubset,
    Finset.sum_union hpre]
  push_cast at hYcast hXcast ⊢
  rw [hYcast, hXcast]
  have hT : T = (T - j) + j := by omega
  conv_rhs =>
    lhs
    rw [hT, add_nsmul]
  module

theorem orderedMixedSumPath_residue
    {X Y : Finset ℤ} {T q : ℕ} {g0 g : ZMod q}
    (hXY : Disjoint X Y) (hXcard : X.card = T)
    (hYcard : Y.card = T)
    (hXres : ∀ x ∈ X, (x : ZMod q) = g0)
    (hYres : ∀ y ∈ Y, (y : ZMod q) = g)
    (j : Fin (T + 1)) :
    ((orderedMixedSumPath X Y T j : ℤ) : ZMod q) =
      T • g0 + (j : ℕ) • (g - g0) := by
  exact orderedMixedSum_residue hXY hXcard hYcard (by omega) hXres hYres

/-! ## Discrete convexity -/

theorem orderedMixedSum_eq_add
    {X Y : Finset ℤ} {T j : ℕ}
    (hXY : Disjoint X Y) (hXcard : X.card = T)
    (hYcard : Y.card = T) (hj : j ≤ T) :
    orderedMixedSum X Y T j =
      (orderedPrefix Y j).sum id + (orderedPrefix X (T - j)).sum id := by
  rw [orderedMixedSum, orderedMixedSubset, Finset.sum_union]
  exact hXY.symm.mono (orderedPrefix_subset (A := Y) (by omega))
    (orderedPrefix_subset (A := X) (by omega))

/-- Exact increment formula for the mixed sum path. -/
theorem orderedMixedSum_succ_sub
    {X Y : Finset ℤ} {T j : ℕ}
    (hXY : Disjoint X Y) (hXcard : X.card = T)
    (hYcard : Y.card = T) (hj : j < T) :
    orderedMixedSum X Y T (j + 1) - orderedMixedSum X Y T j =
      mixedOrderedEntry Y j - mixedOrderedEntry X (T - j - 1) := by
  rw [orderedMixedSum_eq_add hXY hXcard hYcard (by omega),
    orderedMixedSum_eq_add hXY hXcard hYcard (by omega),
    sum_orderedPrefix_succ (A := Y) (by omega)]
  have hsub : T - j = (T - (j + 1)) + 1 := by omega
  have hXsum : (orderedPrefix X (T - j)).sum id =
      (orderedPrefix X (T - (j + 1))).sum id +
        mixedOrderedEntry X (T - (j + 1)) := by
    rw [hsub, sum_orderedPrefix_succ (A := X) (by omega)]
  rw [hXsum]
  have hidx : T - (j + 1) = T - j - 1 := by omega
  rw [hidx]
  ring

/-- The increments of the mixed sum path are nondecreasing.  This is the
discrete convexity property needed by the subsequent interval-packing lemma. -/
theorem orderedMixedSum_increment_mono
    {X Y : Finset ℤ} {T i j : ℕ}
    (hXY : Disjoint X Y) (hXcard : X.card = T)
    (hYcard : Y.card = T) (hij : i ≤ j) (hj : j < T) :
    orderedMixedSum X Y T (i + 1) - orderedMixedSum X Y T i ≤
      orderedMixedSum X Y T (j + 1) - orderedMixedSum X Y T j := by
  rw [orderedMixedSum_succ_sub hXY hXcard hYcard (hij.trans_lt hj),
    orderedMixedSum_succ_sub hXY hXcard hYcard hj]
  have hYmono : mixedOrderedEntry Y i ≤ mixedOrderedEntry Y j :=
    mixedOrderedEntry_mono hij (by omega)
  have hindex : T - j - 1 ≤ T - i - 1 := by omega
  have hXmono : mixedOrderedEntry X (T - j - 1) ≤
      mixedOrderedEntry X (T - i - 1) :=
    mixedOrderedEntry_mono hindex (by omega)
  omega

/-- A clean `Fin T` API for the nondecreasing displacement sequence. -/
theorem monotone_orderedMixedSum_increment
    {X Y : Finset ℤ} {T : ℕ}
    (hXY : Disjoint X Y) (hXcard : X.card = T)
    (hYcard : Y.card = T) :
    Monotone (fun j : Fin T ↦
      orderedMixedSum X Y T (j + 1) - orderedMixedSum X Y T j) := by
  intro i j hij
  exact orderedMixedSum_increment_mono hXY hXcard hYcard
    (Fin.mk_le_mk.mp hij) j.isLt

end

end Erdos874
