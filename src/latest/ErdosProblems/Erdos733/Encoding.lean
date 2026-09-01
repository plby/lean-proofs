/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ErdosProblems.Erdos733.Defs
import ErdosProblems.Erdos733.Counting

/-!
# Erdős Problem 733: encoding compatible sequences

This file connects the geometric definition of compatibility to the generic
dyadic multiset encoding.  The coercion from lists to multisets forgets the
order, but it is injective on compatible sequences because those lists are
canonically sorted.
-/

namespace Erdos733

open Function

noncomputable section

/-- An integer at least two and at most `n` lies in one of the first `n`
dyadic buckets.  The chosen bucket has index `Nat.log2 x - 1`. -/
lemma exists_dyadicBucket_of_two_le_of_le {n x : ℕ} (hx2 : 2 ≤ x) (hxn : x ≤ n) :
    ∃ i : Fin n, InDyadicBucket i x := by
  have hx0 : x ≠ 0 := by omega
  have hlog_pos : 1 ≤ Nat.log2 x := by
    rw [Nat.le_log2 hx0]
    simpa using hx2
  have hindex_lt : Nat.log2 x - 1 < n := by
    have hlog_le_x : Nat.log2 x ≤ x := Nat.log2_le_self x
    omega
  refine ⟨⟨Nat.log2 x - 1, hindex_lt⟩, ?_, ?_⟩
  · rw [dyadicScale, Nat.sub_add_cancel hlog_pos]
    exact Nat.log2_self_le hx0
  · rw [dyadicScale, Nat.sub_add_cancel hlog_pos]
    simpa [Nat.pow_succ, Nat.mul_comm] using (Nat.lt_log2_self (n := x))

/-- Every entry of a compatible sequence on `n` points is supported in the
first `n` dyadic buckets. -/
lemma LineCompatible.supportedInDyadicBuckets {n : ℕ} {X : List ℕ}
    (hX : LineCompatible n X) :
    SupportedInDyadicBuckets n (X : Multiset ℕ) := by
  intro x hx
  have hxX : x ∈ X := Multiset.mem_coe.mp hx
  exact exists_dyadicBucket_of_two_le_of_le (hX.mem_bounds hxX).1 (hX.mem_bounds hxX).2

/-- Regard a compatible sorted sequence as a capped dyadic multiset. -/
def encodeCompatibleSequence {n : ℕ} {cap : Fin n → ℕ}
    (hcap : ∀ (X : List ℕ), LineCompatible n X →
      ∀ i : Fin n, (dyadicBucket i (X : Multiset ℕ)).card ≤ cap i)
    (X : {X : List ℕ // LineCompatible n X}) :
    CappedDyadicMultisets n cap :=
  ⟨(X.1 : Multiset ℕ), X.2.supportedInDyadicBuckets, hcap X.1 X.2⟩

/-- Sorted compatible sequences can be recovered from their underlying
multisets, so the preceding conversion is injective. -/
lemma encodeCompatibleSequence_injective {n : ℕ} {cap : Fin n → ℕ}
    (hcap : ∀ (X : List ℕ), LineCompatible n X →
      ∀ i : Fin n, (dyadicBucket i (X : Multiset ℕ)).card ≤ cap i) :
    Function.Injective (encodeCompatibleSequence hcap) := by
  intro X Y hXY
  apply Subtype.ext
  have hmultiset : (X.1 : Multiset ℕ) = (Y.1 : Multiset ℕ) := by
    exact congrArg Subtype.val hXY
  have hperm : List.Perm X.1 Y.1 := Multiset.coe_eq_coe.mp hmultiset
  exact hperm.eq_of_pairwise' X.2.sorted Y.2.sorted

/-- Compatible sequences form a finite type whenever all their dyadic
buckets satisfy finite caps.  Recording this explicitly rules out any use
of the zero convention for `Nat.card` on infinite types. -/
theorem finite_compatibleSequences_of_bucket_bounds
    (n : ℕ) (cap : Fin n → ℕ)
    (hcap : ∀ (X : List ℕ), LineCompatible n X →
      ∀ i : Fin n, (dyadicBucket i (X : Multiset ℕ)).card ≤ cap i) :
    Finite {X : List ℕ // LineCompatible n X} := by
  let : Finite (CappedDyadicMultisets n cap) :=
    Finite.of_injective
      (encodeCappedDyadicMultiset (b := n) (cap := cap))
      encodeCappedDyadicMultiset_injective
  exact Finite.of_injective (encodeCompatibleSequence hcap)
    (encodeCompatibleSequence_injective hcap)

/-- Once every dyadic bucket is bounded by `cap`, compatible sequences inject
into the generic product of symmetric powers counted in `Counting.lean`. -/
theorem natCard_compatibleSequences_le_of_bucket_bounds
    (n : ℕ) (cap : Fin n → ℕ)
    (hcap : ∀ (X : List ℕ), LineCompatible n X →
      ∀ i : Fin n, (dyadicBucket i (X : Multiset ℕ)).card ≤ cap i) :
    Nat.card {X : List ℕ // LineCompatible n X} ≤
      ∏ i : Fin n, (dyadicScale i + cap i).choose (cap i) := by
  let : Finite (CappedDyadicMultisets n cap) :=
    Finite.of_injective
      (encodeCappedDyadicMultiset (b := n) (cap := cap))
      encodeCappedDyadicMultiset_injective
  calc
    Nat.card {X : List ℕ // LineCompatible n X} ≤
        Nat.card (CappedDyadicMultisets n cap) :=
      Nat.card_le_card_of_injective (encodeCompatibleSequence hcap)
        (encodeCompatibleSequence_injective hcap)
    _ ≤ ∏ i : Fin n, (dyadicScale i + cap i).choose (cap i) :=
      natCard_cappedDyadicMultisets_le n cap

end

end Erdos733
