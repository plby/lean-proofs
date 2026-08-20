/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib

/-!
# Symmetric finite sums over the integers

This file packages the elementary signed-to-unsigned reindexing used for the
small integral difference in the Pollington--Vaughan pair count.
-/

namespace Erdos999

open scoped BigOperators

private def negSuccIntEmbedding : ℕ ↪ ℤ where
  toFun t := -(((t + 1 : ℕ) : ℤ))
  inj' := by
    intro a b h
    simp at h
    omega

@[simp] private lemma natAbs_negSuccIntEmbedding (t : ℕ) :
    (negSuccIntEmbedding t).natAbs = t + 1 := by
  change (-((t + 1 : ℕ) : ℤ)).natAbs = t + 1
  rw [Int.natAbs_neg, Int.natAbs_natCast]

@[simp] private lemma natAbs_natCastEmbedding (t : ℕ) :
    (Nat.castEmbedding t : ℤ).natAbs = t := by
  simp

private lemma int_Icc_neg_eq_negSucc_union_cast (K : ℕ) :
    Finset.Icc (-(K : ℤ)) (K : ℤ) =
      (Finset.range K).map negSuccIntEmbedding ∪
        (Finset.range (K + 1)).map Nat.castEmbedding := by
  ext z
  constructor
  · intro hz
    rw [Finset.mem_Icc] at hz
    rw [Finset.mem_union]
    by_cases hzneg : z < 0
    · left
      refine Finset.mem_map.mpr ⟨(-z - 1).toNat, ?_, ?_⟩
      · simp
        have hcast : ((-z).toNat : ℤ) = -z := by
          rw [Int.toNat_of_nonneg]
          omega
        omega
      · simp [negSuccIntEmbedding]
        have hcast : ((-z).toNat : ℤ) = -z := by
          rw [Int.toNat_of_nonneg]
          omega
        omega
    · right
      refine Finset.mem_map.mpr ⟨z.toNat, ?_, ?_⟩
      · simp
        omega
      · simp
        omega
  · intro hz
    rw [Finset.mem_union] at hz
    rw [Finset.mem_Icc]
    rcases hz with hz | hz
    · rcases Finset.mem_map.mp hz with ⟨t, ht, rfl⟩
      simp [negSuccIntEmbedding] at ht ⊢
      omega
    · rcases Finset.mem_map.mp hz with ⟨t, ht, rfl⟩
      simp at ht ⊢
      omega

private lemma disjoint_negSucc_cast (K : ℕ) :
    Disjoint ((Finset.range K).map negSuccIntEmbedding)
      ((Finset.range (K + 1)).map Nat.castEmbedding) := by
  rw [Finset.disjoint_left]
  intro z hzneg hzpos
  rcases Finset.mem_map.mp hzneg with ⟨t, ht, rfl⟩
  rcases Finset.mem_map.mp hzpos with ⟨u, hu, hEq⟩
  simp [negSuccIntEmbedding] at ht hu hEq
  omega

private lemma sum_Ioc_zero_eq_sum_range_succ
    {R : Type*} [AddCommMonoid R] (F : ℕ → R) (K : ℕ) :
    ∑ n ∈ Finset.Ioc 0 K, F n = ∑ t ∈ Finset.range K, F (t + 1) := by
  symm
  refine Finset.sum_bij (fun t _ ↦ t + 1) ?_ ?_ ?_ ?_
  · intro t ht
    simp only [Finset.mem_range, Finset.mem_Ioc] at ht ⊢
    omega
  · intro t₁ ht₁ t₂ ht₂ h
    omega
  · intro n hn
    refine ⟨n - 1, ?_, ?_⟩
    · simp only [Finset.mem_Ioc, Finset.mem_range] at hn ⊢
      omega
    · simp only [Finset.mem_Ioc] at hn
      omega
  · intro t ht
    rfl

/-- An even summand over the symmetric integer interval is its value at zero
plus twice the corresponding sum over positive naturals. -/
theorem sum_Icc_int_natAbs
    {R : Type*} [AddCommMonoid R] (F : ℕ → R) (K : ℕ) :
    ∑ z ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), F z.natAbs =
      F 0 + 2 • (∑ n ∈ Finset.Ioc 0 K, F n) := by
  rw [int_Icc_neg_eq_negSucc_union_cast K,
    Finset.sum_union (disjoint_negSucc_cast K),
    Finset.sum_map, Finset.sum_map]
  simp only [natAbs_negSuccIntEmbedding, natAbs_natCastEmbedding]
  rw [sum_Ioc_zero_eq_sum_range_succ]
  rw [Finset.sum_range_succ]
  have hshift : (∑ x ∈ Finset.range K, F x) + F K =
      F 0 + ∑ x ∈ Finset.range K, F (x + 1) := by
    rw [← Finset.sum_range_succ, Finset.sum_range_succ']
    ac_rfl
  rw [hshift]
  abel

end Erdos999
