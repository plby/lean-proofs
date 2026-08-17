/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, ChatGPT
-/

import ErdosProblems.Erdos543.LowRankCount

/-!
# Full-rank incidence-pattern counts

The ordered distinct nonzero Boolean `r × k` matrices are partitioned by
their rational rank.  The total count is the descending factorial
`(2^k - 1)_r`.  This file isolates the full-rank stratum, identifies its
exact deficit with the union of all lower-rank strata, and inserts the bounds
from `LowRankCount.lean`.
-/

open scoped BigOperators
open Finset

namespace Erdos543

attribute [local instance] Classical.propDecidable

/-! ## The exact descending-factorial total -/

/-- A Boolean row, represented by membership in the finite Boolean cube. -/
abbrev BooleanRow (k : ℕ) := {v : Fin k → ℚ // v ∈ booleanVectors k}

/-- The all-zero Boolean row. -/
noncomputable def zeroBooleanRow (k : ℕ) : BooleanRow k :=
  ⟨0, by simp⟩

/-- A nonzero Boolean row. -/
abbrev NonzeroBooleanRow (k : ℕ) :=
  {v : BooleanRow k // v ≠ zeroBooleanRow k}

@[simp] theorem card_BooleanRow (k : ℕ) :
    Fintype.card (BooleanRow k) = 2 ^ k := by
  rw [Fintype.card_coe, card_booleanVectors]

@[simp] theorem card_NonzeroBooleanRow (k : ℕ) :
    Fintype.card (NonzeroBooleanRow k) = 2 ^ k - 1 := by
  rw [show Fintype.card (NonzeroBooleanRow k) =
      Fintype.card (BooleanRow k) - 1 by simp [NonzeroBooleanRow]]
  simp

/-- All ordered distinct nonzero Boolean-row matrices, before imposing a
rank condition. -/
noncomputable def allOrderedDistinctRowBooleanMatrices (r k : ℕ) :
    Finset (Matrix (Fin r) (Fin k) ℚ) := by
  classical
  exact (matricesWithColumns (k := k) (booleanVectors r)).filter
    RowsDistinctNonzero

@[simp] theorem mem_allOrderedDistinctRowBooleanMatrices {r k : ℕ}
    {M : Matrix (Fin r) (Fin k) ℚ} :
    M ∈ allOrderedDistinctRowBooleanMatrices r k ↔
      (∀ i j, M i j = 0 ∨ M i j = 1) ∧ RowsDistinctNonzero M := by
  classical
  simp only [allOrderedDistinctRowBooleanMatrices, Finset.mem_filter,
    mem_matricesWithColumns, mem_booleanVectors]
  constructor
  · rintro ⟨h, hrows⟩
    exact ⟨fun i j ↦ h j i, hrows⟩
  · rintro ⟨h, hrows⟩
    exact ⟨fun j i ↦ h i j, hrows⟩

/-- Read the rows of a distinct-nonzero Boolean matrix as an embedding into
the finite type of nonzero Boolean rows. -/
noncomputable def fullRankCountRowsEmbedding {r k : ℕ}
    (M : Matrix (Fin r) (Fin k) ℚ)
    (hbool : ∀ i j, M i j = 0 ∨ M i j = 1)
    (hrows : RowsDistinctNonzero M) : Fin r ↪ NonzeroBooleanRow k where
  toFun i := ⟨⟨fun j ↦ M i j, by
    exact mem_booleanVectors.mpr (hbool i)⟩, by
      intro hz
      obtain ⟨j, hj⟩ := hrows.1 i
      apply hj
      have hfun : (fun j ↦ M i j) = 0 := by
        exact congrArg (fun v : BooleanRow k ↦ (v : Fin k → ℚ)) hz
      exact congrFun hfun j⟩
  inj' := by
    intro i i' h
    apply hrows.2
    exact congrArg (fun v : NonzeroBooleanRow k ↦ (v : Fin k → ℚ)) h

/-- Turn an embedding of ordered nonzero Boolean rows into its matrix. -/
def fullRankCountMatrixOfRows {r k : ℕ}
    (e : Fin r ↪ NonzeroBooleanRow k) : Matrix (Fin r) (Fin k) ℚ :=
  fun i j ↦ (e i).1.1 j

lemma fullRankCountMatrixOfRows_mem {r k : ℕ}
    (e : Fin r ↪ NonzeroBooleanRow k) :
    fullRankCountMatrixOfRows e ∈ allOrderedDistinctRowBooleanMatrices r k := by
  rw [mem_allOrderedDistinctRowBooleanMatrices]
  refine ⟨?_, ?_⟩
  · intro i j
    exact (mem_booleanVectors.mp (e i).1.2) j
  · constructor
    · intro i
      have hne : ((e i : NonzeroBooleanRow k) : Fin k → ℚ) ≠ 0 := by
        intro hz
        apply (e i).2
        apply Subtype.ext
        exact hz
      simpa [fullRankCountMatrixOfRows, Function.ne_iff] using hne
    · intro i i' h
      apply e.injective
      apply Subtype.ext
      apply Subtype.ext
      simpa [fullRankCountMatrixOfRows] using h

/-- Ordered embeddings of nonzero Boolean rows are exactly the matrices in
`allOrderedDistinctRowBooleanMatrices`. -/
noncomputable def fullRankCountRowsEquiv (r k : ℕ) :
    (Fin r ↪ NonzeroBooleanRow k) ≃
      {M : Matrix (Fin r) (Fin k) ℚ //
        M ∈ allOrderedDistinctRowBooleanMatrices r k} where
  toFun e := ⟨fullRankCountMatrixOfRows e, fullRankCountMatrixOfRows_mem e⟩
  invFun M := fullRankCountRowsEmbedding M
    (mem_allOrderedDistinctRowBooleanMatrices.mp M.2).1
    (mem_allOrderedDistinctRowBooleanMatrices.mp M.2).2
  left_inv e := by
    apply Function.Embedding.ext
    intro i
    apply Subtype.ext
    apply Subtype.ext
    simp [fullRankCountMatrixOfRows, fullRankCountRowsEmbedding]
  right_inv M := by
    apply Subtype.ext
    ext i j
    rfl

/-- Exact total count of ordered distinct nonzero Boolean row matrices. -/
theorem card_allOrderedDistinctRowBooleanMatrices (r k : ℕ) :
    (allOrderedDistinctRowBooleanMatrices r k).card =
      (2 ^ k - 1).descFactorial r := by
  have hcard := Fintype.card_congr (fullRankCountRowsEquiv r k)
  rw [Fintype.card_embedding_eq, Fintype.card_fin, card_NonzeroBooleanRow] at hcard
  rw [Fintype.card_coe] at hcard
  exact hcard.symm

/-- Rational column rank is at most the number of rows. -/
theorem rationalColumnRank_le_rows {r k : ℕ}
    (M : Matrix (Fin r) (Fin k) ℚ) : rationalColumnRank M ≤ r := by
  rw [rationalColumnRank]
  calc
    Module.finrank ℚ (rationalColumnSpan M) ≤
        Module.finrank ℚ (Fin r → ℚ) := (rationalColumnSpan M).finrank_le
    _ = r := by simp

/-- A rank stratum is the corresponding fiber inside the total matrix set. -/
theorem orderedDistinctRowLowRankMatrices_eq_filter
    (r d k : ℕ) :
    orderedDistinctRowLowRankMatrices r d k =
      (allOrderedDistinctRowBooleanMatrices r k).filter
        (fun M ↦ rationalColumnRank M = d) := by
  classical
  ext M
  simp only [orderedDistinctRowLowRankMatrices, booleanMatricesOfRank,
    allOrderedDistinctRowBooleanMatrices, Finset.mem_filter,
    mem_matricesWithColumns]
  tauto

/-- The rational-rank strata partition the total matrix class. -/
theorem sum_card_orderedDistinctRowLowRankMatrices_fullRankCount (r k : ℕ) :
    ∑ d ∈ Finset.range (r + 1),
        (orderedDistinctRowLowRankMatrices r d k).card =
      (2 ^ k - 1).descFactorial r := by
  classical
  rw [← card_allOrderedDistinctRowBooleanMatrices r k]
  simp_rw [orderedDistinctRowLowRankMatrices_eq_filter]
  calc
    ∑ d ∈ Finset.range (r + 1),
        ((allOrderedDistinctRowBooleanMatrices r k).filter
          (fun M ↦ rationalColumnRank M = d)).card =
        ((allOrderedDistinctRowBooleanMatrices r k).filter
          (fun M ↦ rationalColumnRank M ∈ Finset.range (r + 1))).card := by
      exact Finset.sum_card_fiberwise_eq_card_filter _ _ rationalColumnRank
    _ = (allOrderedDistinctRowBooleanMatrices r k).card := by
      apply congrArg Finset.card
      apply Finset.filter_eq_self.2
      intro M hM
      exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr (rationalColumnRank_le_rows M))

/-- Number of ordered distinct nonzero Boolean `r × k` matrices having
full rational row rank `r`. -/
noncomputable def fullRankPatternCount (r k : ℕ) : ℕ :=
  (orderedDistinctRowLowRankMatrices r r k).card

/-- Number of ordered distinct nonzero Boolean `r × k` matrices whose
rational rank is strictly less than `r`. -/
noncomputable def rankDeficientPatternCount (r k : ℕ) : ℕ :=
  ∑ d ∈ Finset.range r, (orderedDistinctRowLowRankMatrices r d k).card

/-- The full-rank and rank-deficient strata exactly partition all ordered
distinct nonzero Boolean row families. -/
theorem fullRank_add_rankDeficient_eq_descFactorial (r k : ℕ) :
    fullRankPatternCount r k + rankDeficientPatternCount r k =
      (2 ^ k - 1).descFactorial r := by
  have h := sum_card_orderedDistinctRowLowRankMatrices_fullRankCount r k
  rw [Finset.sum_range_succ] at h
  rw [fullRankPatternCount, rankDeficientPatternCount]
  omega

/-- The exact full-rank count obtained by subtracting the deficient strata. -/
theorem fullRankPatternCount_eq_descFactorial_sub (r k : ℕ) :
    fullRankPatternCount r k =
      (2 ^ k - 1).descFactorial r - rankDeficientPatternCount r k := by
  have h := fullRank_add_rankDeficient_eq_descFactorial r k
  omega

/-- The exact deficit from the descending-factorial total. -/
theorem descFactorial_sub_fullRankPatternCount_eq (r k : ℕ) :
    (2 ^ k - 1).descFactorial r - fullRankPatternCount r k =
      rankDeficientPatternCount r k := by
  have h := fullRank_add_rankDeficient_eq_descFactorial r k
  omega

theorem fullRankPatternCount_le_descFactorial (r k : ℕ) :
    fullRankPatternCount r k ≤ (2 ^ k - 1).descFactorial r := by
  have h := fullRank_add_rankDeficient_eq_descFactorial r k
  omega

/-! ## An unconditional coarse bound -/

/-- Coarse error obtained by using the entire `r`-dimensional Boolean cube
for every column in every deficient rank. -/
def coarseRankDeficientError (r k : ℕ) : ℕ :=
  r * 2 ^ (r * r) * 2 ^ (r * k)

theorem rankDeficientPatternCount_le_coarseError (r k : ℕ) :
    rankDeficientPatternCount r k ≤ coarseRankDeficientError r k := by
  rw [rankDeficientPatternCount, coarseRankDeficientError]
  calc
    (∑ d ∈ Finset.range r,
        (orderedDistinctRowLowRankMatrices r d k).card) ≤
        ∑ d ∈ Finset.range r, 2 ^ (r * d) * 2 ^ (r * k) := by
      apply Finset.sum_le_sum
      intro d hd
      exact card_orderedDistinctRowLowRankMatrices_le_coarse r d k
    _ ≤ ∑ _d ∈ Finset.range r, 2 ^ (r * r) * 2 ^ (r * k) := by
      apply Finset.sum_le_sum
      intro d hd
      apply Nat.mul_le_mul_right
      exact Nat.pow_le_pow_right (by decide : 0 < 2)
        (Nat.mul_le_mul_left r (Nat.le_of_lt (Finset.mem_range.mp hd)))
    _ = r * 2 ^ (r * r) * 2 ^ (r * k) := by
      simp [Nat.mul_assoc]

/-- Hypothesis-free lower bound on the full-rank stratum. -/
theorem descFactorial_sub_coarseError_le_fullRankPatternCount (r k : ℕ) :
    (2 ^ k - 1).descFactorial r - coarseRankDeficientError r k ≤
      fullRankPatternCount r k := by
  have hpart := fullRank_add_rankDeficient_eq_descFactorial r k
  have hlow := rankDeficientPatternCount_le_coarseError r k
  omega

/-- Hypothesis-free upper bound on the descending-factorial deficit. -/
theorem descFactorial_sub_fullRankPatternCount_le_coarseError (r k : ℕ) :
    (2 ^ k - 1).descFactorial r - fullRankPatternCount r k ≤
      coarseRankDeficientError r k := by
  rw [descFactorial_sub_fullRankPatternCount_eq]
  exact rankDeficientPatternCount_le_coarseError r k

/-! ## Bounds with a supplied cube-intersection estimate -/

/-- Sum of the rank-by-rank majorants delivered by `LowRankCount`. -/
noncomputable def rankDeficientMajorant (r k : ℕ) (B : ℕ → ℕ) : ℕ :=
  ∑ d ∈ Finset.range r, 2 ^ (r * d) * (B d) ^ k

/-- A cube-intersection estimate in every deficient rank bounds the entire
rank-deficient count by the sum of the corresponding rank bounds. -/
theorem rankDeficientPatternCount_le_majorant
    (r k : ℕ) (B : ℕ → ℕ)
    (hinter : ∀ d < r,
      ∀ W ∈ generatedSpans (K := ℚ) (booleanVectors r) d,
        ((booleanVectors r).filter (fun v ↦ v ∈ W)).card ≤ B d) :
    rankDeficientPatternCount r k ≤ rankDeficientMajorant r k B := by
  rw [rankDeficientPatternCount, rankDeficientMajorant]
  apply Finset.sum_le_sum
  intro d hd
  exact card_orderedDistinctRowLowRankMatrices_le r d k (B d)
    (hinter d (Finset.mem_range.mp hd))

/-- Explicit lower bound for the full-rank stratum. -/
theorem descFactorial_sub_majorant_le_fullRankPatternCount
    (r k : ℕ) (B : ℕ → ℕ)
    (hinter : ∀ d < r,
      ∀ W ∈ generatedSpans (K := ℚ) (booleanVectors r) d,
        ((booleanVectors r).filter (fun v ↦ v ∈ W)).card ≤ B d) :
    (2 ^ k - 1).descFactorial r - rankDeficientMajorant r k B ≤
      fullRankPatternCount r k := by
  have hpart := fullRank_add_rankDeficient_eq_descFactorial r k
  have hlow := rankDeficientPatternCount_le_majorant r k B hinter
  omega

/-- The deficit from the descending factorial is at most the explicit
rank-by-rank majorant. -/
theorem descFactorial_sub_fullRankPatternCount_le_majorant
    (r k : ℕ) (B : ℕ → ℕ)
    (hinter : ∀ d < r,
      ∀ W ∈ generatedSpans (K := ℚ) (booleanVectors r) d,
        ((booleanVectors r).filter (fun v ↦ v ∈ W)).card ≤ B d) :
    (2 ^ k - 1).descFactorial r - fullRankPatternCount r k ≤
      rankDeficientMajorant r k B := by
  rw [descFactorial_sub_fullRankPatternCount_eq]
  exact rankDeficientPatternCount_le_majorant r k B hinter

/-! ## The standard trivial `2^d` intersection estimate -/

/-- The usual low-rank majorant after bounding a rank-`d` subspace's Boolean
intersection by `2^d` and enlarging `2^(r d)` to `2^(r²)`. -/
noncomputable def trivialRankDeficientMajorant (r k : ℕ) : ℕ :=
  ∑ d ∈ Finset.range r, 2 ^ (r * r) * (2 ^ d) ^ k

theorem rankDeficientPatternCount_le_trivialMajorant
    (r k : ℕ)
    (hinter : ∀ d < r,
      ∀ W ∈ generatedSpans (K := ℚ) (booleanVectors r) d,
        ((booleanVectors r).filter (fun v ↦ v ∈ W)).card ≤ 2 ^ d) :
    rankDeficientPatternCount r k ≤ trivialRankDeficientMajorant r k := by
  rw [rankDeficientPatternCount, trivialRankDeficientMajorant]
  apply Finset.sum_le_sum
  intro d hd
  exact card_orderedDistinctRowLowRankMatrices_le_trivial r d k
    (Nat.le_of_lt (Finset.mem_range.mp hd))
    (hinter d (Finset.mem_range.mp hd))

/-- The rank-by-rank trivial majorant is at most `r` times its largest
possible term. -/
theorem trivialRankDeficientMajorant_le_last (r k : ℕ) :
    trivialRankDeficientMajorant r k ≤
      r * 2 ^ (r * r) * (2 ^ k) ^ (r - 1) := by
  rw [trivialRankDeficientMajorant]
  calc
    (∑ d ∈ Finset.range r, 2 ^ (r * r) * (2 ^ d) ^ k) ≤
        ∑ _d ∈ Finset.range r,
          2 ^ (r * r) * (2 ^ k) ^ (r - 1) := by
      apply Finset.sum_le_sum
      intro d hd
      have hdrlt : d < r := Finset.mem_range.mp hd
      have hdr : d ≤ r - 1 := by omega
      have hpow : (2 ^ d) ^ k ≤ (2 ^ (r - 1)) ^ k :=
        Nat.pow_le_pow_left
          (Nat.pow_le_pow_right (by decide : 0 < 2) hdr) k
      calc
        2 ^ (r * r) * (2 ^ d) ^ k ≤
            2 ^ (r * r) * (2 ^ (r - 1)) ^ k :=
          Nat.mul_le_mul_left _ hpow
        _ = 2 ^ (r * r) * (2 ^ k) ^ (r - 1) := by
          rw [← pow_mul, ← pow_mul, Nat.mul_comm k (r - 1)]
    _ = r * (2 ^ (r * r) * (2 ^ k) ^ (r - 1)) := by simp
    _ = r * 2 ^ (r * r) * (2 ^ k) ^ (r - 1) := by ring

/-- Fully explicit lower bound on the full-rank count. -/
theorem descFactorial_sub_trivialError_le_fullRankPatternCount
    (r k : ℕ)
    (hinter : ∀ d < r,
      ∀ W ∈ generatedSpans (K := ℚ) (booleanVectors r) d,
        ((booleanVectors r).filter (fun v ↦ v ∈ W)).card ≤ 2 ^ d) :
    (2 ^ k - 1).descFactorial r -
        r * 2 ^ (r * r) * (2 ^ k) ^ (r - 1) ≤
      fullRankPatternCount r k := by
  have hpart := fullRank_add_rankDeficient_eq_descFactorial r k
  have hlow := (rankDeficientPatternCount_le_trivialMajorant r k hinter).trans
    (trivialRankDeficientMajorant_le_last r k)
  omega

/-- Fully explicit upper bound on the deficit from the descending-factorial
total. -/
theorem descFactorial_sub_fullRankPatternCount_le_trivialError
    (r k : ℕ)
    (hinter : ∀ d < r,
      ∀ W ∈ generatedSpans (K := ℚ) (booleanVectors r) d,
        ((booleanVectors r).filter (fun v ↦ v ∈ W)).card ≤ 2 ^ d) :
    (2 ^ k - 1).descFactorial r - fullRankPatternCount r k ≤
      r * 2 ^ (r * r) * (2 ^ k) ^ (r - 1) := by
  rw [descFactorial_sub_fullRankPatternCount_eq]
  exact (rankDeficientPatternCount_le_trivialMajorant r k hinter).trans
    (trivialRankDeficientMajorant_le_last r k)

end Erdos543
