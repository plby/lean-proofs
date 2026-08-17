/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, ChatGPT
-/

import ErdosProblems.Erdos543.LowRankCount

/-!
# Incidence matrices of ordered nonempty subsets

This file packages the exact finite combinatorics used when the
inclusion--exclusion expansion in the Ma--Tang proof is grouped according to
the rational rank of an incidence matrix.  An element of
`Fin r ↪ NonemptyIndexSet k` is an ordered list of `r` *distinct* nonempty
subsets of `Fin k`.  Its incidence matrix has those characteristic vectors as
its rows.

The central result is an equivalence between these embeddings and rational
Boolean matrices whose rows are nonzero and pairwise distinct.  Restricting
the equivalence to any rational-rank stratum gives an exact cardinality
identity with `orderedDistinctRowLowRankMatrices` from `LowRankCount`.
-/

open scoped BigOperators
open Finset

namespace Erdos543

attribute [local instance] Classical.propDecidable

/-! ## Nonempty subsets and their incidence matrices -/

/-- A nonempty subset of the coordinate set `Fin k`. -/
abbrev NonemptyIndexSet (k : ℕ) := {S : Finset (Fin k) // S.Nonempty}

/-- The number of nonempty subsets of a `k`-element coordinate set. -/
@[simp] theorem card_nonemptyIndexSet (k : ℕ) :
    Fintype.card (NonemptyIndexSet k) = 2 ^ k - 1 := by
  classical
  rw [Fintype.card_subtype]
  change ((Finset.univ : Finset (Finset (Fin k))).filter Finset.Nonempty).card = _
  rw [show (Finset.univ : Finset (Finset (Fin k))).filter Finset.Nonempty =
      (Finset.univ : Finset (Finset (Fin k))).erase ∅ by
    ext S
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
    exact ⟨fun h ↦ ⟨Finset.nonempty_iff_ne_empty.mp h, trivial⟩,
      fun h ↦ Finset.nonempty_iff_ne_empty.mpr h.1⟩]
  simp [Fintype.card_finset, Fintype.card_fin]

/-- The zero-one incidence matrix of an ordered embedding of distinct
nonempty subsets.  It is defined over any type with distinguished zero and
one, so the same combinatorial matrix can be used over `ℤ`, `ℚ`, and
`ZMod p`. -/
def incidenceMatrix {R : Type*} [Zero R] [One R] {r k : ℕ}
    (ι : Fin r ↪ NonemptyIndexSet k) : Matrix (Fin r) (Fin k) R :=
  fun i j ↦ if j ∈ (ι i : Finset (Fin k)) then 1 else 0

@[simp] theorem incidenceMatrix_apply {R : Type*} [Zero R] [One R]
    {r k : ℕ} (ι : Fin r ↪ NonemptyIndexSet k) (i : Fin r) (j : Fin k) :
    incidenceMatrix (R := R) ι i j =
      if j ∈ (ι i : Finset (Fin k)) then 1 else 0 :=
  rfl

@[simp] theorem incidenceMatrix_apply_of_mem {R : Type*} [Zero R] [One R]
    {r k : ℕ} (ι : Fin r ↪ NonemptyIndexSet k) (i : Fin r) (j : Fin k)
    (hj : j ∈ (ι i : Finset (Fin k))) :
    incidenceMatrix (R := R) ι i j = 1 := by
  simp [incidenceMatrix, hj]

@[simp] theorem incidenceMatrix_apply_of_notMem {R : Type*} [Zero R] [One R]
    {r k : ℕ} (ι : Fin r ↪ NonemptyIndexSet k) (i : Fin r) (j : Fin k)
    (hj : j ∉ (ι i : Finset (Fin k))) :
    incidenceMatrix (R := R) ι i j = 0 := by
  simp [incidenceMatrix, hj]

/-- Incidence matrices commute with a homomorphism preserving zero and one. -/
@[simp] theorem incidenceMatrix_map {R S : Type*} [Semiring R] [Semiring S]
    (f : R →+* S) {r k : ℕ} (ι : Fin r ↪ NonemptyIndexSet k) :
    (incidenceMatrix (R := R) ι).map f = incidenceMatrix (R := S) ι := by
  ext i j
  by_cases h : j ∈ (ι i : Finset (Fin k)) <;> simp [incidenceMatrix, h]

/-- Every incidence entry is zero or one. -/
theorem incidenceMatrix_zero_or_one {R : Type*} [Zero R] [One R]
    {r k : ℕ} (ι : Fin r ↪ NonemptyIndexSet k) (i : Fin r) (j : Fin k) :
    incidenceMatrix (R := R) ι i j = 0 ∨ incidenceMatrix (R := R) ι i j = 1 := by
  by_cases h : j ∈ (ι i : Finset (Fin k))
  · exact Or.inr (incidenceMatrix_apply_of_mem ι i j h)
  · exact Or.inl (incidenceMatrix_apply_of_notMem ι i j h)

/-- A nonempty subset gives a nonzero incidence row. -/
theorem incidenceMatrix_row_nonzero {R : Type*} [Semiring R]
    [Nontrivial R] {r k : ℕ} (ι : Fin r ↪ NonemptyIndexSet k) (i : Fin r) :
    ∃ j, incidenceMatrix (R := R) ι i j ≠ 0 := by
  obtain ⟨j, hj⟩ := (ι i).property
  exact ⟨j, by simp [incidenceMatrix, hj, one_ne_zero]⟩

/-- Equality of incidence rows recovers equality of the underlying subsets. -/
theorem eq_of_incidenceMatrix_row_eq {R : Type*} [Semiring R]
    [Nontrivial R] {r k : ℕ} {ι : Fin r ↪ NonemptyIndexSet k} {i i' : Fin r}
    (h : (fun j ↦ incidenceMatrix (R := R) ι i j) =
      fun j ↦ incidenceMatrix (R := R) ι i' j) :
    ι i = ι i' := by
  apply Subtype.ext
  apply Finset.ext
  intro j
  have hj := congrFun h j
  by_cases hi : j ∈ (ι i : Finset (Fin k)) <;>
    by_cases hi' : j ∈ (ι i' : Finset (Fin k)) <;>
      simp [incidenceMatrix, hi, hi', zero_ne_one, one_ne_zero] at hj ⊢

/-- The ordered incidence rows are pairwise distinct. -/
theorem incidenceMatrix_rows_injective {R : Type*} [Semiring R]
    [Nontrivial R] {r k : ℕ} (ι : Fin r ↪ NonemptyIndexSet k) :
    Function.Injective (fun i j ↦ incidenceMatrix (R := R) ι i j) := by
  intro i i' h
  exact ι.injective (eq_of_incidenceMatrix_row_eq h)

/-- Incidence matrices satisfy the row condition used by the low-rank count. -/
theorem incidenceMatrix_rowsDistinctNonzero {r k : ℕ}
    (ι : Fin r ↪ NonemptyIndexSet k) :
    RowsDistinctNonzero (incidenceMatrix (R := ℚ) ι) :=
  ⟨incidenceMatrix_row_nonzero ι, incidenceMatrix_rows_injective ι⟩

/-- The incidence-matrix construction is injective. -/
theorem incidenceMatrix_injective {R : Type*} [Semiring R] [Nontrivial R]
    {r k : ℕ} : Function.Injective
      (incidenceMatrix (R := R) :
        (Fin r ↪ NonemptyIndexSet k) → Matrix (Fin r) (Fin k) R) := by
  intro ι κ h
  apply Function.Embedding.ext
  intro i
  apply Subtype.ext
  apply Finset.ext
  intro j
  have hj := congr_fun (congr_fun h i) j
  by_cases hι : j ∈ (ι i : Finset (Fin k)) <;>
    by_cases hκ : j ∈ (κ i : Finset (Fin k)) <;>
      simp [incidenceMatrix, hι, hκ, zero_ne_one, one_ne_zero] at hj ⊢

/-! ## Recovering the ordered subsets from a Boolean matrix -/

/-- The support of a rational row at the value one. -/
noncomputable def oneSupport {r k : ℕ} (M : Matrix (Fin r) (Fin k) ℚ)
    (i : Fin r) : Finset (Fin k) := by
  classical
  exact Finset.univ.filter fun j ↦ M i j = 1

@[simp] theorem mem_oneSupport {r k : ℕ} (M : Matrix (Fin r) (Fin k) ℚ)
    (i : Fin r) (j : Fin k) :
    j ∈ oneSupport M i ↔ M i j = 1 := by
  classical
  simp [oneSupport]

/-- A nonzero Boolean row has nonempty one-support. -/
theorem oneSupport_nonempty_of_boolean_of_nonzero {r k : ℕ}
    {M : Matrix (Fin r) (Fin k) ℚ}
    (hbool : ∀ i j, M i j = 0 ∨ M i j = 1)
    (hnonzero : ∀ i, ∃ j, M i j ≠ 0) (i : Fin r) :
    (oneSupport M i).Nonempty := by
  obtain ⟨j, hj⟩ := hnonzero i
  refine ⟨j, (mem_oneSupport M i j).2 ?_⟩
  rcases hbool i j with hzero | hone
  · exact False.elim (hj hzero)
  · exact hone

/-- A Boolean row is exactly the characteristic vector of its one-support. -/
theorem boolean_entry_eq_incidence_oneSupport {r k : ℕ}
    {M : Matrix (Fin r) (Fin k) ℚ}
    (hbool : ∀ i j, M i j = 0 ∨ M i j = 1) (i : Fin r) (j : Fin k) :
    M i j = (if j ∈ oneSupport M i then 1 else 0) := by
  rcases hbool i j with hzero | hone
  · simp [hzero]
  · simp [hone]

/-- Equal one-supports of Boolean rows imply equal rows. -/
theorem row_eq_of_oneSupport_eq {r k : ℕ}
    {M : Matrix (Fin r) (Fin k) ℚ}
    (hbool : ∀ i j, M i j = 0 ∨ M i j = 1) {i i' : Fin r}
    (h : oneSupport M i = oneSupport M i') :
    (fun j ↦ M i j) = fun j ↦ M i' j := by
  funext j
  rw [boolean_entry_eq_incidence_oneSupport hbool i j,
    boolean_entry_eq_incidence_oneSupport hbool i' j, h]

/-- Recover the embedding of nonempty row supports from a Boolean matrix with
distinct nonzero rows. -/
noncomputable def matrixRowsEmbedding {r k : ℕ}
    (M : Matrix (Fin r) (Fin k) ℚ)
    (hbool : ∀ i j, M i j = 0 ∨ M i j = 1)
    (hrows : RowsDistinctNonzero M) : Fin r ↪ NonemptyIndexSet k where
  toFun i := ⟨oneSupport M i,
    oneSupport_nonempty_of_boolean_of_nonzero hbool hrows.1 i⟩
  inj' := by
    intro i i' h
    apply hrows.2
    apply row_eq_of_oneSupport_eq hbool
    exact congrArg Subtype.val h

@[simp] theorem incidenceMatrix_matrixRowsEmbedding {r k : ℕ}
    (M : Matrix (Fin r) (Fin k) ℚ)
    (hbool : ∀ i j, M i j = 0 ∨ M i j = 1)
    (hrows : RowsDistinctNonzero M) :
    incidenceMatrix (R := ℚ) (matrixRowsEmbedding M hbool hrows) = M := by
  ext i j
  symm
  exact boolean_entry_eq_incidence_oneSupport hbool i j

@[simp] theorem matrixRowsEmbedding_incidenceMatrix {r k : ℕ}
    (ι : Fin r ↪ NonemptyIndexSet k) :
    matrixRowsEmbedding (incidenceMatrix (R := ℚ) ι)
      (incidenceMatrix_zero_or_one ι) (incidenceMatrix_rowsDistinctNonzero ι) = ι := by
  apply Function.Embedding.ext
  intro i
  apply Subtype.ext
  apply Finset.ext
  intro j
  change j ∈ oneSupport (incidenceMatrix (R := ℚ) ι) i ↔
    j ∈ (ι i : Finset (Fin k))
  rw [mem_oneSupport]
  simp [incidenceMatrix]

/-! ## Exact equivalence and rational-rank strata -/

/-- Rational Boolean matrices with ordered, pairwise distinct nonzero rows. -/
noncomputable def orderedDistinctRowBooleanMatrices (r k : ℕ) :
    Finset (Matrix (Fin r) (Fin k) ℚ) := by
  classical
  exact (matricesWithColumns (k := k) (booleanVectors r)).filter RowsDistinctNonzero

@[simp] theorem mem_orderedDistinctRowBooleanMatrices {r k : ℕ}
    {M : Matrix (Fin r) (Fin k) ℚ} :
    M ∈ orderedDistinctRowBooleanMatrices r k ↔
      (∀ i j, M i j = 0 ∨ M i j = 1) ∧ RowsDistinctNonzero M := by
  classical
  simp only [orderedDistinctRowBooleanMatrices, Finset.mem_filter,
    mem_matricesWithColumns, mem_booleanVectors]
  constructor
  · rintro ⟨h, hrows⟩
    exact ⟨fun i j ↦ h j i, hrows⟩
  · rintro ⟨h, hrows⟩
    exact ⟨fun j i ↦ h i j, hrows⟩

/-- Ordered embeddings of distinct nonempty subsets are exactly Boolean
matrices with ordered, pairwise distinct nonzero rows. -/
noncomputable def incidenceEmbeddingEquiv (r k : ℕ) :
    (Fin r ↪ NonemptyIndexSet k) ≃
      {M : Matrix (Fin r) (Fin k) ℚ // M ∈ orderedDistinctRowBooleanMatrices r k} where
  toFun ι := ⟨incidenceMatrix (R := ℚ) ι, by
    rw [mem_orderedDistinctRowBooleanMatrices]
    exact ⟨incidenceMatrix_zero_or_one ι, incidenceMatrix_rowsDistinctNonzero ι⟩⟩
  invFun M := matrixRowsEmbedding M
    (by
      have hM := M.property
      rw [mem_orderedDistinctRowBooleanMatrices] at hM
      exact hM.1)
    (by
      have hM := M.property
      rw [mem_orderedDistinctRowBooleanMatrices] at hM
      exact hM.2)
  left_inv ι := matrixRowsEmbedding_incidenceMatrix ι
  right_inv M := by
    apply Subtype.ext
    apply incidenceMatrix_matrixRowsEmbedding

/-- Rational rank of an ordered incidence pattern. -/
noncomputable def incidenceRank {r k : ℕ}
    (ι : Fin r ↪ NonemptyIndexSet k) : ℕ :=
  rationalColumnRank (incidenceMatrix (R := ℚ) ι)

/-- The custom column-span definition of incidence rank agrees with
Mathlib's matrix rank. -/
theorem incidenceRank_eq_matrix_rank {r k : ℕ}
    (ι : Fin r ↪ NonemptyIndexSet k) :
    incidenceRank ι = (incidenceMatrix (R := ℚ) ι).rank := by
  rw [incidenceRank, rationalColumnRank, rationalColumnSpan,
    Matrix.rank_eq_finrank_span_cols]
  congr 2

/-- The finite stratum of ordered incidence patterns of rational rank `d`. -/
noncomputable def incidenceEmbeddingsOfRank (r k d : ℕ) :
    Finset (Fin r ↪ NonemptyIndexSet k) := by
  classical
  exact Finset.univ.filter fun ι ↦ incidenceRank ι = d

@[simp] theorem mem_incidenceEmbeddingsOfRank {r k d : ℕ}
    {ι : Fin r ↪ NonemptyIndexSet k} :
    ι ∈ incidenceEmbeddingsOfRank r k d ↔ incidenceRank ι = d := by
  classical
  simp [incidenceEmbeddingsOfRank]

/-- The rational rank of an `r`-row incidence pattern is at most `r`. -/
theorem incidenceRank_le_rows {r k : ℕ}
    (ι : Fin r ↪ NonemptyIndexSet k) : incidenceRank ι ≤ r := by
  rw [incidenceRank, rationalColumnRank]
  calc
    Module.finrank ℚ (rationalColumnSpan (incidenceMatrix (R := ℚ) ι)) ≤
        Module.finrank ℚ (Fin r → ℚ) :=
      (rationalColumnSpan (incidenceMatrix (R := ℚ) ι)).finrank_le
    _ = r := by simp

/-- Reassociate the two conditions defining a rank-`d`, distinct-nonzero-row
Boolean matrix. -/
noncomputable def rankedOrderedRowMatrixEquiv (r k d : ℕ) :
    { M : {M : Matrix (Fin r) (Fin k) ℚ //
        M ∈ orderedDistinctRowBooleanMatrices r k} //
      rationalColumnRank M.1 = d } ≃
      { M : Matrix (Fin r) (Fin k) ℚ //
        M ∈ orderedDistinctRowLowRankMatrices r d k } where
  toFun M := ⟨M.1.1, by
    have hbase := M.1.2
    rw [mem_orderedDistinctRowBooleanMatrices] at hbase
    simp only [orderedDistinctRowLowRankMatrices, Finset.mem_filter,
      mem_booleanMatricesOfRank]
    exact ⟨⟨fun j ↦ mem_booleanVectors.mpr (fun i ↦ hbase.1 i j), M.2⟩,
      hbase.2⟩⟩
  invFun M := by
    have hlow := M.2
    simp only [orderedDistinctRowLowRankMatrices, Finset.mem_filter,
      mem_booleanMatricesOfRank] at hlow
    exact ⟨⟨M.1, mem_orderedDistinctRowBooleanMatrices.mpr
      ⟨fun i j ↦ (mem_booleanVectors.mp (hlow.1.1 j)) i, hlow.2⟩⟩, hlow.1.2⟩
  left_inv M := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv M := by
    apply Subtype.ext
    rfl

/-- Restricting the exact incidence equivalence to a rank stratum. -/
noncomputable def incidenceRankEquiv (r k d : ℕ) :
    { ι : Fin r ↪ NonemptyIndexSet k // incidenceRank ι = d } ≃
      { M : Matrix (Fin r) (Fin k) ℚ //
        M ∈ orderedDistinctRowLowRankMatrices r d k } :=
  ((incidenceEmbeddingEquiv r k).subtypeEquiv fun ι ↦ by
    change incidenceRank ι = d ↔
      rationalColumnRank (incidenceMatrix (R := ℚ) ι) = d
    rfl).trans (rankedOrderedRowMatrixEquiv r k d)

/-- Exact equality between the number of incidence patterns of rank `d` and
the matrix class estimated in `LowRankCount`. -/
theorem card_incidenceEmbeddingsOfRank_eq (r k d : ℕ) :
    (incidenceEmbeddingsOfRank r k d).card =
      (orderedDistinctRowLowRankMatrices r d k).card := by
  classical
  have hcard := Fintype.card_congr (incidenceRankEquiv r k d)
  simpa only [Fintype.card_subtype, incidenceEmbeddingsOfRank,
    Fintype.card_coe] using hcard

/-- Every low-rank matrix count from `LowRankCount` transfers verbatim to
incidence patterns. -/
theorem card_incidenceEmbeddingsOfRank_le
    (r k d B : ℕ)
    (hinter : ∀ W ∈ generatedSpans (K := ℚ) (booleanVectors r) d,
      ((booleanVectors r).filter (fun v ↦ v ∈ W)).card ≤ B) :
    (incidenceEmbeddingsOfRank r k d).card ≤ 2 ^ (r * d) * B ^ k := by
  rw [card_incidenceEmbeddingsOfRank_eq]
  exact card_orderedDistinctRowLowRankMatrices_le r d k B hinter

/-- Unconditional coarse count for a rational-rank stratum. -/
theorem card_incidenceEmbeddingsOfRank_le_coarse (r k d : ℕ) :
    (incidenceEmbeddingsOfRank r k d).card ≤
      2 ^ (r * d) * 2 ^ (r * k) := by
  rw [card_incidenceEmbeddingsOfRank_eq]
  exact card_orderedDistinctRowLowRankMatrices_le_coarse r d k

/-- The standard `2^(r²) (2^d)^k` form, conditional on a `2^d`
cube-intersection estimate. -/
theorem card_incidenceEmbeddingsOfRank_le_trivial
    (r k d : ℕ) (hdr : d ≤ r)
    (hinter : ∀ W ∈ generatedSpans (K := ℚ) (booleanVectors r) d,
      ((booleanVectors r).filter (fun v ↦ v ∈ W)).card ≤ 2 ^ d) :
    (incidenceEmbeddingsOfRank r k d).card ≤
      2 ^ (r * r) * (2 ^ d) ^ k := by
  rw [card_incidenceEmbeddingsOfRank_eq]
  exact card_orderedDistinctRowLowRankMatrices_le_trivial r d k hdr hinter

/-- The rank strata partition every ordered incidence pattern exactly. -/
theorem sum_card_incidenceEmbeddingsOfRank (r k : ℕ) :
    ∑ d ∈ Finset.range (r + 1), (incidenceEmbeddingsOfRank r k d).card =
      (2 ^ k - 1).descFactorial r := by
  classical
  let allPatterns : Finset (Fin r ↪ NonemptyIndexSet k) := Finset.univ
  let rankRange : Finset ℕ := Finset.range (r + 1)
  have hpartition :
      ∑ d ∈ rankRange, (incidenceEmbeddingsOfRank r k d).card =
        (allPatterns.filter (fun ι ↦ incidenceRank ι ∈ rankRange)).card := by
    simpa only [allPatterns, rankRange, incidenceEmbeddingsOfRank] using
      (Finset.sum_card_fiberwise_eq_card_filter
        (Finset.univ : Finset (Fin r ↪ NonemptyIndexSet k))
        (Finset.range (r + 1)) incidenceRank)
  have hall :
      allPatterns.filter (fun ι ↦ incidenceRank ι ∈ rankRange) = allPatterns := by
    apply Finset.filter_eq_self.2
    intro ι hι
    simp only [rankRange, Finset.mem_range]
    exact Nat.lt_succ_iff.mpr (incidenceRank_le_rows ι)
  have hcard : Fintype.card (Fin r ↪ NonemptyIndexSet k) =
      (2 ^ k - 1).descFactorial r := by
    have h := Fintype.card_embedding_eq
      (α := Fin r) (β := NonemptyIndexSet k)
    rw [Fintype.card_fin, card_nonemptyIndexSet] at h
    exact h
  rw [show Finset.range (r + 1) = rankRange by rfl, hpartition, hall]
  simpa only [allPatterns, Finset.card_univ] using hcard

/-- Equivalent partition identity directly in terms of the low-rank matrix
classes. -/
theorem sum_card_orderedDistinctRowLowRankMatrices (r k : ℕ) :
    ∑ d ∈ Finset.range (r + 1),
        (orderedDistinctRowLowRankMatrices r d k).card =
      (2 ^ k - 1).descFactorial r := by
  simpa only [card_incidenceEmbeddingsOfRank_eq] using
    sum_card_incidenceEmbeddingsOfRank r k

end Erdos543
