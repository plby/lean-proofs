/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import ErdosProblems.Erdos88.Foundations
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.FieldTheory.Finiteness
import Mathlib.Data.Fin.Tuple.Embedding
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Tactic

/-!
# Robust rank tools for Erdős Problem 88

This file contains the finite-matrix part of Section 10 of
Kwan--Sah--Sauermann--Sawhney.  Matrices are viewed over `ℝ`; a binary
matrix therefore means one whose entries are literally zero or one.
-/

open scoped BigOperators

namespace Erdos88
namespace RobustRank

universe u v

/-- A real matrix all of whose entries are zero or one. -/
def IsBinary {ι : Type u} {κ : Type v} (A : Matrix ι κ ℝ) : Prop :=
  ∀ i j, A i j = 0 ∨ A i j = 1

/-- Squared Frobenius norm, in an explicit finite-sum form. -/
noncomputable def frobeniusSq {ι : Type u} {κ : Type v} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℝ) : ℝ :=
  ∑ i, ∑ j, (A i j) ^ 2

/-- Hamming/edit distance between two finite matrices. -/
noncomputable def editDistance {ι : Type u} {κ : Type v} [Fintype ι] [Fintype κ]
    (A B : Matrix ι κ ℝ) : ℕ :=
  ((Finset.univ.product Finset.univ).filter fun p ↦ A p.1 p.2 ≠ B p.1 p.2).card

lemma frobeniusSq_nonneg {ι : Type u} {κ : Type v} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℝ) : 0 ≤ frobeniusSq A := by
  classical
  exact Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

lemma frobeniusSq_eq_zero_iff {ι : Type u} {κ : Type v} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℝ) : frobeniusSq A = 0 ↔ A = 0 := by
  classical
  rw [frobeniusSq]
  constructor
  · intro hsum
    funext i j
    have hi := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i (_ : i ∈ (Finset.univ : Finset ι)) ↦
        Finset.sum_nonneg fun j (_ : j ∈ (Finset.univ : Finset κ)) ↦
          sq_nonneg (A i j))).mp hsum i (Finset.mem_univ i)
    have hij := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j (_ : j ∈ (Finset.univ : Finset κ)) ↦ sq_nonneg (A i j))).mp
        hi j (Finset.mem_univ j)
    simpa using (sq_eq_zero_iff.mp hij)
  · rintro rfl
    simp

/-- A binary matrix has squared Frobenius norm at most its number of cells. -/
lemma frobeniusSq_le_card_mul_card_of_binary
    {ι : Type u} {κ : Type v} [Fintype ι] [Fintype κ]
    {A : Matrix ι κ ℝ} (hA : IsBinary A) :
    frobeniusSq A ≤ (Fintype.card ι : ℝ) * Fintype.card κ := by
  classical
  rw [frobeniusSq]
  calc
    (∑ i, ∑ j, A i j ^ 2) ≤ ∑ _i : ι, ∑ _j : κ, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      rcases hA i j with hij | hij <;> simp [hij]
    _ = (Fintype.card ι : ℝ) * Fintype.card κ := by simp

lemma frobeniusSq_sub_eq_editDistance {ι : Type u} {κ : Type v}
    [Fintype ι] [Fintype κ] {A B : Matrix ι κ ℝ}
    (hA : IsBinary A) (hB : IsBinary B) :
    frobeniusSq (A - B) = editDistance A B := by
  classical
  simp only [frobeniusSq, Matrix.sub_apply]
  calc
    (∑ i, ∑ j, (A i j - B i j) ^ 2) =
        ∑ i, ∑ j, if A i j ≠ B i j then (1 : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rcases hA i j with hAi | hAi <;> rcases hB i j with hBj | hBj <;>
        simp [hAi, hBj]
    _ = ∑ p ∈ Finset.univ.product Finset.univ,
          if A p.1 p.2 ≠ B p.1 p.2 then (1 : ℝ) else 0 := by
      exact (Finset.sum_product
        (Finset.univ : Finset ι) (Finset.univ : Finset κ)
        (fun p ↦ if A p.1 p.2 ≠ B p.1 p.2 then (1 : ℝ) else 0)).symm
    _ = editDistance A B := by
      simp only [editDistance]
      rw [show (((Finset.univ.product Finset.univ).filter fun p ↦
          A p.1 p.2 ≠ B p.1 p.2).card : ℝ) =
          ∑ _p ∈ ((Finset.univ.product Finset.univ).filter fun p ↦
            A p.1 p.2 ≠ B p.1 p.2), (1 : ℝ) by simp]
      rw [Finset.sum_filter]

/-- Coordinate evaluation restricted to a subspace of a finite function space. -/
def coordinateOn {κ : Type v} (W : Submodule ℝ (κ → ℝ)) (j : κ) : W →ₗ[ℝ] ℝ where
  toFun x := x.1 j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private lemma binary_eq_of_decide_eq {a b : ℝ}
    (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1)
    (h : decide (a = 1) = decide (b = 1)) : a = b := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp_all

/-- A finite family of binary vectors spanning a `d`-dimensional real
subspace has at most `2^d` members.  This is the linear-algebraic counting
step behind KSSS Lemma 10.4. -/
lemma card_binary_vectors_le_two_pow_finrank {κ : Type v} [Fintype κ]
    (S : Finset (κ → ℝ))
    (hS : ∀ x ∈ S, ∀ j, x j = 0 ∨ x j = 1) :
    S.card ≤ 2 ^ Module.finrank ℝ (Submodule.span ℝ (S : Set (κ → ℝ))) := by
  classical
  let W : Submodule ℝ (κ → ℝ) := Submodule.span ℝ (S : Set (κ → ℝ))
  let coords : Set (W →ₗ[ℝ] ℝ) := Set.range (coordinateOn W)
  have hcoords : Submodule.span ℝ coords = ⊤ := by
    apply Submodule.span_eq_top_of_ne_zero
    intro z hz
    have hzfun : z.1 ≠ 0 := by
      intro h
      apply hz
      exact Subtype.ext h
    obtain ⟨j, hj⟩ : ∃ j, z.1 j ≠ 0 := by
      by_contra h
      push_neg at h
      exact hzfun (funext h)
    exact ⟨coordinateOn W j, ⟨j, rfl⟩, hj⟩
  obtain ⟨T, hTsub, hTcard, hTspan, hTind⟩ :=
    Submodule.exists_finset_span_eq_linearIndepOn ℝ coords
  have hTtop : Submodule.span ℝ (T : Set (W →ₗ[ℝ] ℝ)) = ⊤ := by
    simpa [hcoords] using hTspan
  choose idx hidx using fun f : T ↦ hTsub f.2
  let code : {x // x ∈ S} → (T → Bool) := fun x f ↦ decide (x.1 (idx f) = 1)
  have hcode : Function.Injective code := by
    intro x y hxy
    apply Subtype.ext
    funext j
    let xW : W := ⟨x.1, Submodule.subset_span x.2⟩
    let yW : W := ⟨y.1, Submodule.subset_span y.2⟩
    have h_on_T : ∀ f : T, f.1 xW = f.1 yW := by
      intro f
      have hbit : decide (x.1 (idx f) = 1) = decide (y.1 (idx f) = 1) := by
        have := congr_fun hxy f
        simpa [code] using this
      have hentry : x.1 (idx f) = y.1 (idx f) :=
        binary_eq_of_decide_eq (hS x.1 x.2 (idx f)) (hS y.1 y.2 (idx f)) hbit
      rw [← hidx f]
      exact hentry
    have hall : ∀ f : W →ₗ[ℝ] ℝ,
        f ∈ Submodule.span ℝ (T : Set (W →ₗ[ℝ] ℝ)) → f xW = f yW := by
      intro f hf
      induction hf using Submodule.span_induction with
      | mem f hf =>
          exact h_on_T ⟨f, hf⟩
      | zero => simp
      | add f g hf hg ihf ihg => simp [ihf, ihg]
      | smul a f hf ih => simp [ih]
    have hjmem : coordinateOn W j ∈ Submodule.span ℝ (T : Set (W →ₗ[ℝ] ℝ)) := by
      rw [hTtop]
      trivial
    simpa [coordinateOn, xW, yW] using hall (coordinateOn W j) hjmem
  have hcard := Fintype.card_le_of_injective code hcode
  have hTcardW : T.card = Module.finrank ℝ W := by
    rw [hcoords, finrank_top, Subspace.dual_finrank_eq] at hTcard
    exact hTcard
  simpa [hTcardW] using hcard

/-- The finite set of row vectors occurring in a matrix. -/
noncomputable def rowTypes {ι : Type u} {κ : Type v} [Fintype ι]
    (A : Matrix ι κ ℝ) : Finset (κ → ℝ) :=
  @Finset.image ι (κ → ℝ) (Classical.decEq (κ → ℝ)) (fun i ↦ A i) Finset.univ

lemma rowTypes_card_le_two_pow_rank {ι : Type u} {κ : Type v}
    [Fintype ι] [Fintype κ] (A : Matrix ι κ ℝ) (hA : IsBinary A) :
    (rowTypes A).card ≤ 2 ^ A.rank := by
  classical
  have h := card_binary_vectors_le_two_pow_finrank (rowTypes A) (by
    intro x hx j
    obtain ⟨i, hix⟩ : ∃ i, A i = x := by
      simpa only [rowTypes, Finset.mem_image, Finset.mem_univ, true_and] using hx
    rw [← hix]
    exact hA i j)
  have hcoe : (↑(rowTypes A) : Set (κ → ℝ)) = Set.range A.row := by
    ext x
    simp only [rowTypes, Finset.mem_coe, Finset.mem_image, Finset.mem_univ, true_and]
    exact Iff.rfl
  rwa [Matrix.rank_eq_finrank_span_row, ← hcoe]

/-- KSSS Lemma 10.4, in its useful coding form.  Fibres of `rowCode` and
`colCode` are the two partitions; every rectangle formed by two fibres is
constant. -/
theorem binary_low_rank_partition (r : ℕ) {ι : Type u} {κ : Type v}
    [Fintype ι] [Fintype κ] (Q : Matrix ι κ ℝ)
    (hQ : IsBinary Q) (hrank : Q.rank ≤ r) :
    ∃ rowCode : ι → Fin (2 ^ r), ∃ colCode : κ → Fin (2 ^ r),
      ∀ ⦃i i' j j'⦄, rowCode i = rowCode i' → colCode j = colCode j' →
        Q i j = Q i' j' := by
  classical
  let R := rowTypes Q
  have hRcard : R.card ≤ 2 ^ r :=
    (rowTypes_card_le_two_pow_rank Q hQ).trans (Nat.pow_le_pow_right (by omega) hrank)
  have hRcard' : Fintype.card R ≤ 2 ^ r := by
    rw [Fintype.card_coe]
    exact hRcard
  let remb : R ↪ Fin (2 ^ r) :=
    (Fintype.equivFin R).toEmbedding.trans (Fin.castLEEmb hRcard')
  have hrowmem (i : ι) : Q i ∈ R := by
    simp only [R, rowTypes, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨i, rfl⟩
  let rowCode : ι → Fin (2 ^ r) := fun i ↦ remb ⟨Q i, hrowmem i⟩
  let QT : Matrix κ ι ℝ := Q.transpose
  have hQT : IsBinary QT := by
    intro j i
    exact hQ i j
  have hrankT : QT.rank ≤ r := by
    simpa [QT, Matrix.rank_transpose] using hrank
  let C := rowTypes QT
  have hCcard : C.card ≤ 2 ^ r :=
    (rowTypes_card_le_two_pow_rank QT hQT).trans
      (Nat.pow_le_pow_right (by omega) hrankT)
  have hCcard' : Fintype.card C ≤ 2 ^ r := by
    rw [Fintype.card_coe]
    exact hCcard
  let cemb : C ↪ Fin (2 ^ r) :=
    (Fintype.equivFin C).toEmbedding.trans (Fin.castLEEmb hCcard')
  have hcolmem (j : κ) : QT j ∈ C := by
    simp only [C, rowTypes, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨j, rfl⟩
  let colCode : κ → Fin (2 ^ r) := fun j ↦ cemb ⟨QT j, hcolmem j⟩
  refine ⟨rowCode, colCode, ?_⟩
  intro i i' j j' hi hj
  have hrows : Q i = Q i' := by
    exact congr_arg Subtype.val (remb.injective hi)
  have hcols : QT j = QT j' := by
    exact congr_arg Subtype.val (cemb.injective hj)
  calc
    Q i j = Q i' j := congr_fun hrows j
    _ = Q i' j' := by simpa [QT] using congr_fun hcols i'

/-! ## Exact Section 10 interfaces -/

/-- The zero-one adjacency matrix of a finite simple graph.  Keeping this
definition local to the robust-rank module prevents an implicit choice of a
matrix norm from entering the graph statement. -/
noncomputable def graphAdjacencyMatrix {V : Type u} (G : SimpleGraph V) :
    Matrix V V ℝ := by
  classical
  exact fun i j ↦ if G.Adj i j then 1 else 0

lemma graphAdjacencyMatrix_isBinary {V : Type u} (G : SimpleGraph V) :
    IsBinary (graphAdjacencyMatrix G) := by
  intro i j
  classical
  by_cases hij : G.Adj i j
  · exact Or.inr (by simp [graphAdjacencyMatrix, hij])
  · exact Or.inl (by simp [graphAdjacencyMatrix, hij])

@[simp] lemma graphAdjacencyMatrix_diag {V : Type u} (G : SimpleGraph V)
    (i : V) : graphAdjacencyMatrix G i i = 0 := by
  classical
  simp [graphAdjacencyMatrix]

/-- Number of red cells in a finite red/green coloring of matrix entries. -/
noncomputable def redCount {ι : Type u} {κ : Type v} [Fintype ι] [Fintype κ]
    (red : ι → κ → Prop) : ℕ := by
  classical
  exact ((Finset.univ.product Finset.univ).filter fun p ↦ red p.1 p.2).card

/-- Red degree of one row. -/
noncomputable def redRowDegree {ι : Type u} {κ : Type v} [Fintype κ]
    (red : ι → κ → Prop) (i : ι) : ℕ := by
  classical
  exact (Finset.univ.filter fun j ↦ red i j).card

/-- Red degree of one column. -/
noncomputable def redColDegree {ι : Type u} {κ : Type v} [Fintype ι]
    (red : ι → κ → Prop) (j : κ) : ℕ := by
  classical
  exact (Finset.univ.filter fun i ↦ red i j).card

lemma redCount_eq_sum_rowDegree
    {ι : Type u} {κ : Type v} [Fintype ι] [Fintype κ]
    (red : ι → κ → Prop) : redCount red = ∑ i, redRowDegree red i := by
  classical
  calc
    redCount red =
        ∑ p ∈ Finset.univ.product Finset.univ,
          if red p.1 p.2 then 1 else 0 := by
      unfold redCount
      rw [Finset.card_filter]
    _ = ∑ i ∈ (Finset.univ : Finset ι), ∑ j ∈ (Finset.univ : Finset κ),
          if red i j then 1 else 0 :=
      Finset.sum_product (Finset.univ : Finset ι) (Finset.univ : Finset κ)
        (fun p ↦ if red p.1 p.2 then 1 else 0)
    _ = ∑ i, redRowDegree red i := by
      apply Finset.sum_congr rfl
      intro i hi
      unfold redRowDegree
      rw [Finset.card_filter]

lemma redCount_eq_sum_colDegree
    {ι : Type u} {κ : Type v} [Fintype ι] [Fintype κ]
    (red : ι → κ → Prop) : redCount red = ∑ j, redColDegree red j := by
  classical
  calc
    redCount red =
        ∑ p ∈ Finset.univ.product Finset.univ,
          if red p.1 p.2 then 1 else 0 := by
      unfold redCount
      rw [Finset.card_filter]
    _ = ∑ i ∈ (Finset.univ : Finset ι), ∑ j ∈ (Finset.univ : Finset κ),
          if red i j then 1 else 0 :=
      Finset.sum_product (Finset.univ : Finset ι) (Finset.univ : Finset κ)
        (fun p ↦ if red p.1 p.2 then 1 else 0)
    _ = ∑ j ∈ (Finset.univ : Finset κ), ∑ i ∈ (Finset.univ : Finset ι),
          if red i j then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ j, redColDegree red j := by
      apply Finset.sum_congr rfl
      intro j hj
      unfold redColDegree
      rw [Finset.card_filter]

/-- There are few rows whose red degree exceeds a threshold. -/
lemma threshold_mul_card_highRedRows_le
    {ι : Type u} {κ : Type v} [Fintype ι] [Fintype κ]
    (red : ι → κ → Prop) {t : ℝ} (ht : 0 ≤ t) :
    (((Finset.univ.filter fun i ↦ t < (redRowDegree red i : ℝ)).card : ℕ) : ℝ) * t ≤
      redCount red := by
  classical
  let high : Finset ι :=
    Finset.univ.filter fun i ↦ t < (redRowDegree red i : ℝ)
  calc
    ((high.card : ℕ) : ℝ) * t = ∑ _i ∈ high, t := by simp
    _ ≤ ∑ i ∈ high, (redRowDegree red i : ℝ) := by
      apply Finset.sum_le_sum
      intro i hi
      exact le_of_lt (Finset.mem_filter.mp hi).2
    _ ≤ ∑ i, (redRowDegree red i : ℝ) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun _ _ _ ↦ Nat.cast_nonneg _)
    _ = redCount red := by
      exact_mod_cast (redCount_eq_sum_rowDegree red).symm

/-- Column version of `threshold_mul_card_highRedRows_le`. -/
lemma threshold_mul_card_highRedCols_le
    {ι : Type u} {κ : Type v} [Fintype ι] [Fintype κ]
    (red : ι → κ → Prop) {t : ℝ} (ht : 0 ≤ t) :
    (((Finset.univ.filter fun j ↦ t < (redColDegree red j : ℝ)).card : ℕ) : ℝ) * t ≤
      redCount red := by
  classical
  let high : Finset κ :=
    Finset.univ.filter fun j ↦ t < (redColDegree red j : ℝ)
  calc
    ((high.card : ℕ) : ℝ) * t = ∑ _j ∈ high, t := by simp
    _ ≤ ∑ j ∈ high, (redColDegree red j : ℝ) := by
      apply Finset.sum_le_sum
      intro j hj
      exact le_of_lt (Finset.mem_filter.mp hj).2
    _ ≤ ∑ j, (redColDegree red j : ℝ) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun _ _ _ ↦ Nat.cast_nonneg _)
    _ = redCount red := by
      exact_mod_cast (redCount_eq_sum_colDegree red).symm

lemma card_highRedRows_lt
    {iota : Type u} {kappa : Type v} [Fintype iota] [Fintype kappa]
    (red : iota → kappa → Prop) {s : ℝ} (hs : 0 < s)
    (hred : (redCount red : ℝ) < s ^ 2) :
    (((Finset.univ.filter fun i ↦
      s < (redRowDegree red i : ℝ)).card : ℕ) : ℝ) < s := by
  have hmul := threshold_mul_card_highRedRows_le red (le_of_lt hs)
  nlinarith

lemma card_highRedCols_lt
    {iota : Type u} {kappa : Type v} [Fintype iota] [Fintype kappa]
    (red : iota → kappa → Prop) {s : ℝ} (hs : 0 < s)
    (hred : (redCount red : ℝ) < s ^ 2) :
    (((Finset.univ.filter fun j ↦
      s < (redColDegree red j : ℝ)).card : ℕ) : ℝ) < s := by
  have hmul := threshold_mul_card_highRedCols_le red (le_of_lt hs)
  nlinarith

/-- The union of all code fibres of size at most `s` has cardinality at
most the number of occurring codes times `s`. -/
lemma card_small_code_fibers_le
    {I C : Type*} [DecidableEq I] [DecidableEq C]
    (S : Finset I) (code : I → C) {s : ℝ} (hs : 0 ≤ s) :
    let types := S.image code
    let smallTypes := types.filter fun c ↦
      ((S.filter fun i ↦ code i = c).card : ℝ) ≤ s
    ((S.filter fun i ↦ code i ∈ smallTypes).card : ℝ) ≤
      (types.card : ℝ) * s := by
  classical
  dsimp only
  let types := S.image code
  let smallTypes := types.filter fun c ↦
    ((S.filter fun i ↦ code i = c).card : ℝ) ≤ s
  have hpartition :
      (S.filter fun i ↦ code i ∈ smallTypes).card =
        ∑ c ∈ smallTypes, (S.filter fun i ↦ code i = c).card := by
    exact (Finset.sum_card_fiberwise_eq_card_filter S smallTypes code).symm
  calc
    ((S.filter fun i ↦ code i ∈ smallTypes).card : ℝ) =
        ∑ c ∈ smallTypes,
          ((S.filter fun i ↦ code i = c).card : ℝ) := by
      exact_mod_cast hpartition
    _ ≤ ∑ _c ∈ smallTypes, s := by
      apply Finset.sum_le_sum
      intro c hc
      exact (Finset.mem_filter.mp hc).2
    _ = (smallTypes.card : ℝ) * s := by simp
    _ ≤ (types.card : ℝ) * s := by
      gcongr
      exact Finset.filter_subset _ _

/-- At most `2^l` Boolean words of length `l` can occur as codes. -/
lemma card_bool_codes_le_two_pow {I : Type*} [DecidableEq I]
    (S : Finset I) {l : ℕ} (code : I → Fin l → Bool) :
    (S.image code).card ≤ 2 ^ l := by
  classical
  calc
    (S.image code).card ≤ Fintype.card (Fin l → Bool) := Finset.card_le_univ _
    _ = 2 ^ l := by simp

/-- If two matrices agree away from the red cells and discarded rows and
columns, their edit distance is bounded by the corresponding union bound. -/
lemma editDistance_le_redCount_add_discard
    {I J : Type*} [Fintype I] [Fintype J]
    (A B : Matrix I J ℝ) (red : I → J → Prop)
    (discardRows : Finset I) (discardCols : Finset J)
    (hagrees : ∀ i j, i ∉ discardRows → j ∉ discardCols →
      ¬ red i j → A i j = B i j) :
    (editDistance A B : ℝ) ≤ (redCount red : ℝ) +
      (discardRows.card : ℝ) * Fintype.card J +
      Fintype.card I * (discardCols.card : ℝ) := by
  classical
  let cells : Finset (I × J) := Finset.univ.product Finset.univ
  let changed : Finset (I × J) :=
    cells.filter fun p ↦ A p.1 p.2 ≠ B p.1 p.2
  let redCells : Finset (I × J) := cells.filter fun p ↦ red p.1 p.2
  let rowCells : Finset (I × J) := discardRows.product Finset.univ
  let colCells : Finset (I × J) := Finset.univ.product discardCols
  have hsubset : changed ⊆ (redCells ∪ rowCells) ∪ colCells := by
    intro p hp
    have hpcells := (Finset.mem_filter.mp hp).1
    have hpne := (Finset.mem_filter.mp hp).2
    by_cases hr : red p.1 p.2
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨hpcells, hr⟩))
    by_cases hi : p.1 ∈ discardRows
    · exact Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_product.mpr ⟨hi, Finset.mem_univ _⟩))
    by_cases hj : p.2 ∈ discardCols
    · exact Finset.mem_union_right _
        (Finset.mem_product.mpr ⟨Finset.mem_univ _, hj⟩)
    exact (hpne (hagrees p.1 p.2 hi hj hr)).elim
  have hcard : changed.card ≤ redCells.card + rowCells.card + colCells.card := by
    calc
      changed.card ≤ ((redCells ∪ rowCells) ∪ colCells).card :=
        Finset.card_le_card hsubset
      _ ≤ (redCells ∪ rowCells).card + colCells.card :=
        Finset.card_union_le (redCells ∪ rowCells) colCells
      _ ≤ (redCells.card + rowCells.card) + colCells.card := by
        gcongr
        exact Finset.card_union_le redCells rowCells
  change (changed.card : ℝ) ≤ _
  calc
    (changed.card : ℝ) ≤
        (redCells.card : ℝ) + rowCells.card + colCells.card := by
      exact_mod_cast hcard
    _ = (redCount red : ℝ) +
        (discardRows.card : ℝ) * Fintype.card J +
        Fintype.card I * (discardCols.card : ℝ) := by
      simp [redCells, rowCells, colCells, redCount, cells]

/-- Markov's inequality for matrix cells, in the form used to create the
red/green coloring in Proposition 10.2. -/
lemma threshold_mul_redCount_le_frobeniusSq
    {ι : Type u} {κ : Type v} [Fintype ι] [Fintype κ]
    (A B : Matrix ι κ ℝ) {τ : ℝ} (hτ : 0 ≤ τ) :
    (redCount (fun i j ↦ τ < (A i j - B i j) ^ 2) : ℝ) * τ ≤
      frobeniusSq (A - B) := by
  classical
  let entries : Finset (ι × κ) := Finset.univ.product Finset.univ
  let red : Finset (ι × κ) :=
    entries.filter fun p ↦ τ < (A p.1 p.2 - B p.1 p.2) ^ 2
  have hfilter : red ⊆ entries := Finset.filter_subset _ _
  calc
    (redCount (fun i j ↦ τ < (A i j - B i j) ^ 2) : ℝ) * τ =
        ∑ _p ∈ red, τ := by simp [redCount, red, entries]
    _ ≤ ∑ p ∈ red, (A p.1 p.2 - B p.1 p.2) ^ 2 := by
      apply Finset.sum_le_sum
      intro p hp
      exact le_of_lt ((Finset.mem_filter.mp hp).2)
    _ ≤ ∑ p ∈ entries, (A p.1 p.2 - B p.1 p.2) ^ 2 := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hfilter
        (fun p _ _ ↦ sq_nonneg (A p.1 p.2 - B p.1 p.2))
    _ = frobeniusSq (A - B) := by
      rw [frobeniusSq]
      simp only [Matrix.sub_apply]
      exact (Finset.sum_product
        (Finset.univ : Finset ι) (Finset.univ : Finset κ)
        (fun p ↦ (A p.1 p.2 - B p.1 p.2) ^ 2)).trans rfl

/-- Every all-green square minor of order `r+1` is singular.  This is the
hypothesis to which the determinant-separation argument reduces
Proposition 10.2. -/
def AllGreenMinorSingular {n : ℕ} (r : ℕ) (A : Matrix (Fin n) (Fin n) ℝ)
    (red : Fin n → Fin n → Prop) : Prop :=
  ∀ rows cols : Fin (r + 1) ↪ Fin n,
    (∀ i j, ¬ red (rows i) (cols j)) → (A.submatrix rows cols).det = 0

/-- Existence of a nonsingular all-green square minor of a prescribed
order. -/
def HasGreenNonsingularMinor {n : ℕ} (l : ℕ)
    (A : Matrix (Fin n) (Fin n) ℝ) (red : Fin n → Fin n → Prop) : Prop :=
  ∃ rows cols : Fin l ↪ Fin n,
    (∀ i j, ¬ red (rows i) (cols j)) ∧ (A.submatrix rows cols).det ≠ 0

/-- A maximal all-green nonsingular minor exists.  This is the finite
choice step at the start of the proof of Lemma 10.3. -/
lemma exists_maximal_greenNonsingularMinor
    {n : ℕ} (r : ℕ) (A : Matrix (Fin n) (Fin n) ℝ)
    (red : Fin n → Fin n → Prop) :
    ∃ l : ℕ, l ≤ r ∧ HasGreenNonsingularMinor l A red ∧
      ∀ k : ℕ, l < k → k ≤ r → ¬ HasGreenNonsingularMinor k A red := by
  classical
  let P : ℕ → Prop := fun l ↦ HasGreenNonsingularMinor l A red
  have hPzero : P 0 := by
    let e : Fin 0 ↪ Fin n := Fin.castLEEmb (Nat.zero_le n)
    refine ⟨e, e, ?_, ?_⟩
    · intro i
      exact Fin.elim0 i
    · simp
  let l := Nat.findGreatest P r
  refine ⟨l, Nat.findGreatest_le r,
    Nat.findGreatest_spec (P := P) (Nat.zero_le r) hPzero, ?_⟩
  intro k hlk hkr
  exact Nat.findGreatest_is_greatest (P := P) hlk hkr

/-- A maximal nonsingular all-green core whose selected rows and columns
also satisfy prescribed side conditions.  Searching only through orders at
most `r` keeps the finite maximization independent of the singularity
hypothesis; the order-`r+1` case is discharged afterwards. -/
private lemma exists_maximal_good_green_core
    {n r : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (red : Fin n → Fin n → Prop) (goodRow goodCol : Fin n → Prop)
    (hsingular : AllGreenMinorSingular r A red) :
    ∃ l : ℕ, l ≤ r ∧ ∃ rows cols : Fin l ↪ Fin n,
      (∀ a, goodRow (rows a)) ∧ (∀ b, goodCol (cols b)) ∧
      (∀ a b, ¬ red (rows a) (cols b)) ∧
      (A.submatrix rows cols).det ≠ 0 ∧
      ∀ rows' cols' : Fin (l + 1) ↪ Fin n,
        (∀ a, goodRow (rows' a)) → (∀ b, goodCol (cols' b)) →
        (∀ a b, ¬ red (rows' a) (cols' b)) →
          (A.submatrix rows' cols').det = 0 := by
  classical
  let P : ℕ → Prop := fun k ↦ ∃ rows cols : Fin k ↪ Fin n,
    (∀ a, goodRow (rows a)) ∧ (∀ b, goodCol (cols b)) ∧
    (∀ a b, ¬ red (rows a) (cols b)) ∧
    (A.submatrix rows cols).det ≠ 0
  have hPzero : P 0 := by
    let e : Fin 0 ↪ Fin n := Fin.castLEEmb (Nat.zero_le n)
    refine ⟨e, e, ?_, ?_, ?_, ?_⟩
    · intro a
      exact Fin.elim0 a
    · intro b
      exact Fin.elim0 b
    · intro a
      exact Fin.elim0 a
    · simp
  let l := Nat.findGreatest P r
  have hlr : l ≤ r := Nat.findGreatest_le r
  have hPl : P l :=
    Nat.findGreatest_spec (P := P) (Nat.zero_le r) hPzero
  obtain ⟨rows, cols, hrows, hcols, hgreen, hdet⟩ := hPl
  refine ⟨l, hlr, rows, cols, hrows, hcols, hgreen, hdet, ?_⟩
  intro rows' cols' hrows' hcols' hgreen'
  by_cases hl : l < r
  · by_contra hdet'
    have hPnext : P (l + 1) :=
      ⟨rows', cols', hrows', hcols', hgreen', hdet'⟩
    exact (Nat.findGreatest_is_greatest (P := P) (Nat.lt_succ_self l)
      (by omega)) hPnext
  · have hlEq : l = r := by omega
    let e : Fin (r + 1) ≃ Fin (l + 1) := finCongr (by omega)
    let rowsR : Fin (r + 1) ↪ Fin n := e.toEmbedding.trans rows'
    let colsR : Fin (r + 1) ↪ Fin n := e.toEmbedding.trans cols'
    have hgreenR : ∀ a b, ¬ red (rowsR a) (colsR b) := by
      intro a b
      exact hgreen' (e a) (e b)
    have hdetR := hsingular rowsR colsR hgreenR
    have hreindex :
        A.submatrix rowsR colsR =
          (A.submatrix rows' cols').submatrix e e := by
      ext a b
      rfl
    rw [hreindex, Matrix.det_submatrix_equiv_self] at hdetR
    exact hdetR

/-- Algebraic heart of the maximal-core argument.  If adjoining one new
row and one new column to an invertible core produces a singular matrix,
then the new corner is the value predicted by the Schur complement. -/
private lemma corner_eq_schur_of_snoc_det_eq_zero
    {n l : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (rows cols : Fin l ↪ Fin n) (i j : Fin n)
    (hi : i ∉ Set.range rows) (hj : j ∉ Set.range cols)
    (hcore : (A.submatrix rows cols).det ≠ 0)
    (hext : (A.submatrix (Fin.Embedding.snoc rows hi)
      (Fin.Embedding.snoc cols hj)).det = 0) :
    A i j =
      ((A.submatrix (fun _ : Fin 1 ↦ i) cols) *
        (A.submatrix rows cols)⁻¹ *
        (A.submatrix rows (fun _ : Fin 1 ↦ j))) 0 0 := by
  classical
  let K : Matrix (Fin l) (Fin l) ℝ := A.submatrix rows cols
  let B : Matrix (Fin l) (Fin 1) ℝ := A.submatrix rows (fun _ ↦ j)
  let C : Matrix (Fin 1) (Fin l) ℝ := A.submatrix (fun _ ↦ i) cols
  let D : Matrix (Fin 1) (Fin 1) ℝ := A.submatrix (fun _ ↦ i) (fun _ ↦ j)
  let E : Matrix (Fin (l + 1)) (Fin (l + 1)) ℝ :=
    A.submatrix (Fin.Embedding.snoc rows hi) (Fin.Embedding.snoc cols hj)
  have hblock :
      E.submatrix finSumFinEquiv finSumFinEquiv = Matrix.fromBlocks K B C D := by
    ext x y
    rcases x with x | x <;> rcases y with y | y
    · simp [E, K, Fin.Embedding.snoc, Fin.snoc]
    · fin_cases y
      simp [E, B, Fin.Embedding.snoc, Fin.snoc]
    · fin_cases x
      simp [E, C, Fin.Embedding.snoc, Fin.snoc]
    · fin_cases x
      fin_cases y
      simp [E, D, Fin.Embedding.snoc, Fin.snoc]
  have hdetblock : (Matrix.fromBlocks K B C D).det = 0 := by
    rw [← hblock, Matrix.det_submatrix_equiv_self]
    exact hext
  have hunit : IsUnit K.det := isUnit_iff_ne_zero.mpr hcore
  let : Invertible K := Matrix.invertibleOfIsUnitDet K hunit
  have hschur : (D - C * ⅟K * B).det = 0 := by
    rw [Matrix.det_fromBlocks₁₁ K B C D] at hdetblock
    exact (mul_eq_zero.mp hdetblock).resolve_left hcore
  have hentry : D 0 0 = (C * ⅟K * B) 0 0 := by
    have hsub : D 0 0 - (C * ⅟K * B) 0 0 = 0 := by
      simpa [Matrix.det_fin_one] using hschur
    exact sub_eq_zero.mp hsub
  simpa [K, B, C, D, Matrix.invOf_eq_nonsing_inv] using hentry

/-- A quantitative determinant-separation constant for binary minors of a
fixed order.  It says that a binary minor entrywise `τ`-close to a matrix
of rank at most `r` must already be singular.  Its dimension is fixed by
`r`, so the constant is independent of the ambient order. -/
def BinaryMinorSeparationAt (r : ℕ) (τ : ℝ) : Prop :=
  0 < τ ∧ ∀ (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℝ),
    IsBinary A → B.rank ≤ r →
    ∀ rows cols : Fin (r + 1) ↪ Fin n,
      (∀ i j, (A (rows i) (cols j) - B (rows i) (cols j)) ^ 2 ≤ τ) →
        (A.submatrix rows cols).det = 0

/-- The large-error coloring associated to a separation constant satisfies
the all-green singular-minor hypothesis of Lemma 10.3. -/
lemma allGreenMinorSingular_of_separation
    {r n : ℕ} {τ : ℝ} (hsep : BinaryMinorSeparationAt r τ)
    {A B : Matrix (Fin n) (Fin n) ℝ} (hA : IsBinary A) (hB : B.rank ≤ r) :
    AllGreenMinorSingular r A
      (fun i j ↦ τ < (A i j - B i j) ^ 2) := by
  intro rows cols hgreen
  apply hsep.2 n A B hA hB rows cols
  intro i j
  exact le_of_not_gt (hgreen i j)

private lemma det_ne_zero_of_entrywise_sq_le
    {k : ℕ} (A : Matrix (Fin k) (Fin k) ℝ) (hA : A.det ≠ 0) :
    ∃ τ : ℝ, 0 < τ ∧ ∀ B : Matrix (Fin k) (Fin k) ℝ,
      (∀ i j, (A i j - B i j) ^ 2 ≤ τ) → B.det ≠ 0 := by
  classical
  let rowPseudoMetric : PseudoMetricSpace (Fin k → ℝ) :=
    pseudoMetricSpacePi
  let matrixPseudoMetric : PseudoMetricSpace (Matrix (Fin k) (Fin k) ℝ) :=
    pseudoMetricSpacePi
  have hopen : IsOpen {M : Matrix (Fin k) (Fin k) ℝ | M.det ≠ 0} := by
    exact isClosed_singleton.isOpen_compl.preimage continuous_id.matrix_det
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen A (show A.det ≠ 0 from hA)
  refine ⟨(ε / 2) ^ 2, sq_pos_of_pos (half_pos hε), ?_⟩
  intro B hclose
  apply hball
  rw [Metric.mem_ball, dist_comm]
  apply (dist_pi_lt_iff hε).2
  intro i
  apply (dist_pi_lt_iff hε).2
  intro j
  rw [Real.dist_eq]
  have habs : |A i j - B i j| ≤ ε / 2 :=
    abs_le_of_sq_le_sq (hclose i j) (le_of_lt (half_pos hε))
  simpa only [abs_sub_comm] using habs.trans_lt (half_lt_self hε)

/-- The finite collection of all binary square matrices of a fixed order,
realized as the image of the corresponding Boolean matrices. -/
private noncomputable def binaryMatrices (k : ℕ) :
    Finset (Matrix (Fin k) (Fin k) ℝ) := by
  classical
  exact Finset.univ.image
    (fun C : Matrix (Fin k) (Fin k) Bool ↦ fun i j ↦
      if C i j then (1 : ℝ) else 0)

private lemma mem_binaryMatrices {k : ℕ} {A : Matrix (Fin k) (Fin k) ℝ}
    (hA : IsBinary A) : A ∈ binaryMatrices k := by
  classical
  rw [binaryMatrices]
  refine Finset.mem_image.2
    ⟨(fun i j ↦ decide (A i j = 1)), Finset.mem_univ _, ?_⟩
  funext i j
  rcases hA i j with hij | hij
  · simp [hij]
  · simp [hij]

/-- In a fixed dimension, one positive entrywise neighborhood works
simultaneously for every nonsingular binary matrix. -/
private lemma finite_binary_det_separation (k : ℕ) :
    ∃ τ : ℝ, 0 < τ ∧
      ∀ A ∈ binaryMatrices k, A.det ≠ 0 →
        ∀ B : Matrix (Fin k) (Fin k) ℝ,
          (∀ i j, (A i j - B i j) ^ 2 ≤ τ) → B.det ≠ 0 := by
  classical
  induction binaryMatrices k using Finset.induction_on with
  | empty =>
      refine ⟨1, by norm_num, ?_⟩
      simp
  | @insert a s ha ih =>
      obtain ⟨τs, hτs, hs⟩ := ih
      by_cases hadeg : a.det = 0
      · refine ⟨τs, hτs, ?_⟩
        intro A hAin hAdet B hclose
        rcases Finset.mem_insert.mp hAin with hAa | hAs
        · subst A
          exact (hAdet hadeg).elim
        · exact hs A hAs hAdet B hclose
      · obtain ⟨τa, hτa, ha_sep⟩ := det_ne_zero_of_entrywise_sq_le a hadeg
        refine ⟨min τs τa, lt_min hτs hτa, ?_⟩
        intro A hAin hAdet B hclose
        rcases Finset.mem_insert.mp hAin with hAa | hAs
        · subst A
          apply ha_sep B
          intro i j
          exact (hclose i j).trans (min_le_right _ _)
        · apply hs A hAs hAdet B
          intro i j
          exact (hclose i j).trans (min_le_left _ _)

/-- Uniform determinant separation for binary minors.  The constant depends
only on the target rank, not on the ambient matrix order. -/
theorem binaryMinorSeparation_exists :
    ∀ r : ℕ, ∃ τ : ℝ, BinaryMinorSeparationAt r τ := by
  intro r
  obtain ⟨τ, hτ, hsep⟩ := finite_binary_det_separation (r + 1)
  refine ⟨τ, hτ, ?_⟩
  intro n A B hA hBrank rows cols hclose
  let A₀ : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ := A.submatrix rows cols
  let B₀ : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ := B.submatrix rows cols
  have hA₀binary : IsBinary A₀ := by
    intro i j
    exact hA (rows i) (cols j)
  have hA₀mem : A₀ ∈ binaryMatrices (r + 1) :=
    mem_binaryMatrices hA₀binary
  have hB₀rank : B₀.rank ≤ r := by
    exact (Matrix.rank_submatrix_le B rows cols).trans hBrank
  have hB₀det : B₀.det = 0 := by
    by_contra hne
    have hfull : B₀.rank = r + 1 := by
      simpa [B₀] using Matrix.rank_of_det_ne_zero hne
    omega
  by_contra hA₀det
  have hB₀ne : B₀.det ≠ 0 := by
    apply hsep A₀ hA₀mem hA₀det B₀
    intro i j
    exact hclose i j
  exact hB₀ne hB₀det

/-- The exact finite assertion of KSSS Lemma 10.3.  The normalization of
the red-cell bound is the one used in the paper: fewer than
`η² / (10·2^r)²` of all cells are red. -/
def KSSSLemma103 : Prop :=
  ∀ (r n : ℕ) (η : ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
      (red : Fin n → Fin n → Prop),
    0 < η → η ≤ 1 → IsBinary A →
    (redCount red : ℝ) <
      η ^ 2 / (10 * (2 : ℝ) ^ r) ^ 2 * (n : ℝ) ^ 2 →
    AllGreenMinorSingular r A red →
      ∃ Q : Matrix (Fin n) (Fin n) ℝ,
        IsBinary Q ∧ Q.rank ≤ r ∧
          (editDistance A Q : ℝ) ≤ η * (n : ℝ) ^ 2

/-- The first construction step in the general proof of Lemma 10.3.  With
the paper's scale `s = η n / (10·2^r)`, choose a maximal nonsingular
all-green core among rows and columns having red degree at most `s`.
The two exceptional high-degree sets each have cardinality strictly below
`s`. -/
private lemma exists_ksss_maximal_core
    {r n : ℕ} {η : ℝ} (A : Matrix (Fin n) (Fin n) ℝ)
    (red : Fin n → Fin n → Prop)
    (hn : 0 < n) (hη : 0 < η)
    (hred : (redCount red : ℝ) <
      η ^ 2 / (10 * (2 : ℝ) ^ r) ^ 2 * (n : ℝ) ^ 2)
    (hsingular : AllGreenMinorSingular r A red) :
    ∃ s : ℝ, s = η * (n : ℝ) / (10 * (2 : ℝ) ^ r) ∧ 0 < s ∧
      (redCount red : ℝ) < s ^ 2 ∧
      ∃ l : ℕ, l ≤ r ∧ ∃ rows cols : Fin l ↪ Fin n,
        (∀ a, (redRowDegree red (rows a) : ℝ) ≤ s) ∧
        (∀ b, (redColDegree red (cols b) : ℝ) ≤ s) ∧
        (∀ a b, ¬ red (rows a) (cols b)) ∧
        (A.submatrix rows cols).det ≠ 0 ∧
        (∀ rows' cols' : Fin (l + 1) ↪ Fin n,
          (∀ a, (redRowDegree red (rows' a) : ℝ) ≤ s) →
          (∀ b, (redColDegree red (cols' b) : ℝ) ≤ s) →
          (∀ a b, ¬ red (rows' a) (cols' b)) →
            (A.submatrix rows' cols').det = 0) ∧
        (((Finset.univ.filter fun i ↦
          s < (redRowDegree red i : ℝ)).card : ℕ) : ℝ) < s ∧
        (((Finset.univ.filter fun j ↦
          s < (redColDegree red j : ℝ)).card : ℕ) : ℝ) < s := by
  classical
  let s : ℝ := η * (n : ℝ) / (10 * (2 : ℝ) ^ r)
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : 0 < s := by
    dsimp [s]
    positivity
  have hsq :
      s ^ 2 = η ^ 2 / (10 * (2 : ℝ) ^ r) ^ 2 * (n : ℝ) ^ 2 := by
    dsimp [s]
    ring
  have hredSq : (redCount red : ℝ) < s ^ 2 := by
    rw [hsq]
    exact hred
  obtain ⟨l, hlr, rows, cols, hrows, hcols, hgreen, hdet, hmax⟩ :=
    exists_maximal_good_green_core A red
      (fun i ↦ (redRowDegree red i : ℝ) ≤ s)
      (fun j ↦ (redColDegree red j : ℝ) ≤ s) hsingular
  refine ⟨s, rfl, hs, hredSq, l, hlr, rows, cols, hrows, hcols,
    hgreen, hdet, hmax, ?_, ?_⟩
  · exact card_highRedRows_lt red hs hredSq
  · exact card_highRedCols_lt red hs hredSq

/-- A green entry outside a maximal good core equals its Schur-complement
prediction, provided its row and column have green links to the entire core.
This is the pointwise algebraic bridge used by the Boolean type argument. -/
private lemma maximal_core_predicts_green_entry
    {n l : ℕ} {s : ℝ} (A : Matrix (Fin n) (Fin n) ℝ)
    (red : Fin n → Fin n → Prop)
    (rows cols : Fin l ↪ Fin n)
    (hrows : ∀ a, (redRowDegree red (rows a) : ℝ) ≤ s)
    (hcols : ∀ b, (redColDegree red (cols b) : ℝ) ≤ s)
    (hcoreGreen : ∀ a b, ¬ red (rows a) (cols b))
    (hcore : (A.submatrix rows cols).det ≠ 0)
    (hmax : ∀ rows' cols' : Fin (l + 1) ↪ Fin n,
      (∀ a, (redRowDegree red (rows' a) : ℝ) ≤ s) →
      (∀ b, (redColDegree red (cols' b) : ℝ) ≤ s) →
      (∀ a b, ¬ red (rows' a) (cols' b)) →
        (A.submatrix rows' cols').det = 0)
    {i j : Fin n} (hi : i ∉ Set.range rows) (hj : j ∉ Set.range cols)
    (hrow : (redRowDegree red i : ℝ) ≤ s)
    (hcol : (redColDegree red j : ℝ) ≤ s)
    (hrowLinks : ∀ b, ¬ red i (cols b))
    (hcolLinks : ∀ a, ¬ red (rows a) j)
    (hij : ¬ red i j) :
    A i j =
      ((A.submatrix (fun _ : Fin 1 ↦ i) cols) *
        (A.submatrix rows cols)⁻¹ *
        (A.submatrix rows (fun _ : Fin 1 ↦ j))) 0 0 := by
  classical
  let rows' : Fin (l + 1) ↪ Fin n := Fin.Embedding.snoc rows hi
  let cols' : Fin (l + 1) ↪ Fin n := Fin.Embedding.snoc cols hj
  have hrows' : ∀ a, (redRowDegree red (rows' a) : ℝ) ≤ s := by
    intro a
    refine Fin.lastCases ?_ (fun a ↦ ?_) a
    · simpa [rows', Fin.Embedding.snoc_last] using hrow
    · simpa [rows', Fin.Embedding.snoc_castSucc] using hrows a
  have hcols' : ∀ b, (redColDegree red (cols' b) : ℝ) ≤ s := by
    intro b
    refine Fin.lastCases ?_ (fun b ↦ ?_) b
    · simpa [cols', Fin.Embedding.snoc_last] using hcol
    · simpa [cols', Fin.Embedding.snoc_castSucc] using hcols b
  have hgreen' : ∀ a b, ¬ red (rows' a) (cols' b) := by
    intro a b
    refine Fin.lastCases ?_ (fun a ↦ ?_) a
    · refine Fin.lastCases ?_ (fun b ↦ ?_) b
      · simpa [rows', cols', Fin.Embedding.snoc_last] using hij
      · simpa [rows', cols', Fin.Embedding.snoc_last,
          Fin.Embedding.snoc_castSucc] using hrowLinks b
    · refine Fin.lastCases ?_ (fun b ↦ ?_) b
      · simpa [rows', cols', Fin.Embedding.snoc_last,
          Fin.Embedding.snoc_castSucc] using hcolLinks a
      · simpa [rows', cols', Fin.Embedding.snoc_castSucc] using hcoreGreen a b
  have hext : (A.submatrix rows' cols').det = 0 :=
    hmax rows' cols' hrows' hcols' hgreen'
  exact corner_eq_schur_of_snoc_det_eq_zero A rows cols i j hi hj hcore hext

/-- Boolean signature of a row on the columns of a selected core. -/
noncomputable def coreRowCode {n l : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (cols : Fin l ↪ Fin n) (i : Fin n) : Fin l → Bool := by
  classical
  exact fun b ↦ decide (A i (cols b) = 1)

/-- Boolean signature of a column on the rows of a selected core. -/
noncomputable def coreColCode {n l : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (rows : Fin l ↪ Fin n) (j : Fin n) : Fin l → Bool := by
  classical
  exact fun a ↦ decide (A (rows a) j = 1)

private lemma coreRowCode_eq_entries
    {n l : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsBinary A)
    (cols : Fin l ↪ Fin n) {i i' : Fin n}
    (hcode : coreRowCode A cols i = coreRowCode A cols i') :
    ∀ b, A i (cols b) = A i' (cols b) := by
  intro b
  apply binary_eq_of_decide_eq (hA i (cols b)) (hA i' (cols b))
  have := congr_fun hcode b
  simpa [coreRowCode] using this

private lemma coreColCode_eq_entries
    {n l : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsBinary A)
    (rows : Fin l ↪ Fin n) {j j' : Fin n}
    (hcode : coreColCode A rows j = coreColCode A rows j') :
    ∀ a, A (rows a) j = A (rows a) j' := by
  intro a
  apply binary_eq_of_decide_eq (hA (rows a) j) (hA (rows a) j')
  have := congr_fun hcode a
  simpa [coreColCode] using this

/-- For Boolean words of length `l`, the union of the occurring fibres of
size at most `s` has size at most `2^l s`. -/
lemma card_small_bool_code_fibers_le
    {I : Type*} [DecidableEq I] (S : Finset I) {l : ℕ}
    (code : I → Fin l → Bool) {s : ℝ} (hs : 0 ≤ s) :
    let types := S.image code
    let smallTypes := types.filter fun c ↦
      ((S.filter fun i ↦ code i = c).card : ℝ) ≤ s
    ((S.filter fun i ↦ code i ∈ smallTypes).card : ℝ) ≤
      (2 : ℝ) ^ l * s := by
  classical
  dsimp only
  let types := S.image code
  let smallTypes := types.filter fun c ↦
    ((S.filter fun i ↦ code i = c).card : ℝ) ≤ s
  have hsmall :
      ((S.filter fun i ↦ code i ∈ smallTypes).card : ℝ) ≤
        (types.card : ℝ) * s := by
    simpa [types, smallTypes] using card_small_code_fibers_le S code hs
  have htypesNat : types.card ≤ 2 ^ l := by
    simpa [types] using card_bool_codes_le_two_pow S code
  have htypes : (types.card : ℝ) ≤ (2 : ℝ) ^ l := by
    exact_mod_cast htypesNat
  exact hsmall.trans (mul_le_mul_of_nonneg_right htypes hs)

lemma card_small_coreRowCode_fibers_le
    {n l : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (cols : Fin l ↪ Fin n)
    (S : Finset (Fin n)) {s : ℝ} (hs : 0 ≤ s) :
    let code := coreRowCode A cols
    let types := S.image code
    let smallTypes := types.filter fun c ↦
      ((S.filter fun i ↦ code i = c).card : ℝ) ≤ s
    ((S.filter fun i ↦ code i ∈ smallTypes).card : ℝ) ≤
      (2 : ℝ) ^ l * s := by
  classical
  exact card_small_bool_code_fibers_le S (coreRowCode A cols) hs

lemma card_small_coreColCode_fibers_le
    {n l : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (rows : Fin l ↪ Fin n)
    (S : Finset (Fin n)) {s : ℝ} (hs : 0 ≤ s) :
    let code := coreColCode A rows
    let types := S.image code
    let smallTypes := types.filter fun c ↦
      ((S.filter fun j ↦ code j = c).card : ℝ) ≤ s
    ((S.filter fun j ↦ code j ∈ smallTypes).card : ℝ) ≤
      (2 : ℝ) ^ l * s := by
  classical
  exact card_small_bool_code_fibers_le S (coreColCode A rows) hs

/-- Rows having at least one red link to a selected set of core columns. -/
noncomputable def coreRedLinkedRows {n l : ℕ}
    (red : Fin n → Fin n → Prop) (cols : Fin l ↪ Fin n) :
    Finset (Fin n) := by
  classical
  exact Finset.univ.biUnion fun b ↦ Finset.univ.filter fun i ↦ red i (cols b)

/-- Columns having at least one red link to a selected set of core rows. -/
noncomputable def coreRedLinkedCols {n l : ℕ}
    (red : Fin n → Fin n → Prop) (rows : Fin l ↪ Fin n) :
    Finset (Fin n) := by
  classical
  exact Finset.univ.biUnion fun a ↦ Finset.univ.filter fun j ↦ red (rows a) j

@[simp] lemma mem_coreRedLinkedRows {n l : ℕ}
    (red : Fin n → Fin n → Prop) (cols : Fin l ↪ Fin n) (i : Fin n) :
    i ∈ coreRedLinkedRows red cols ↔ ∃ b, red i (cols b) := by
  classical
  simp [coreRedLinkedRows]

@[simp] lemma mem_coreRedLinkedCols {n l : ℕ}
    (red : Fin n → Fin n → Prop) (rows : Fin l ↪ Fin n) (j : Fin n) :
    j ∈ coreRedLinkedCols red rows ↔ ∃ a, red (rows a) j := by
  classical
  simp [coreRedLinkedCols]

lemma card_coreRedLinkedRows_le
    {n l : ℕ} (red : Fin n → Fin n → Prop) (cols : Fin l ↪ Fin n)
    {s : ℝ} (hcols : ∀ b, (redColDegree red (cols b) : ℝ) ≤ s) :
    ((coreRedLinkedRows red cols).card : ℝ) ≤ (l : ℝ) * s := by
  classical
  let fibers : Fin l → Finset (Fin n) :=
    fun b ↦ Finset.univ.filter fun i ↦ red i (cols b)
  have hcardNat : (Finset.univ.biUnion fibers).card ≤
      ∑ b ∈ (Finset.univ : Finset (Fin l)), (fibers b).card :=
    Finset.card_biUnion_le
  have hcard : ((Finset.univ.biUnion fibers).card : ℝ) ≤
      ∑ b : Fin l, ((fibers b).card : ℝ) := by
    exact_mod_cast hcardNat
  calc
    ((coreRedLinkedRows red cols).card : ℝ) ≤
        ∑ b : Fin l, ((fibers b).card : ℝ) := by
      simpa [coreRedLinkedRows, fibers] using hcard
    _ = ∑ b : Fin l, (redColDegree red (cols b) : ℝ) := by
      congr 1
    _ ≤ ∑ _b : Fin l, s := by
      exact Finset.sum_le_sum fun b _ ↦ hcols b
    _ = (l : ℝ) * s := by simp

lemma card_coreRedLinkedCols_le
    {n l : ℕ} (red : Fin n → Fin n → Prop) (rows : Fin l ↪ Fin n)
    {s : ℝ} (hrows : ∀ a, (redRowDegree red (rows a) : ℝ) ≤ s) :
    ((coreRedLinkedCols red rows).card : ℝ) ≤ (l : ℝ) * s := by
  classical
  let fibers : Fin l → Finset (Fin n) :=
    fun a ↦ Finset.univ.filter fun j ↦ red (rows a) j
  have hcardNat : (Finset.univ.biUnion fibers).card ≤
      ∑ a ∈ (Finset.univ : Finset (Fin l)), (fibers a).card :=
    Finset.card_biUnion_le
  have hcard : ((Finset.univ.biUnion fibers).card : ℝ) ≤
      ∑ a : Fin l, ((fibers a).card : ℝ) := by
    exact_mod_cast hcardNat
  calc
    ((coreRedLinkedCols red rows).card : ℝ) ≤
        ∑ a : Fin l, ((fibers a).card : ℝ) := by
      simpa [coreRedLinkedCols, fibers] using hcard
    _ = ∑ a : Fin l, (redRowDegree red (rows a) : ℝ) := by
      congr 1
    _ ≤ ∑ _a : Fin l, s := by
      exact Finset.sum_le_sum fun a _ ↦ hrows a
    _ = (l : ℝ) * s := by simp

noncomputable def highRedRowsAt {n : ℕ}
    (red : Fin n → Fin n → Prop) (s : ℝ) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun i ↦ s < (redRowDegree red i : ℝ)

noncomputable def highRedColsAt {n : ℕ}
    (red : Fin n → Fin n → Prop) (s : ℝ) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun j ↦ s < (redColDegree red j : ℝ)

noncomputable def coreRowCandidates {n l : ℕ}
    (red : Fin n → Fin n → Prop) (cols : Fin l ↪ Fin n) (s : ℝ) :
    Finset (Fin n) :=
  Finset.univ \ (highRedRowsAt red s ∪ coreRedLinkedRows red cols)

noncomputable def coreColCandidates {n l : ℕ}
    (red : Fin n → Fin n → Prop) (rows : Fin l ↪ Fin n) (s : ℝ) :
    Finset (Fin n) :=
  Finset.univ \ (highRedColsAt red s ∪ coreRedLinkedCols red rows)

noncomputable def smallCoreRowMembers {n l : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (red : Fin n → Fin n → Prop)
    (cols : Fin l ↪ Fin n) (s : ℝ) : Finset (Fin n) := by
  classical
  let S := coreRowCandidates red cols s
  let code := coreRowCode A cols
  let smallTypes := (S.image code).filter fun c ↦
    ((S.filter fun i ↦ code i = c).card : ℝ) ≤ s
  exact S.filter fun i ↦ code i ∈ smallTypes

noncomputable def smallCoreColMembers {n l : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (red : Fin n → Fin n → Prop)
    (rows : Fin l ↪ Fin n) (s : ℝ) : Finset (Fin n) := by
  classical
  let S := coreColCandidates red rows s
  let code := coreColCode A rows
  let smallTypes := (S.image code).filter fun c ↦
    ((S.filter fun j ↦ code j = c).card : ℝ) ≤ s
  exact S.filter fun j ↦ code j ∈ smallTypes

noncomputable def ksssDiscardRows {n l : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (red : Fin n → Fin n → Prop)
    (cols : Fin l ↪ Fin n) (s : ℝ) : Finset (Fin n) :=
  (highRedRowsAt red s ∪ coreRedLinkedRows red cols) ∪
    smallCoreRowMembers A red cols s

noncomputable def ksssDiscardCols {n l : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (red : Fin n → Fin n → Prop)
    (rows : Fin l ↪ Fin n) (s : ℝ) : Finset (Fin n) :=
  (highRedColsAt red s ∪ coreRedLinkedCols red rows) ∪
    smallCoreColMembers A red rows s

lemma card_ksssDiscardRows_lt
    {n l : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (red : Fin n → Fin n → Prop) (cols : Fin l ↪ Fin n)
    {s : ℝ} (hs : 0 < s) (hred : (redCount red : ℝ) < s ^ 2)
    (hcols : ∀ b, (redColDegree red (cols b) : ℝ) ≤ s) :
    ((ksssDiscardRows A red cols s).card : ℝ) <
      (1 + (l : ℝ) + (2 : ℝ) ^ l) * s := by
  classical
  let H := highRedRowsAt red s
  let L := coreRedLinkedRows red cols
  let S := coreRowCandidates red cols s
  let M := smallCoreRowMembers A red cols s
  have hH : (H.card : ℝ) < s := by
    simpa [H, highRedRowsAt] using card_highRedRows_lt red hs hred
  have hL : (L.card : ℝ) ≤ (l : ℝ) * s := by
    simpa [L] using card_coreRedLinkedRows_le red cols hcols
  have hM : (M.card : ℝ) ≤ (2 : ℝ) ^ l * s := by
    simpa [M, smallCoreRowMembers, S] using
      card_small_coreRowCode_fibers_le A cols S (le_of_lt hs)
  have hcardNat : ((H ∪ L) ∪ M).card ≤ H.card + L.card + M.card := by
    calc
      ((H ∪ L) ∪ M).card ≤ (H ∪ L).card + M.card :=
        Finset.card_union_le (H ∪ L) M
      _ ≤ (H.card + L.card) + M.card := by
        gcongr
        exact Finset.card_union_le H L
  have hcard : (((H ∪ L) ∪ M).card : ℝ) ≤
      (H.card : ℝ) + L.card + M.card := by
    exact_mod_cast hcardNat
  change (((H ∪ L) ∪ M).card : ℝ) < _
  calc
    (((H ∪ L) ∪ M).card : ℝ) ≤
        (H.card : ℝ) + L.card + M.card := hcard
    _ < s + (l : ℝ) * s + (2 : ℝ) ^ l * s := by linarith
    _ = (1 + (l : ℝ) + (2 : ℝ) ^ l) * s := by ring

lemma card_ksssDiscardCols_lt
    {n l : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (red : Fin n → Fin n → Prop) (rows : Fin l ↪ Fin n)
    {s : ℝ} (hs : 0 < s) (hred : (redCount red : ℝ) < s ^ 2)
    (hrows : ∀ a, (redRowDegree red (rows a) : ℝ) ≤ s) :
    ((ksssDiscardCols A red rows s).card : ℝ) <
      (1 + (l : ℝ) + (2 : ℝ) ^ l) * s := by
  classical
  let H := highRedColsAt red s
  let L := coreRedLinkedCols red rows
  let S := coreColCandidates red rows s
  let M := smallCoreColMembers A red rows s
  have hH : (H.card : ℝ) < s := by
    simpa [H, highRedColsAt] using card_highRedCols_lt red hs hred
  have hL : (L.card : ℝ) ≤ (l : ℝ) * s := by
    simpa [L] using card_coreRedLinkedCols_le red rows hrows
  have hM : (M.card : ℝ) ≤ (2 : ℝ) ^ l * s := by
    simpa [M, smallCoreColMembers, S] using
      card_small_coreColCode_fibers_le A rows S (le_of_lt hs)
  have hcardNat : ((H ∪ L) ∪ M).card ≤ H.card + L.card + M.card := by
    calc
      ((H ∪ L) ∪ M).card ≤ (H ∪ L).card + M.card :=
        Finset.card_union_le (H ∪ L) M
      _ ≤ (H.card + L.card) + M.card := by
        gcongr
        exact Finset.card_union_le H L
  have hcard : (((H ∪ L) ∪ M).card : ℝ) ≤
      (H.card : ℝ) + L.card + M.card := by
    exact_mod_cast hcardNat
  change (((H ∪ L) ∪ M).card : ℝ) < _
  calc
    (((H ∪ L) ∪ M).card : ℝ) ≤
        (H.card : ℝ) + L.card + M.card := hcard
    _ < s + (l : ℝ) * s + (2 : ℝ) ^ l * s := by linarith
    _ = (1 + (l : ℝ) + (2 : ℝ) ^ l) * s := by ring

lemma retainedRow_properties
    {n l : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (red : Fin n → Fin n → Prop) (cols : Fin l ↪ Fin n)
    {s : ℝ} {i : Fin n} (hi : i ∉ ksssDiscardRows A red cols s) :
    (redRowDegree red i : ℝ) ≤ s ∧
      (∀ b, ¬ red i (cols b)) ∧
      s < ((coreRowCandidates red cols s).filter fun i' ↦
        coreRowCode A cols i' = coreRowCode A cols i).card := by
  classical
  let H := highRedRowsAt red s
  let L := coreRedLinkedRows red cols
  let S := coreRowCandidates red cols s
  let code := coreRowCode A cols
  let smallTypes := (S.image code).filter fun c ↦
    ((S.filter fun i ↦ code i = c).card : ℝ) ≤ s
  have hiH : i ∉ H := by
    intro hi'
    exact hi (by simp [ksssDiscardRows, H, hi'])
  have hiL : i ∉ L := by
    intro hi'
    exact hi (by simp [ksssDiscardRows, L, hi'])
  have hiS : i ∈ S := by
    simp [S, coreRowCandidates, H, L, hiH, hiL]
  have hiM : i ∉ smallCoreRowMembers A red cols s := by
    intro hi'
    exact hi (by simp [ksssDiscardRows, hi'])
  have hcodeMem : code i ∈ S.image code := Finset.mem_image.mpr ⟨i, hiS, rfl⟩
  have hcodeNotSmall : code i ∉ smallTypes := by
    intro hc
    apply hiM
    have hiSmall : i ∈ S.filter (fun i' ↦ code i' ∈ smallTypes) :=
      Finset.mem_filter.mpr ⟨hiS, hc⟩
    simpa [smallCoreRowMembers, S, code, smallTypes] using hiSmall
  have hfiber : s < ((S.filter fun i' ↦ code i' = code i).card : ℝ) := by
    exact lt_of_not_ge fun hle ↦ hcodeNotSmall
      (Finset.mem_filter.mpr ⟨hcodeMem, hle⟩)
  refine ⟨?_, ?_, ?_⟩
  · exact le_of_not_gt (by simpa [H, highRedRowsAt] using hiH)
  · intro b hr
    exact hiL (mem_coreRedLinkedRows red cols i |>.mpr ⟨b, hr⟩)
  · simpa [S, code] using hfiber

lemma retainedCol_properties
    {n l : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (red : Fin n → Fin n → Prop) (rows : Fin l ↪ Fin n)
    {s : ℝ} {j : Fin n} (hj : j ∉ ksssDiscardCols A red rows s) :
    (redColDegree red j : ℝ) ≤ s ∧
      (∀ a, ¬ red (rows a) j) ∧
      s < ((coreColCandidates red rows s).filter fun j' ↦
        coreColCode A rows j' = coreColCode A rows j).card := by
  classical
  let H := highRedColsAt red s
  let L := coreRedLinkedCols red rows
  let S := coreColCandidates red rows s
  let code := coreColCode A rows
  let smallTypes := (S.image code).filter fun c ↦
    ((S.filter fun j ↦ code j = c).card : ℝ) ≤ s
  have hjH : j ∉ H := by
    intro hj'
    exact hj (by simp [ksssDiscardCols, H, hj'])
  have hjL : j ∉ L := by
    intro hj'
    exact hj (by simp [ksssDiscardCols, L, hj'])
  have hjS : j ∈ S := by
    simp [S, coreColCandidates, H, L, hjH, hjL]
  have hjM : j ∉ smallCoreColMembers A red rows s := by
    intro hj'
    exact hj (by simp [ksssDiscardCols, hj'])
  have hcodeMem : code j ∈ S.image code := Finset.mem_image.mpr ⟨j, hjS, rfl⟩
  have hcodeNotSmall : code j ∉ smallTypes := by
    intro hc
    apply hjM
    have hjSmall : j ∈ S.filter (fun j' ↦ code j' ∈ smallTypes) :=
      Finset.mem_filter.mpr ⟨hjS, hc⟩
    simpa [smallCoreColMembers, S, code, smallTypes] using hjSmall
  have hfiber : s < ((S.filter fun j' ↦ code j' = code j).card : ℝ) := by
    exact lt_of_not_ge fun hle ↦ hcodeNotSmall
      (Finset.mem_filter.mpr ⟨hcodeMem, hle⟩)
  refine ⟨?_, ?_, ?_⟩
  · exact le_of_not_gt (by simpa [H, highRedColsAt] using hjH)
  · intro a hr
    exact hjL (mem_coreRedLinkedCols red rows j |>.mpr ⟨a, hr⟩)
  · simpa [S, code] using hfiber

/-- If the whole matrix has fewer than `s²` red cells, any rectangle whose
two sides both have cardinality greater than `s` contains a green cell. -/
lemma exists_green_in_large_rectangle
    {I J : Type*} [Fintype I] [Fintype J]
    (red : I → J → Prop) (S : Finset I) (T : Finset J)
    {s : ℝ} (hs : 0 < s)
    (hS : s < (S.card : ℝ)) (hT : s < (T.card : ℝ))
    (hred : (redCount red : ℝ) < s ^ 2) :
    ∃ i ∈ S, ∃ j ∈ T, ¬ red i j := by
  classical
  by_contra hgreen
  push_neg at hgreen
  have hsubset : S.product T ⊆
      (Finset.univ.product Finset.univ).filter fun p ↦ red p.1 p.2 := by
    intro p hp
    obtain ⟨hpi, hpj⟩ := Finset.mem_product.mp hp
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩,
        hgreen p.1 hpi p.2 hpj⟩
  have hcardNat : (S.product T).card ≤ redCount red := by
    unfold redCount
    exact Finset.card_le_card hsubset
  have hcard : (S.card : ℝ) * (T.card : ℝ) ≤ redCount red := by
    rw [← Nat.cast_mul, ← Finset.card_product]
    exact_mod_cast hcardNat
  have hprod : s ^ 2 < (S.card : ℝ) * (T.card : ℝ) := by
    nlinarith [mul_pos (sub_pos.mpr hS) (sub_pos.mpr hT)]
  nlinarith

/-- The unmasked rank-`l` Schur prediction associated to a nonsingular
`l × l` core. -/
noncomputable def schurPrediction {n l : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (rows cols : Fin l ↪ Fin n) :
    Matrix (Fin n) (Fin n) ℝ :=
  (A.submatrix id cols) *
    ((A.submatrix rows cols)⁻¹ * (A.submatrix rows id))

/-- The Schur prediction after zeroing prescribed exceptional rows and
columns.  Writing the masks into the two rectangular factors makes the
rank bound immediate. -/
noncomputable def maskedSchurPrediction {n l : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (rows cols : Fin l ↪ Fin n)
    (discardRows discardCols : Finset (Fin n)) :
    Matrix (Fin n) (Fin n) ℝ := by
  classical
  let L : Matrix (Fin n) (Fin l) ℝ :=
    fun i b ↦ if i ∈ discardRows then 0 else A i (cols b)
  let Kinv : Matrix (Fin l) (Fin l) ℝ := (A.submatrix rows cols)⁻¹
  let R : Matrix (Fin l) (Fin n) ℝ :=
    fun a j ↦ if j ∈ discardCols then 0 else A (rows a) j
  exact L * (Kinv * R)

lemma maskedSchurPrediction_rank_le
    {n l : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (rows cols : Fin l ↪ Fin n) (discardRows discardCols : Finset (Fin n)) :
    (maskedSchurPrediction A rows cols discardRows discardCols).rank ≤ l := by
  classical
  simp only [maskedSchurPrediction]
  exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_le_width _)

@[simp] lemma maskedSchurPrediction_apply_of_row_mem
    {n l : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (rows cols : Fin l ↪ Fin n) (discardRows discardCols : Finset (Fin n))
    {i j : Fin n} (hi : i ∈ discardRows) :
    maskedSchurPrediction A rows cols discardRows discardCols i j = 0 := by
  classical
  change (∑ b : Fin l,
    (if i ∈ discardRows then 0 else A i (cols b)) *
      (∑ a : Fin l, (A.submatrix rows cols)⁻¹ b a *
        (if j ∈ discardCols then 0 else A (rows a) j))) = 0
  simp [hi]

@[simp] lemma maskedSchurPrediction_apply_of_col_mem
    {n l : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (rows cols : Fin l ↪ Fin n) (discardRows discardCols : Finset (Fin n))
    {i j : Fin n} (hj : j ∈ discardCols) :
    maskedSchurPrediction A rows cols discardRows discardCols i j = 0 := by
  classical
  change (∑ b : Fin l,
    (if i ∈ discardRows then 0 else A i (cols b)) *
      (∑ a : Fin l, (A.submatrix rows cols)⁻¹ b a *
        (if j ∈ discardCols then 0 else A (rows a) j))) = 0
  simp [hj]

lemma maskedSchurPrediction_apply_of_not_mem
    {n l : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (rows cols : Fin l ↪ Fin n) (discardRows discardCols : Finset (Fin n))
    {i j : Fin n} (hi : i ∉ discardRows) (hj : j ∉ discardCols) :
    maskedSchurPrediction A rows cols discardRows discardCols i j =
      schurPrediction A rows cols i j := by
  classical
  change (∑ b : Fin l,
    (if i ∈ discardRows then 0 else A i (cols b)) *
      (∑ a : Fin l, (A.submatrix rows cols)⁻¹ b a *
        (if j ∈ discardCols then 0 else A (rows a) j))) =
    ∑ b : Fin l, A i (cols b) *
      (∑ a : Fin l, (A.submatrix rows cols)⁻¹ b a * A (rows a) j)
  simp [hi, hj]

/-- On every selected core row, the Schur prediction is exactly the
corresponding row of the original matrix. -/
lemma schurPrediction_core_row
    {n l : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (rows cols : Fin l ↪ Fin n)
    (hcore : (A.submatrix rows cols).det ≠ 0)
    (a : Fin l) (j : Fin n) :
    schurPrediction A rows cols (rows a) j = A (rows a) j := by
  classical
  let K : Matrix (Fin l) (Fin l) ℝ := A.submatrix rows cols
  let R : Matrix (Fin l) (Fin n) ℝ := A.submatrix rows id
  have hunit : IsUnit K.det := isUnit_iff_ne_zero.mpr hcore
  have hcancel : K * (K⁻¹ * R) = R :=
    Matrix.mul_nonsing_inv_cancel_left K R hunit
  calc
    schurPrediction A rows cols (rows a) j = (K * (K⁻¹ * R)) a j := by
      rfl
    _ = R a j := by rw [hcancel]
    _ = A (rows a) j := rfl

/-- On every selected core column, the Schur prediction is exactly the
corresponding column of the original matrix. -/
lemma schurPrediction_core_col
    {n l : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (rows cols : Fin l ↪ Fin n)
    (hcore : (A.submatrix rows cols).det ≠ 0)
    (i : Fin n) (b : Fin l) :
    schurPrediction A rows cols i (cols b) = A i (cols b) := by
  classical
  let K : Matrix (Fin l) (Fin l) ℝ := A.submatrix rows cols
  let L : Matrix (Fin n) (Fin l) ℝ := A.submatrix id cols
  have hunit : IsUnit K.det := isUnit_iff_ne_zero.mpr hcore
  have hcancel : L * K⁻¹ * K = L :=
    Matrix.nonsing_inv_mul_cancel_right K L hunit
  calc
    schurPrediction A rows cols i (cols b) = (L * (K⁻¹ * K)) i b := by
      rfl
    _ = (L * K⁻¹ * K) i b := by rw [Matrix.mul_assoc]
    _ = L i b := by rw [hcancel]
    _ = A i (cols b) := rfl

/-- The Schur prediction depends only on the Boolean row signature on the
core columns and the Boolean column signature on the core rows. -/
lemma schurPrediction_eq_of_coreCodes
    {n l : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsBinary A)
    (rows cols : Fin l ↪ Fin n) {i i' j j' : Fin n}
    (hrowCode : coreRowCode A cols i = coreRowCode A cols i')
    (hcolCode : coreColCode A rows j = coreColCode A rows j') :
    schurPrediction A rows cols i j = schurPrediction A rows cols i' j' := by
  classical
  have hrow := coreRowCode_eq_entries hA cols hrowCode
  have hcol := coreColCode_eq_entries hA rows hcolCode
  change (∑ b : Fin l, A i (cols b) *
      (∑ a : Fin l, (A.submatrix rows cols)⁻¹ b a * A (rows a) j)) =
    ∑ b : Fin l, A i' (cols b) *
      (∑ a : Fin l, (A.submatrix rows cols)⁻¹ b a * A (rows a) j')
  apply Finset.sum_congr rfl
  intro b hb
  rw [hrow b]
  apply congrArg (fun x : ℝ ↦ A i' (cols b) * x)
  apply Finset.sum_congr rfl
  intro a ha
  rw [hcol a]

/-- Every good green cell with green links to the core is reproduced by
the Schur prediction.  Core rows or columns use inverse cancellation;
the outside/outside case uses maximality and the Schur identity. -/
private lemma schurPrediction_eq_on_good_green
    {n l : ℕ} {s : ℝ} (A : Matrix (Fin n) (Fin n) ℝ)
    (red : Fin n → Fin n → Prop)
    (rows cols : Fin l ↪ Fin n)
    (hrows : ∀ a, (redRowDegree red (rows a) : ℝ) ≤ s)
    (hcols : ∀ b, (redColDegree red (cols b) : ℝ) ≤ s)
    (hcoreGreen : ∀ a b, ¬ red (rows a) (cols b))
    (hcore : (A.submatrix rows cols).det ≠ 0)
    (hmax : ∀ rows' cols' : Fin (l + 1) ↪ Fin n,
      (∀ a, (redRowDegree red (rows' a) : ℝ) ≤ s) →
      (∀ b, (redColDegree red (cols' b) : ℝ) ≤ s) →
      (∀ a b, ¬ red (rows' a) (cols' b)) →
        (A.submatrix rows' cols').det = 0)
    {i j : Fin n}
    (hrow : (redRowDegree red i : ℝ) ≤ s)
    (hcol : (redColDegree red j : ℝ) ≤ s)
    (hrowLinks : ∀ b, ¬ red i (cols b))
    (hcolLinks : ∀ a, ¬ red (rows a) j)
    (hij : ¬ red i j) :
    schurPrediction A rows cols i j = A i j := by
  classical
  by_cases hi : i ∈ Set.range rows
  · obtain ⟨a, rfl⟩ := hi
    exact schurPrediction_core_row A rows cols hcore a j
  by_cases hj : j ∈ Set.range cols
  · obtain ⟨b, rfl⟩ := hj
    exact schurPrediction_core_col A rows cols hcore i b
  have hraw :=
    (maximal_core_predicts_green_entry A red rows cols
      hrows hcols hcoreGreen hcore hmax hi hj hrow hcol
      hrowLinks hcolLinks hij).symm
  unfold schurPrediction
  rw [← Matrix.mul_assoc]
  simpa [Matrix.mul_apply] using hraw

private lemma coreRowCandidate_properties
    {n l : ℕ} (red : Fin n → Fin n → Prop) (cols : Fin l ↪ Fin n)
    {s : ℝ} {i : Fin n} (hi : i ∈ coreRowCandidates red cols s) :
    (redRowDegree red i : ℝ) ≤ s ∧ ∀ b, ¬ red i (cols b) := by
  classical
  have hi' := Finset.mem_sdiff.mp hi
  have hiH : i ∉ highRedRowsAt red s := by
    intro h
    exact hi'.2 (Finset.mem_union_left _ h)
  have hiL : i ∉ coreRedLinkedRows red cols := by
    intro h
    exact hi'.2 (Finset.mem_union_right _ h)
  refine ⟨le_of_not_gt (by simpa [highRedRowsAt] using hiH), ?_⟩
  intro b hr
  exact hiL ((mem_coreRedLinkedRows red cols i).2 ⟨b, hr⟩)

private lemma coreColCandidate_properties
    {n l : ℕ} (red : Fin n → Fin n → Prop) (rows : Fin l ↪ Fin n)
    {s : ℝ} {j : Fin n} (hj : j ∈ coreColCandidates red rows s) :
    (redColDegree red j : ℝ) ≤ s ∧ ∀ a, ¬ red (rows a) j := by
  classical
  have hj' := Finset.mem_sdiff.mp hj
  have hjH : j ∉ highRedColsAt red s := by
    intro h
    exact hj'.2 (Finset.mem_union_left _ h)
  have hjL : j ∉ coreRedLinkedCols red rows := by
    intro h
    exact hj'.2 (Finset.mem_union_right _ h)
  refine ⟨le_of_not_gt (by simpa [highRedColsAt] using hjH), ?_⟩
  intro a hr
  exact hjL ((mem_coreRedLinkedCols red rows j).2 ⟨a, hr⟩)

/-- The quantitative rounding construction once a maximal good green core
has been selected.  This is the main finite-matrix step of Lemma 10.3. -/
private lemma exists_binary_approx_from_maximal_core
    {n l : ℕ} {s : ℝ} (A : Matrix (Fin n) (Fin n) ℝ)
    (red : Fin n → Fin n → Prop) (hA : IsBinary A)
    (rows cols : Fin l ↪ Fin n) (hs : 0 < s)
    (hred : (redCount red : ℝ) < s ^ 2)
    (hrows : ∀ a, (redRowDegree red (rows a) : ℝ) ≤ s)
    (hcols : ∀ b, (redColDegree red (cols b) : ℝ) ≤ s)
    (hcoreGreen : ∀ a b, ¬ red (rows a) (cols b))
    (hcore : (A.submatrix rows cols).det ≠ 0)
    (hmax : ∀ rows' cols' : Fin (l + 1) ↪ Fin n,
      (∀ a, (redRowDegree red (rows' a) : ℝ) ≤ s) →
      (∀ b, (redColDegree red (cols' b) : ℝ) ≤ s) →
      (∀ a b, ¬ red (rows' a) (cols' b)) →
        (A.submatrix rows' cols').det = 0) :
    ∃ Q : Matrix (Fin n) (Fin n) ℝ,
      IsBinary Q ∧ Q.rank ≤ l ∧
      (editDistance A Q : ℝ) ≤
        s ^ 2 + 2 * (1 + (l : ℝ) + (2 : ℝ) ^ l) * s * (n : ℝ) := by
  classical
  let dRows := ksssDiscardRows A red cols s
  let dCols := ksssDiscardCols A red rows s
  let Q := maskedSchurPrediction A rows cols dRows dCols
  have hdRows : (dRows.card : ℝ) <
      (1 + (l : ℝ) + (2 : ℝ) ^ l) * s := by
    simpa [dRows] using card_ksssDiscardRows_lt A red cols hs hred hcols
  have hdCols : (dCols.card : ℝ) <
      (1 + (l : ℝ) + (2 : ℝ) ^ l) * s := by
    simpa [dCols] using card_ksssDiscardCols_lt A red rows hs hred hrows
  have hQrank : Q.rank ≤ l := by
    simpa [Q] using maskedSchurPrediction_rank_le A rows cols dRows dCols
  have hQbinary : IsBinary Q := by
    intro i j
    by_cases hi : i ∈ dRows
    · exact Or.inl (by simpa [Q] using
        maskedSchurPrediction_apply_of_row_mem A rows cols dRows dCols hi)
    by_cases hj : j ∈ dCols
    · exact Or.inl (by simpa [Q] using
        maskedSchurPrediction_apply_of_col_mem A rows cols dRows dCols hj)
    obtain ⟨hiGood, hiLinks, hiFiber⟩ :=
      retainedRow_properties A red cols (s := s) (by simpa [dRows] using hi)
    obtain ⟨hjGood, hjLinks, hjFiber⟩ :=
      retainedCol_properties A red rows (s := s) (by simpa [dCols] using hj)
    let rowFiber := (coreRowCandidates red cols s).filter fun i' ↦
      coreRowCode A cols i' = coreRowCode A cols i
    let colFiber := (coreColCandidates red rows s).filter fun j' ↦
      coreColCode A rows j' = coreColCode A rows j
    have hrowFiber : s < (rowFiber.card : ℝ) := by simpa [rowFiber] using hiFiber
    have hcolFiber : s < (colFiber.card : ℝ) := by simpa [colFiber] using hjFiber
    obtain ⟨i', hi', j', hj', hij'⟩ :=
      exists_green_in_large_rectangle red rowFiber colFiber hs
        hrowFiber hcolFiber hred
    have hi'parts := Finset.mem_filter.mp hi'
    have hj'parts := Finset.mem_filter.mp hj'
    obtain ⟨hi'Good, hi'Links⟩ :=
      coreRowCandidate_properties red cols hi'parts.1
    obtain ⟨hj'Good, hj'Links⟩ :=
      coreColCandidate_properties red rows hj'parts.1
    have hcodes : schurPrediction A rows cols i j =
        schurPrediction A rows cols i' j' :=
      schurPrediction_eq_of_coreCodes hA rows cols hi'parts.2.symm hj'parts.2.symm
    have hrep : schurPrediction A rows cols i' j' = A i' j' :=
      schurPrediction_eq_on_good_green A red rows cols hrows hcols
        hcoreGreen hcore hmax hi'Good hj'Good hi'Links hj'Links hij'
    have hQentry : Q i j = A i' j' := by
      calc
        Q i j = schurPrediction A rows cols i j := by
          simpa [Q] using maskedSchurPrediction_apply_of_not_mem
            A rows cols dRows dCols hi hj
        _ = schurPrediction A rows cols i' j' := hcodes
        _ = A i' j' := hrep
    rw [hQentry]
    exact hA i' j'
  have hagrees : ∀ i j, i ∉ dRows → j ∉ dCols →
      ¬ red i j → A i j = Q i j := by
    intro i j hi hj hij
    obtain ⟨hiGood, hiLinks, _⟩ :=
      retainedRow_properties A red cols (s := s) (by simpa [dRows] using hi)
    obtain ⟨hjGood, hjLinks, _⟩ :=
      retainedCol_properties A red rows (s := s) (by simpa [dCols] using hj)
    calc
      A i j = schurPrediction A rows cols i j :=
        (schurPrediction_eq_on_good_green A red rows cols hrows hcols
          hcoreGreen hcore hmax hiGood hjGood hiLinks hjLinks hij).symm
      _ = Q i j := by
        simpa [Q] using (maskedSchurPrediction_apply_of_not_mem
          A rows cols dRows dCols hi hj).symm
  have hEdit := editDistance_le_redCount_add_discard
    A Q red dRows dCols hagrees
  have hEdit' : (editDistance A Q : ℝ) ≤
      (redCount red : ℝ) + (dRows.card : ℝ) * (n : ℝ) +
        (n : ℝ) * (dCols.card : ℝ) := by
    simpa only [Fintype.card_fin] using hEdit
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hrowTerm : (dRows.card : ℝ) * (n : ℝ) ≤
      ((1 + (l : ℝ) + (2 : ℝ) ^ l) * s) * (n : ℝ) :=
    mul_le_mul_of_nonneg_right (le_of_lt hdRows) hn
  have hcolTerm : (n : ℝ) * (dCols.card : ℝ) ≤
      (n : ℝ) * ((1 + (l : ℝ) + (2 : ℝ) ^ l) * s) :=
    mul_le_mul_of_nonneg_left (le_of_lt hdCols) hn
  refine ⟨Q, hQbinary, hQrank, hEdit'.trans ?_⟩
  calc
    (redCount red : ℝ) + (dRows.card : ℝ) * (n : ℝ) +
        (n : ℝ) * (dCols.card : ℝ) ≤
      s ^ 2 + ((1 + (l : ℝ) + (2 : ℝ) ^ l) * s) * (n : ℝ) +
        (n : ℝ) * ((1 + (l : ℝ) + (2 : ℝ) ^ l) * s) :=
      add_le_add (add_le_add (le_of_lt hred) hrowTerm) hcolTerm
    _ = s ^ 2 + 2 * (1 + (l : ℝ) + (2 : ℝ) ^ l) * s * (n : ℝ) := by
      ring

/-- The rank-zero case of Lemma 10.3.  It records the base case of the
maximal nonsingular green-minor construction: every green entry must be
zero, so the zero matrix changes only red cells. -/
theorem ksssLemma103_rank_zero
    (n : ℕ) (η : ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (red : Fin n → Fin n → Prop)
    (hη : 0 < η) (hηone : η ≤ 1) (hA : IsBinary A)
    (hred : (redCount red : ℝ) <
      η ^ 2 / (10 * (2 : ℝ) ^ (0 : ℕ)) ^ 2 * (n : ℝ) ^ 2)
    (hsingular : AllGreenMinorSingular 0 A red) :
    ∃ Q : Matrix (Fin n) (Fin n) ℝ,
      IsBinary Q ∧ Q.rank ≤ 0 ∧
        (editDistance A Q : ℝ) ≤ η * (n : ℝ) ^ 2 := by
  classical
  let entries : Finset (Fin n × Fin n) := Finset.univ.product Finset.univ
  have hsupport :
      entries.filter (fun p ↦ A p.1 p.2 ≠ 0) ⊆
        entries.filter (fun p ↦ red p.1 p.2) := by
    intro p hp
    have hp' := Finset.mem_filter.mp hp
    apply Finset.mem_filter.mpr
    refine ⟨hp'.1, ?_⟩
    by_contra hgreen
    let rows : Fin 1 ↪ Fin n :=
      { toFun := fun _ ↦ p.1
        inj' := fun a b _ ↦ Subsingleton.elim a b }
    let cols : Fin 1 ↪ Fin n :=
      { toFun := fun _ ↦ p.2
        inj' := fun a b _ ↦ Subsingleton.elim a b }
    have hallgreen : ∀ i j, ¬ red (rows i) (cols j) := by
      intro i j
      fin_cases i
      fin_cases j
      change ¬ red (rows 0) (cols 0)
      have hrow0 : rows 0 = p.1 := rfl
      have hcol0 : cols 0 = p.2 := rfl
      rw [hrow0, hcol0]
      exact hgreen
    have hdet := hsingular rows cols hallgreen
    rw [Matrix.det_fin_one] at hdet
    have hentry : A p.1 p.2 = 0 := by
      change (A.submatrix rows cols) 0 0 = 0 at hdet
      change A (rows 0) (cols 0) = 0 at hdet
      have hrow0 : rows 0 = p.1 := rfl
      have hcol0 : cols 0 = p.2 := rfl
      rw [hrow0, hcol0] at hdet
      exact hdet
    exact hp'.2 hentry
  have hcardNat : editDistance A 0 ≤ redCount red := by
    unfold editDistance redCount
    apply Finset.card_le_card
    intro p hp
    exact hsupport hp
  have hcardReal : (editDistance A 0 : ℝ) ≤ redCount red := by
    exact_mod_cast hcardNat
  have hcoeff : η ^ 2 / (10 * (2 : ℝ) ^ (0 : ℕ)) ^ 2 ≤ η := by
    norm_num
    nlinarith [sq_nonneg η]
  have hredle : (redCount red : ℝ) ≤ η * (n : ℝ) ^ 2 := by
    exact le_of_lt (hred.trans_le
      (mul_le_mul_of_nonneg_right hcoeff (sq_nonneg (n : ℝ))))
  refine ⟨0, ?_, by simp, hcardReal.trans hredle⟩
  intro i j
  exact Or.inl rfl

/-- KSSS Lemma 10.3: a binary matrix with very few red cells and no
nonsingular all-green minor of order `r+1` can be rounded to a binary
matrix of rank at most `r` after at most `η n²` edits. -/
theorem ksssLemma103 : KSSSLemma103 := by
  intro r n η A red hη hηone hA hred hsingular
  by_cases hn : n = 0
  · subst n
    have hneg : (redCount red : ℝ) < 0 := by simpa using hred
    exact (not_lt_of_ge (Nat.cast_nonneg (redCount red)) hneg).elim
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  obtain ⟨s, hsdef, hs, hredSq, l, hlr, rows, cols,
      hrows, hcols, hcoreGreen, hcore, hmax, hbadRows, hbadCols⟩ :=
    exists_ksss_maximal_core A red hnpos hη hred hsingular
  obtain ⟨Q, hQbinary, hQrank, hQedit⟩ :=
    exists_binary_approx_from_maximal_core A red hA rows cols hs hredSq
      hrows hcols hcoreGreen hcore hmax
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hnpos
  let p : ℝ := (2 : ℝ) ^ r
  have hp : 0 < p := by
    dsimp [p]
    positivity
  have hpone : 1 ≤ p := by
    dsimp [p]
    exact one_le_pow₀ (by norm_num)
  have hlpow : (2 : ℝ) ^ l ≤ p := by
    dsimp [p]
    exact pow_le_pow_right₀ (by norm_num) hlr
  have hloneNat : l + 1 ≤ 2 ^ r :=
    (Nat.add_le_add_right hlr 1).trans r.lt_two_pow_self
  have hlone : (l : ℝ) + 1 ≤ p := by
    dsimp [p]
    exact_mod_cast hloneNat
  let c : ℝ := 1 + (l : ℝ) + (2 : ℝ) ^ l
  have hc : c ≤ 2 * p := by
    dsimp [c]
    linarith
  have hscale : 10 * p * s = η * (n : ℝ) := by
    rw [hsdef]
    dsimp [p]
    field_simp
    <;> ring
  have hsMulP : s ≤ p * s := by
    simpa [one_mul] using mul_le_mul_of_nonneg_right hpone (le_of_lt hs)
  have hsEta : s ≤ η * (n : ℝ) / 10 := by
    nlinarith [hscale]
  have hηn : η * (n : ℝ) ≤ n := by
    simpa [one_mul] using mul_le_mul_of_nonneg_right hηone (le_of_lt hnreal)
  have hsN : s ≤ (n : ℝ) / 10 := by
    linarith
  have hsSq : s ^ 2 ≤ (1 / 100 : ℝ) * η * (n : ℝ) ^ 2 := by
    have hmul := mul_le_mul hsEta hsN (le_of_lt hs)
      (div_nonneg (mul_nonneg (le_of_lt hη) (le_of_lt hnreal)) (by norm_num))
    nlinarith
  have hcsn : 2 * c * s * (n : ℝ) ≤ 4 * p * s * (n : ℝ) := by
    have hc2 : 2 * c ≤ 4 * p := by nlinarith
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hc2 (le_of_lt hs)) (le_of_lt hnreal)
  have hscaleN : 10 * p * s * (n : ℝ) = η * (n : ℝ) ^ 2 := by
    nlinarith [congrArg (fun x : ℝ ↦ x * (n : ℝ)) hscale]
  have hterm : 2 * c * s * (n : ℝ) ≤
      (2 / 5 : ℝ) * η * (n : ℝ) ^ 2 := by
    calc
      2 * c * s * (n : ℝ) ≤ 4 * p * s * (n : ℝ) := hcsn
      _ = (2 / 5 : ℝ) * η * (n : ℝ) ^ 2 := by nlinarith
  have htotal : s ^ 2 + 2 * c * s * (n : ℝ) ≤ η * (n : ℝ) ^ 2 := by
    calc
      s ^ 2 + 2 * c * s * (n : ℝ) ≤
          (1 / 100 : ℝ) * η * (n : ℝ) ^ 2 +
            (2 / 5 : ℝ) * η * (n : ℝ) ^ 2 :=
        add_le_add hsSq hterm
      _ ≤ η * (n : ℝ) ^ 2 := by
        nlinarith [mul_nonneg (le_of_lt hη) (sq_nonneg (n : ℝ))]
  refine ⟨Q, hQbinary, hQrank.trans hlr, ?_⟩
  exact hQedit.trans (by simpa [c] using htotal)

/-- The exact finite assertion of KSSS Proposition 10.2.  The constant is
uniform in the matrix order and in the error parameter, and depends only on
the target rank. -/
def KSSSProposition102 : Prop :=
  ∀ r : ℕ, ∃ Cr : ℝ, 0 < Cr ∧
    ∀ (n : ℕ) (ε : ℝ) (A B : Matrix (Fin n) (Fin n) ℝ),
      0 ≤ ε → IsBinary A → B.rank ≤ r →
      frobeniusSq (A - B) ≤ ε * (n : ℝ) ^ 2 →
        ∃ Q : Matrix (Fin n) (Fin n) ℝ,
          IsBinary Q ∧ Q.rank ≤ r ∧
            frobeniusSq (A - Q) ≤ Cr * Real.sqrt ε * (n : ℝ) ^ 2

/-- The formal reduction of Proposition 10.2 to Lemma 10.3 and the
fixed-dimensional determinant-separation estimate.  This is the complete
constant bookkeeping in the rounding argument; no matrix-order dependent
constant occurs. -/
theorem proposition102_of_lemma103_and_minorSeparation
    (h103 : KSSSLemma103)
    (hseparation : ∀ r : ℕ, ∃ τ : ℝ, BinaryMinorSeparationAt r τ) :
    KSSSProposition102 := by
  intro r
  obtain ⟨τ, hsep⟩ := hseparation r
  have hτ : 0 < τ := hsep.1
  let d : ℝ := 10 * (2 : ℝ) ^ r
  have hd : 0 < d := by
    dsimp [d]
    positivity
  let Cr : ℝ := d * Real.sqrt (2 / τ)
  have hratio : 0 < (2 : ℝ) / τ := div_pos (by norm_num) hτ
  have hCr : 0 < Cr := by
    dsimp [Cr]
    exact mul_pos hd (Real.sqrt_pos.2 hratio)
  refine ⟨Cr, hCr, ?_⟩
  intro n ε A B hε hA hB hclose
  by_cases hn : n = 0
  · subst n
    have hAz : A = 0 := by
      ext i
      exact Fin.elim0 i
    subst A
    refine ⟨0, ?_, by simp, ?_⟩
    · intro i
      exact Fin.elim0 i
    · simp [frobeniusSq]
  by_cases hεzero : ε = 0
  · subst ε
    have hzero : frobeniusSq (A - B) = 0 :=
      le_antisymm (by simpa using hclose) (frobeniusSq_nonneg (A - B))
    have hAB : A = B := sub_eq_zero.mp ((frobeniusSq_eq_zero_iff (A - B)).mp hzero)
    subst B
    refine ⟨A, hA, hB, ?_⟩
    simp [frobeniusSq]
  have hεpos : 0 < ε := lt_of_le_of_ne hε (Ne.symm hεzero)
  have hnreal : (0 : ℝ) < n := by
    exact_mod_cast Nat.pos_of_ne_zero hn
  let η : ℝ := Cr * Real.sqrt ε
  have hηpos : 0 < η := by
    exact mul_pos hCr (Real.sqrt_pos.2 hεpos)
  by_cases hηle : η ≤ 1
  · let red : Fin n → Fin n → Prop :=
      fun i j ↦ τ < (A i j - B i j) ^ 2
    have hredmul : (redCount red : ℝ) * τ ≤ frobeniusSq (A - B) := by
      simpa [red] using
        (threshold_mul_redCount_le_frobeniusSq A B (le_of_lt hτ))
    have hredcount :
        (redCount red : ℝ) ≤ ε / τ * (n : ℝ) ^ 2 := by
      calc
        (redCount red : ℝ) ≤ (ε * (n : ℝ) ^ 2) / τ :=
          (le_div_iff₀ hτ).2 (hredmul.trans hclose)
        _ = ε / τ * (n : ℝ) ^ 2 := by ring
    have hsratio : Real.sqrt (2 / τ) ^ 2 = 2 / τ :=
      Real.sq_sqrt (le_of_lt hratio)
    have hsε : Real.sqrt ε ^ 2 = ε := Real.sq_sqrt hε
    have heta : η ^ 2 / d ^ 2 = 2 * ε / τ := by
      dsimp [η, Cr]
      rw [mul_pow, mul_pow, hsratio, hsε]
      field_simp [ne_of_gt hd]
      <;> ring
    have hbase : 0 < ε / τ * (n : ℝ) ^ 2 :=
      mul_pos (div_pos hεpos hτ) (sq_pos_of_pos hnreal)
    have hredstrict :
        (redCount red : ℝ) <
          η ^ 2 / (10 * (2 : ℝ) ^ r) ^ 2 * (n : ℝ) ^ 2 := by
      change (redCount red : ℝ) < η ^ 2 / d ^ 2 * (n : ℝ) ^ 2
      rw [heta]
      calc
        (redCount red : ℝ) ≤ ε / τ * (n : ℝ) ^ 2 := hredcount
        _ < 2 * (ε / τ * (n : ℝ) ^ 2) := by nlinarith
        _ = 2 * ε / τ * (n : ℝ) ^ 2 := by ring
    have hgreen : AllGreenMinorSingular r A red := by
      simpa [red] using allGreenMinorSingular_of_separation hsep hA hB
    obtain ⟨Q, hQ, hQrank, hQedit⟩ :=
      h103 r n η A red hηpos hηle hA hredstrict hgreen
    refine ⟨Q, hQ, hQrank, ?_⟩
    calc
      frobeniusSq (A - Q) = (editDistance A Q : ℝ) :=
        frobeniusSq_sub_eq_editDistance hA hQ
      _ ≤ η * (n : ℝ) ^ 2 := hQedit
      _ = Cr * Real.sqrt ε * (n : ℝ) ^ 2 := rfl
  · have honeη : (1 : ℝ) < η := lt_of_not_ge hηle
    have hzeroBinary : IsBinary (0 : Matrix (Fin n) (Fin n) ℝ) := by
      intro i j
      exact Or.inl rfl
    refine ⟨0, hzeroBinary, by simp, ?_⟩
    have hAnorm : frobeniusSq A ≤ (n : ℝ) ^ 2 := by
      simpa [pow_two] using frobeniusSq_le_card_mul_card_of_binary hA
    calc
      frobeniusSq (A - 0) = frobeniusSq A := by simp
      _ ≤ (n : ℝ) ^ 2 := hAnorm
      _ ≤ η * (n : ℝ) ^ 2 := by
        nlinarith [sq_nonneg (n : ℝ)]
      _ = Cr * Real.sqrt ε * (n : ℝ) ^ 2 := rfl

/-- KSSS Proposition 10.2, obtained from Lemma 10.3 and the uniform
fixed-dimensional determinant-separation theorem. -/
theorem ksssProposition102 : KSSSProposition102 :=
  proposition102_of_lemma103_and_minorSeparation
    ksssLemma103 binaryMinorSeparation_exists

/-- The squared Frobenius norm is unchanged when both index types are
relabelled by equivalences. -/
lemma frobeniusSq_submatrix_equiv
    {ι : Type u} {κ : Type v} {ι' : Type u'} {κ' : Type v'}
    [Fintype ι] [Fintype κ] [Fintype ι'] [Fintype κ']
    (A : Matrix ι κ ℝ) (eι : ι' ≃ ι) (eκ : κ' ≃ κ) :
    frobeniusSq (A.submatrix eι eκ) = frobeniusSq A := by
  rw [frobeniusSq, frobeniusSq]
  simp only [Matrix.submatrix_apply]
  calc
    (∑ i : ι', ∑ j : κ', (A (eι i) (eκ j)) ^ 2) =
        ∑ i : ι', ∑ j : κ, (A (eι i) j) ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _hi
      exact eκ.sum_comp (fun j ↦ (A (eι i) j) ^ 2)
    _ = ∑ i : ι, ∑ j : κ, (A i j) ^ 2 :=
      eι.sum_comp (fun i ↦ ∑ j : κ, (A i j) ^ 2)

/-- Proposition 10.2 after relabelling two arbitrary finite index types of
the same prescribed cardinality.  This is the form used on each pair of
equal buckets in Lemma 10.1. -/
theorem ksssProposition102_equalCard
    {ι : Type u} {κ : Type v} [Fintype ι] [Fintype κ] (r : ℕ) :
    ∃ Cr : ℝ, 0 < Cr ∧
      ∀ (q : ℕ), Fintype.card ι = q → Fintype.card κ = q →
        ∀ (ε : ℝ) (A B : Matrix ι κ ℝ),
          0 ≤ ε → IsBinary A → B.rank ≤ r →
          frobeniusSq (A - B) ≤ ε * (q : ℝ) ^ 2 →
            ∃ Q : Matrix ι κ ℝ,
              IsBinary Q ∧ Q.rank ≤ r ∧
                frobeniusSq (A - Q) ≤ Cr * Real.sqrt ε * (q : ℝ) ^ 2 := by
  obtain ⟨Cr, hCr, hround⟩ := ksssProposition102 r
  refine ⟨Cr, hCr, ?_⟩
  intro q hι hκ ε A B hε hA hBrank hclose
  let eι : ι ≃ Fin q := Fintype.equivFinOfCardEq hι
  let eκ : κ ≃ Fin q := Fintype.equivFinOfCardEq hκ
  let A₀ : Matrix (Fin q) (Fin q) ℝ := A.reindex eι eκ
  let B₀ : Matrix (Fin q) (Fin q) ℝ := B.reindex eι eκ
  have hA₀ : IsBinary A₀ := by
    intro i j
    simpa [A₀, Matrix.reindex_apply] using hA (eι.symm i) (eκ.symm j)
  have hB₀rank : B₀.rank ≤ r := by
    rw [show B₀.rank = B.rank by
      simpa [B₀] using Matrix.rank_reindex eι eκ B]
    exact hBrank
  have hclose₀ : frobeniusSq (A₀ - B₀) ≤ ε * (q : ℝ) ^ 2 := by
    have hsub : A₀ - B₀ = (A - B).submatrix eι.symm eκ.symm := by
      rfl
    rw [hsub, frobeniusSq_submatrix_equiv]
    exact hclose
  obtain ⟨Q₀, hQ₀, hQ₀rank, hQ₀close⟩ :=
    hround q ε A₀ B₀ hε hA₀ hB₀rank hclose₀
  let Q : Matrix ι κ ℝ := Q₀.submatrix eι eκ
  refine ⟨Q, ?_, ?_, ?_⟩
  · intro i j
    simpa [Q] using hQ₀ (eι i) (eκ j)
  · rw [show Q.rank = Q₀.rank by
      simpa [Q] using Matrix.rank_submatrix Q₀ eι eκ]
    exact hQ₀rank
  · have hsub : A - Q = (A₀ - Q₀).submatrix eι eκ := by
      ext i j
      simp [A₀, Q, Matrix.reindex_apply]
    rw [hsub, frobeniusSq_submatrix_equiv]
    exact hQ₀close

/-- Vertices in one bucket of a finite bucket map. -/
noncomputable def bucketFiber {n m : ℕ} (bucket : Fin n → Fin m) (j : Fin m) :
    Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun i ↦ bucket i = j

@[simp] lemma mem_bucketFiber {n m : ℕ} (bucket : Fin n → Fin m)
    (j : Fin m) (i : Fin n) : i ∈ bucketFiber bucket j ↔ bucket i = j := by
  classical
  simp [bucketFiber]

/-- The buckets all have one common cardinality.  Since `bucket` is a total
map, its fibers are automatically disjoint and cover the vertex set. -/
def HasEqualBuckets {n m : ℕ} (bucket : Fin n → Fin m) : Prop :=
  ∃ s : ℕ, 0 < s ∧ ∀ j, (bucketFiber bucket j).card = s

/-- A finite sum splits exactly over the fibers of a bucket map. -/
lemma sum_bucketFibers {n m : ℕ} (bucket : Fin n → Fin m)
    {R : Type*} [AddCommMonoid R] (f : Fin n → R) :
    (∑ a : Fin m, ∑ i : bucketFiber bucket a, f i.1) = ∑ i : Fin n, f i := by
  classical
  calc
    (∑ a : Fin m, ∑ i : bucketFiber bucket a, f i.1) =
        ∑ a : Fin m, ∑ i ∈ bucketFiber bucket a, f i := by
      apply Finset.sum_congr rfl
      intro a _ha
      simpa using Finset.sum_attach (bucketFiber bucket a) f
    _ = ∑ i : Fin n, f i := by
      simpa [bucketFiber] using
        (Finset.sum_fiberwise (Finset.univ : Finset (Fin n)) bucket f)

/-- The fiber cardinalities of a bucket map add up to the cardinality of
its domain. -/
lemma sum_card_bucketFiber {n m : ℕ} (bucket : Fin n → Fin m) :
    (∑ a : Fin m, (bucketFiber bucket a).card) = n := by
  simpa using sum_bucketFibers bucket (fun _ ↦ (1 : ℕ))

/-- If every one of `m` buckets has size `s`, then the ambient vertex set
has exactly `m*s` elements. -/
lemma card_eq_bucketCount_mul_bucketSize {n m s : ℕ} (bucket : Fin n → Fin m)
    (hs : ∀ a, (bucketFiber bucket a).card = s) : n = m * s := by
  calc
    n = ∑ a : Fin m, (bucketFiber bucket a).card :=
      (sum_card_bucketFiber bucket).symm
    _ = ∑ _a : Fin m, s := by
      apply Finset.sum_congr rfl
      intro a _ha
      exact hs a
    _ = m * s := by simp

/-- Restriction of a matrix to a pair of buckets. -/
noncomputable def bucketBlock {n m : ℕ} (bucket : Fin n → Fin m)
    (M : Matrix (Fin n) (Fin n) ℝ) (j k : Fin m) :
    Matrix (bucketFiber bucket j) (bucketFiber bucket k) ℝ :=
  M.submatrix Subtype.val Subtype.val

/-- Every block of `M` has rank at most `r`. -/
def BlockRankAtMost {n m : ℕ} (r : ℕ) (bucket : Fin n → Fin m)
    (M : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ j k, (bucketBlock bucket M j k).rank ≤ r

/-- The squared Frobenius norm is the sum of the squared Frobenius norms
of all ordered bucket blocks. -/
lemma frobeniusSq_eq_sum_bucketBlocks {n m : ℕ} (bucket : Fin n → Fin m)
    (M : Matrix (Fin n) (Fin n) ℝ) :
    frobeniusSq M =
      ∑ a : Fin m, ∑ b : Fin m, frobeniusSq (bucketBlock bucket M a b) := by
  classical
  simp only [frobeniusSq, bucketBlock, Matrix.submatrix_apply]
  calc
    (∑ i : Fin n, ∑ j : Fin n, M i j ^ 2) =
        ∑ i : Fin n, ∑ b : Fin m,
          ∑ j : bucketFiber bucket b, M i j.1 ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _hi
      exact (sum_bucketFibers bucket (fun j ↦ M i j ^ 2)).symm
    _ = ∑ a : Fin m, ∑ i : bucketFiber bucket a,
          ∑ b : Fin m, ∑ j : bucketFiber bucket b, M i.1 j.1 ^ 2 := by
      exact (sum_bucketFibers bucket (fun i ↦
        ∑ b : Fin m, ∑ j : bucketFiber bucket b, M i j.1 ^ 2)).symm
    _ = ∑ a : Fin m, ∑ b : Fin m,
          ∑ i : bucketFiber bucket a,
            ∑ j : bucketFiber bucket b, M i.1 j.1 ^ 2 := by
      apply Finset.sum_congr rfl
      intro a _ha
      rw [Finset.sum_comm]

/-- Ordered pairs in `S` satisfying a finite relation. -/
noncomputable def relationPairs {α : Type*} [DecidableEq α]
    (bad : α → α → Prop) (S : Finset α) : Finset (α × α) := by
  classical
  exact (S.product S).filter fun p ↦ bad p.1 p.2

/-- The number of `bad` partners of `v` inside `S`. -/
noncomputable def relationDegree {α : Type*} [DecidableEq α]
    (bad : α → α → Prop) (S : Finset α) (v : α) : ℕ := by
  classical
  exact (S.filter fun w ↦ bad v w).card

/-- Double-counting ordered related pairs by their first coordinate. -/
lemma card_relationPairs_eq_sum_degree {α : Type*} [DecidableEq α]
    (bad : α → α → Prop) (S : Finset α) :
    (relationPairs bad S).card = ∑ v ∈ S, relationDegree bad S v := by
  classical
  calc
    (relationPairs bad S).card =
        ∑ p ∈ S.product S, if bad p.1 p.2 then 1 else 0 := by
      unfold relationPairs
      rw [Finset.card_filter]
    _ = ∑ v ∈ S, ∑ w ∈ S, if bad v w then 1 else 0 :=
      Finset.sum_product S S (fun p ↦ if bad p.1 p.2 then 1 else 0)
    _ = ∑ v ∈ S, relationDegree bad S v := by
      apply Finset.sum_congr rfl
      intro v _hv
      unfold relationDegree
      rw [Finset.card_filter]

/-- Restricting the ambient set cannot create new ordered related pairs. -/
lemma card_relationPairs_mono {α : Type*} [DecidableEq α]
    (bad : α → α → Prop) {S T : Finset α} (hTS : T ⊆ S) :
    (relationPairs bad T).card ≤ (relationPairs bad S).card := by
  classical
  apply Finset.card_le_card
  intro p hp
  unfold relationPairs at hp ⊢
  have hpFilter := Finset.mem_filter.mp hp
  have hpProduct := Finset.mem_product.mp hpFilter.1
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_product.mpr ⟨hTS hpProduct.1, hTS hpProduct.2⟩,
    hpFilter.2⟩

/-- Greedy extraction of a pairwise-good set.  The invariant says that `L`
vertices must remain after paying at most `q` vertices for each selected
point; the strict ordered-pair budget supplies a point of bad degree `< q`
at every step. -/
lemma exists_pairwise_not_relation_of_pair_budget
    {α : Type*} [DecidableEq α] (bad : α → α → Prop)
    (hbadSymm : Symmetric bad) (S : Finset α) (L q k : ℕ)
    (hL : 0 < L) (hsize : L + k * q ≤ S.card)
    (hpairs : (relationPairs bad S).card < q * L) :
    ∃ T : Finset α, T ⊆ S ∧ T.card = k ∧
      Set.Pairwise (T : Set α) fun x y ↦ ¬ bad x y := by
  classical
  induction k generalizing S with
  | zero =>
      exact ⟨∅, Finset.empty_subset _, by simp, by simp⟩
  | succ k ih =>
      have hsumlt :
          (∑ v ∈ S, relationDegree bad S v) < ∑ _v ∈ S, q := by
        rw [← card_relationPairs_eq_sum_degree]
        calc
          (relationPairs bad S).card < q * L := hpairs
          _ ≤ q * S.card := Nat.mul_le_mul_left q (by omega)
          _ = ∑ _v ∈ S, q := by simp [Nat.mul_comm]
      obtain ⟨v, hvS, hvdeg⟩ := Finset.exists_lt_of_sum_lt hsumlt
      let removed : Finset α := insert v (S.filter fun w ↦ bad v w)
      let U : Finset α := S \ removed
      have hremovedSub : removed ⊆ S := by
        intro x hx
        simp only [removed, Finset.mem_insert, Finset.mem_filter] at hx
        rcases hx with rfl | hx
        · exact hvS
        · exact hx.1
      have hremovedCard : removed.card ≤ q := by
        have hinsert :
            removed.card ≤ 1 + (S.filter fun w ↦ bad v w).card := by
          simpa [removed, Nat.add_comm] using
            (Finset.card_insert_le v (S.filter fun w : α ↦ bad v w))
        have hfilter :
            (S.filter fun w ↦ bad v w).card = relationDegree bad S v := by
          rfl
        rw [hfilter] at hinsert
        omega
      have hUSub : U ⊆ S := Finset.sdiff_subset
      have hremovedCard_le : removed.card ≤ S.card :=
        Finset.card_le_card hremovedSub
      have hUeq : U.card = S.card - removed.card := by
        dsimp [U]
        exact Finset.card_sdiff_of_subset hremovedSub
      have hUcard : S.card ≤ U.card + q := by
        rw [hUeq]
        omega
      have hUsize : L + k * q ≤ U.card := by
        have hsize' : L + k * q + q ≤ S.card := by
          simpa [Nat.succ_mul, add_assoc] using hsize
        omega
      have hUpairs : (relationPairs bad U).card < q * L :=
        (card_relationPairs_mono bad hUSub).trans_lt hpairs
      obtain ⟨T, hTU, hTcard, hTpair⟩ := ih U hUsize hUpairs
      refine ⟨insert v T, ?_, ?_, ?_⟩
      · exact Finset.insert_subset hvS (hTU.trans hUSub)
      · have hvT : v ∉ T := by
          intro hv
          have hvU := Finset.mem_sdiff.mp (hTU hv)
          exact hvU.2 (by simp [removed])
        simp [hvT, hTcard]
      · rw [Finset.coe_insert]
        apply Set.Pairwise.insert hTpair
        intro x hxT hxv
        have hxU := hTU hxT
        have hxnot : x ∉ removed := (Finset.mem_sdiff.mp hxU).2
        have hnotvx : ¬ bad v x := by
          intro hvx
          exact hxnot (by
            simp only [removed, Finset.mem_insert, Finset.mem_filter]
            exact Or.inr ⟨hUSub hxU, hvx⟩)
        exact ⟨hnotvx, fun hxvbad ↦ hnotvx (hbadSymm hxvbad)⟩

/-- Squared error contributed by one ordered bucket block. -/
noncomputable def bucketError {n m : ℕ} (bucket : Fin n → Fin m)
    (M : Matrix (Fin n) (Fin n) ℝ) (a b : Fin m) : ℝ :=
  frobeniusSq (bucketBlock bucket M a b)

lemma bucketError_nonneg {n m : ℕ} (bucket : Fin n → Fin m)
    (M : Matrix (Fin n) (Fin n) ℝ) (a b : Fin m) :
    0 ≤ bucketError bucket M a b :=
  frobeniusSq_nonneg _

/-- A symmetric bad-pair relation: the errors in the two directed blocks
together reach the prescribed threshold. -/
def badBlockPair {n m : ℕ} (bucket : Fin n → Fin m)
    (M : Matrix (Fin n) (Fin n) ℝ) (θ : ℝ) (a b : Fin m) : Prop :=
  θ ≤ bucketError bucket M a b + bucketError bucket M b a

lemma badBlockPair_symmetric {n m : ℕ} (bucket : Fin n → Fin m)
    (M : Matrix (Fin n) (Fin n) ℝ) (θ : ℝ) :
    Symmetric (badBlockPair bucket M θ) := by
  intro a b hab
  simpa [badBlockPair, add_comm] using hab

/-- The total weight of all bad ordered bucket pairs is bounded by twice
the global squared Frobenius error. -/
lemma threshold_mul_card_badBlockPairs_le {n m : ℕ}
    (bucket : Fin n → Fin m) (M : Matrix (Fin n) (Fin n) ℝ)
    {θ : ℝ} (hθ : 0 ≤ θ) :
    ((relationPairs (badBlockPair bucket M θ)
        (Finset.univ : Finset (Fin m))).card : ℝ) * θ ≤
      2 * frobeniusSq M := by
  classical
  let bad := badBlockPair bucket M θ
  let P := relationPairs bad (Finset.univ : Finset (Fin m))
  let E : Fin m → Fin m → ℝ := bucketError bucket M
  calc
    (P.card : ℝ) * θ = ∑ _p ∈ P, θ := by simp
    _ ≤ ∑ p ∈ P, (E p.1 p.2 + E p.2 p.1) := by
      apply Finset.sum_le_sum
      intro p hp
      have hpbad : bad p.1 p.2 := by
        change p ∈ relationPairs bad (Finset.univ : Finset (Fin m)) at hp
        unfold relationPairs at hp
        exact (Finset.mem_filter.mp hp).2
      exact hpbad
    _ ≤ ∑ p ∈ (Finset.univ : Finset (Fin m)).product Finset.univ,
          (E p.1 p.2 + E p.2 p.1) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro p hp
        change p ∈ relationPairs bad (Finset.univ : Finset (Fin m)) at hp
        unfold relationPairs at hp
        exact (Finset.mem_filter.mp hp).1
      · intro p _hp _hnot
        exact add_nonneg (bucketError_nonneg bucket M _ _)
          (bucketError_nonneg bucket M _ _)
    _ = ∑ a : Fin m, ∑ b : Fin m, (E a b + E b a) := by
      exact Finset.sum_product (Finset.univ : Finset (Fin m))
        (Finset.univ : Finset (Fin m))
        (fun p ↦ E p.1 p.2 + E p.2 p.1)
    _ = (∑ a : Fin m, ∑ b : Fin m, E a b) +
          ∑ a : Fin m, ∑ b : Fin m, E b a := by
      simp_rw [Finset.sum_add_distrib]
    _ = 2 * ∑ a : Fin m, ∑ b : Fin m, E a b := by
      rw [Finset.sum_comm (f := fun a b ↦ E b a)]
      ring
    _ = 2 * frobeniusSq M := by
      rw [frobeniusSq_eq_sum_bucketBlocks bucket M]
      rfl

/-- Select `k` buckets with low error in both directed cross-blocks.  This
is the deterministic double-counting version of the random bucket selection
in the proof of KSSS Lemma 10.1. -/
lemma exists_lowError_bucket_subset {n m : ℕ}
    (bucket : Fin n → Fin m) (M : Matrix (Fin n) (Fin n) ℝ)
    {θ : ℝ} {L q k : ℕ} (hθ : 0 < θ) (hL : 0 < L)
    (hsize : L + k * q ≤ m)
    (hbudget : 2 * frobeniusSq M < (q * L : ℕ) * θ) :
    ∃ T : Finset (Fin m), T.card = k ∧
      Set.Pairwise (T : Set (Fin m)) fun a b ↦
        bucketError bucket M a b + bucketError bucket M b a < θ := by
  classical
  let bad := badBlockPair bucket M θ
  have hweighted :
      ((relationPairs bad (Finset.univ : Finset (Fin m))).card : ℝ) * θ ≤
        2 * frobeniusSq M := by
    simpa only [bad] using threshold_mul_card_badBlockPairs_le bucket M hθ.le
  have hcardReal :
      ((relationPairs bad (Finset.univ : Finset (Fin m))).card : ℝ) < q * L := by
    have hmul :
        ((relationPairs bad (Finset.univ : Finset (Fin m))).card : ℝ) * θ <
          ((q * L : ℕ) : ℝ) * θ := hweighted.trans_lt hbudget
    exact (mul_lt_mul_iff_left₀ hθ).mp (by simpa using hmul)
  have hcard :
      (relationPairs bad (Finset.univ : Finset (Fin m))).card < q * L := by
    exact_mod_cast hcardReal
  obtain ⟨T, _hTuniv, hTcard, hTpair⟩ :=
    exists_pairwise_not_relation_of_pair_budget bad
      (badBlockPair_symmetric bucket M θ) Finset.univ L q k hL
      (by simpa using hsize) hcard
  refine ⟨T, hTcard, ?_⟩
  intro a ha b hb hab
  have hnot := hTpair ha hb hab
  simpa [bad, badBlockPair, not_le] using hnot

/-- A quantitative pigeonhole principle packaged in the form needed for a
common refinement: if `q` copies of the code space fit inside the domain,
there is a `q`-element subset on which the code is constant. -/
lemma exists_constant_code_subset
    {α : Type u} {β : Type v} [Fintype α] [Fintype β] [Nonempty β]
    (code : α → β) (q : ℕ) (hfit : Fintype.card β * q ≤ Fintype.card α) :
    ∃ T : Finset α, T.card = q ∧ ∃ c : β, ∀ x ∈ T, code x = c := by
  classical
  obtain ⟨c, hc⟩ := Fintype.exists_le_card_fiber_of_mul_le_card
    (f := code) hfit
  let fiber : Finset α := Finset.univ.filter fun x ↦ code x = c
  have hfiber : q ≤ fiber.card := by simpa [fiber] using hc
  obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq hfiber
  refine ⟨T, hTcard, c, ?_⟩
  intro x hx
  exact (Finset.mem_filter.mp (hTsub hx)).2

/-- A family of binary rank-`r` matrices on all ordered pairs of a selected
family of buckets. -/
structure RoundedBucketSystem {n m D r : ℕ} (bucket : Fin n → Fin m)
    (sel : Fin D → Fin m) where
  Q : ∀ a b : Fin D,
    Matrix (bucketFiber bucket (sel a)) (bucketFiber bucket (sel b)) ℝ
  binary : ∀ a b, IsBinary (Q a b)
  rank_le : ∀ a b, (Q a b).rank ≤ r

noncomputable def roundedBlockRowCode
    {n m D r : ℕ} {bucket : Fin n → Fin m} {sel : Fin D → Fin m}
    (sys : RoundedBucketSystem (r := r) bucket sel) (a b : Fin D) :
    bucketFiber bucket (sel a) → Fin (2 ^ r) :=
  Classical.choose
    (binary_low_rank_partition r (sys.Q a b) (sys.binary a b) (sys.rank_le a b))

noncomputable def roundedBlockColCode
    {n m D r : ℕ} {bucket : Fin n → Fin m} {sel : Fin D → Fin m}
    (sys : RoundedBucketSystem (r := r) bucket sel) (a b : Fin D) :
    bucketFiber bucket (sel b) → Fin (2 ^ r) :=
  Classical.choose (Classical.choose_spec
    (binary_low_rank_partition r (sys.Q a b) (sys.binary a b) (sys.rank_le a b)))

lemma roundedBlock_eq_of_codes
    {n m D r : ℕ} {bucket : Fin n → Fin m} {sel : Fin D → Fin m}
    (sys : RoundedBucketSystem (r := r) bucket sel) (a b : Fin D)
    {i i' : bucketFiber bucket (sel a)}
    {j j' : bucketFiber bucket (sel b)}
    (hi : roundedBlockRowCode sys a b i = roundedBlockRowCode sys a b i')
    (hj : roundedBlockColCode sys a b j = roundedBlockColCode sys a b j') :
    sys.Q a b i j = sys.Q a b i' j' := by
  exact Classical.choose_spec (Classical.choose_spec
    (binary_low_rank_partition r (sys.Q a b) (sys.binary a b) (sys.rank_le a b))) hi hj

/-- The joint code of a vertex records its row code in every outgoing
rounded block and its column code in every incoming rounded block. -/
noncomputable def roundedVertexCode
    {n m D r : ℕ} {bucket : Fin n → Fin m} {sel : Fin D → Fin m}
    (sys : RoundedBucketSystem (r := r) bucket sel) (a : Fin D)
    (i : bucketFiber bucket (sel a)) :
    Fin D → (Fin (2 ^ r) × Fin (2 ^ r)) :=
  fun b ↦ (roundedBlockRowCode sys a b i, roundedBlockColCode sys b a i)

/-- Simultaneously refine every selected bucket by all incident row and
column codes, and retain equally many vertices in one code fibre of each
bucket. -/
theorem exists_commonRefinement_of_roundedBucketSystem
    {n m D r s q : ℕ} {bucket : Fin n → Fin m} {sel : Fin D → Fin m}
    (sys : RoundedBucketSystem (r := r) bucket sel)
    (hs : ∀ a, (bucketFiber bucket (sel a)).card = s)
    (hfit : Fintype.card (Fin D → (Fin (2 ^ r) × Fin (2 ^ r))) * q ≤ s) :
    ∃ J : ∀ a : Fin D, Finset (bucketFiber bucket (sel a)),
      (∀ a, (J a).card = q) ∧
      ∀ a ⦃i i'⦄, i ∈ J a → i' ∈ J a →
        roundedVertexCode sys a i = roundedVertexCode sys a i' := by
  classical
  have hex : ∀ a : Fin D,
      ∃ T : Finset (bucketFiber bucket (sel a)), T.card = q ∧
        ∀ ⦃i i'⦄, i ∈ T → i' ∈ T →
          roundedVertexCode sys a i = roundedVertexCode sys a i' := by
    intro a
    have hfitA :
        Fintype.card (Fin D → (Fin (2 ^ r) × Fin (2 ^ r))) * q ≤
          Fintype.card (bucketFiber bucket (sel a)) := by
      rw [Fintype.card_coe, hs a]
      exact hfit
    obtain ⟨T, hTcard, c, hc⟩ :=
      exists_constant_code_subset (roundedVertexCode sys a) q hfitA
    refine ⟨T, hTcard, ?_⟩
    intro i i' hi hi'
    exact (hc i hi).trans (hc i' hi').symm
  let J : ∀ a : Fin D, Finset (bucketFiber bucket (sel a)) :=
    fun a ↦ Classical.choose (hex a)
  refine ⟨J, ?_, ?_⟩
  · intro a
    exact (Classical.choose_spec (hex a)).1
  · intro a i i' hi hi'
    exact (Classical.choose_spec (hex a)).2 hi hi'

/-- Every rounded matrix is constant on the rectangles supplied by the
common refinement. -/
lemma roundedBlock_constant_on_commonRefinement
    {n m D r : ℕ} {bucket : Fin n → Fin m} {sel : Fin D → Fin m}
    (sys : RoundedBucketSystem (r := r) bucket sel)
    (J : ∀ a : Fin D, Finset (bucketFiber bucket (sel a)))
    (hcode : ∀ a ⦃i i'⦄, i ∈ J a → i' ∈ J a →
      roundedVertexCode sys a i = roundedVertexCode sys a i')
    (a b : Fin D) {i i' : bucketFiber bucket (sel a)}
    {j j' : bucketFiber bucket (sel b)}
    (hi : i ∈ J a) (hi' : i' ∈ J a) (hj : j ∈ J b) (hj' : j' ∈ J b) :
    sys.Q a b i j = sys.Q a b i' j' := by
  apply roundedBlock_eq_of_codes sys a b
  · exact congrArg (fun c ↦ (c b).1) (hcode a hi hi')
  · exact congrArg (fun c ↦ (c a).2) (hcode b hj hj')

/-- The exact asymptotic assertion of KSSS Lemma 10.1.  The integer `N`
spells out the meaning of the paper's `\gtrsim_{C,r,δ}` notation. -/
def KSSSLemma101 : Prop :=
  ∀ (C δ : ℝ) (r : ℕ), 0 < C → 0 < δ → δ < 1 →
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ (m : ℕ) (bucket : Fin n → Fin m) (G : SimpleGraph (Fin n))
        (B : Matrix (Fin n) (Fin n) ℝ),
        0 < m →
        Real.rpow (n : ℝ) δ / 2 ≤ (m : ℝ) →
        (m : ℝ) ≤ 2 * Real.rpow (n : ℝ) δ →
        HasEqualBuckets bucket → RamseyFree C G →
        BlockRankAtMost r bucket B →
          c * (n : ℝ) ^ 2 ≤ frobeniusSq (graphAdjacencyMatrix G - B)

/-- Arithmetic endpoint of the density contradiction in Lemma 10.1.
After blockwise rounding and the homogeneous bucket selection, `E` is the
edge count either in the selected induced graph or in its complement. -/
lemma robust_rank_density_contradiction_endpoint
    {a errorDensity : ℝ} {q E : ℕ} (hq : 0 < q)
    (hgap : errorDensity < a)
    (hlower : a * (q : ℝ) ^ 2 ≤ E)
    (hupper : (E : ℝ) ≤ errorDensity * (q : ℝ) ^ 2) : False := by
  have hqreal : (0 : ℝ) < q := by exact_mod_cast hq
  nlinarith [sq_pos_of_pos hqreal]

/-- For a binary rounded matrix, the Frobenius error in Proposition 10.2
is literally its number of edited cells. -/
lemma frobeniusSq_graphAdjacency_sub_eq_editDistance
    {n : ℕ} (G : SimpleGraph (Fin n)) {Q : Matrix (Fin n) (Fin n) ℝ}
    (hQ : IsBinary Q) :
    frobeniusSq (graphAdjacencyMatrix G - Q) =
      editDistance (graphAdjacencyMatrix G) Q :=
  frobeniusSq_sub_eq_editDistance (graphAdjacencyMatrix_isBinary G) hQ

end RobustRank
end Erdos88
