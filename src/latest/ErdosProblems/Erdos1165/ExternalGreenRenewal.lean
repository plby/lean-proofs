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

import ErdosProblems.Erdos1165.ExternalOnePoint
import ErdosProblems.Erdos1165.ExternalRenewal
import ErdosProblems.Erdos1165.StirlingLocalCLT
import Mathlib.Data.Finset.Sort

/-!
# The external walk: binomial transform and the Green-function reduction

An ordinary two-step block is either the single block removed by the lazy
decomposition, or one of the fifteen retained blocks.  Since the removed
block has zero displacement, returning ordinary block words decompose by
their set of retained coordinates.  This gives the exact positive binomial
transform

`centralBinom n ^ 2 = ∑ j ≤ n, choose n j * #externalReturningWords j`.

This identity is the combinatorial core of a route to the sharp external
Green-function constant which avoids redoing a two-saddle Fourier inversion:
the known ordinary planar return asymptotic can be transferred through the
binomial transform.  The results below prove the finite, exact part of that
reduction from the definitions of the two walks.
-/

open Set
open scoped BigOperators

namespace Erdos1165.ExternalGreenRenewal

open ExternalWalk ExternalOnePoint LazyDecomposition

/-! ## A two-step block is a deleted block or a retained block -/

/-- The sixteen ordinary two-step blocks are the disjoint union of the
unique deleted block and the fifteen retained blocks. -/
def blockOptionEquiv (o : Orientation) : Block ≃ Option (RetainedBlock o) where
  toFun b := if h : b = removableBlock o then none else some ⟨b, h⟩
  invFun
    | none => removableBlock o
    | some b => b
  left_inv b := by
    by_cases h : b = removableBlock o
    · simp [h]
    · simp [h]
  right_inv q := by
    cases q with
    | none => simp
    | some b => simp [b.property]

@[simp] theorem blockOptionEquiv_removable (o : Orientation) :
    blockOptionEquiv o (removableBlock o) = none := by
  simp [blockOptionEquiv]

@[simp] theorem blockOptionEquiv_retained (o : Orientation) (b : RetainedBlock o) :
    blockOptionEquiv o (b : Block) = some b := by
  simp [blockOptionEquiv, b.property]

/-- Coordinates occupied by retained rather than deleted blocks. -/
def retainedIndices (o : Orientation) {n : ℕ} (u : Fin n → Block) : Finset (Fin n) :=
  Finset.univ.filter fun i ↦ u i ≠ removableBlock o

@[simp] lemma mem_retainedIndices (o : Orientation) {n : ℕ}
    (u : Fin n → Block) (i : Fin n) :
    i ∈ retainedIndices o u ↔ u i ≠ removableBlock o := by
  simp [retainedIndices]

/-- The word obtained by inserting deleted blocks away from `s`. -/
def inflateRetainedWord (o : Orientation) {n j : ℕ}
    (s : Finset (Fin n)) (hs : s.card = j)
    (v : Fin j → RetainedBlock o) : Fin n → Block :=
  fun i ↦ if hi : i ∈ s then
    (v ((s.orderIsoOfFin hs).symm ⟨i, hi⟩) : Block)
  else removableBlock o

@[simp] lemma inflateRetainedWord_on (o : Orientation) {n j : ℕ}
    (s : Finset (Fin n)) (hs : s.card = j)
    (v : Fin j → RetainedBlock o) (k : Fin j) :
    inflateRetainedWord o s hs v (s.orderIsoOfFin hs k) = v k := by
  simp only [inflateRetainedWord, (s.orderIsoOfFin hs k).property, dif_pos]
  have hsub :
      (⟨↑(s.orderIsoOfFin hs k), (s.orderIsoOfFin hs k).property⟩ : s) =
        s.orderIsoOfFin hs k := Subtype.ext rfl
  rw [hsub, (s.orderIsoOfFin hs).symm_apply_apply]

lemma inflateRetainedWord_off (o : Orientation) {n j : ℕ}
    (s : Finset (Fin n)) (hs : s.card = j)
    (v : Fin j → RetainedBlock o) {i : Fin n} (hi : i ∉ s) :
    inflateRetainedWord o s hs v i = removableBlock o := by
  simp [inflateRetainedWord, hi]

@[simp] theorem retainedIndices_inflateRetainedWord (o : Orientation) {n j : ℕ}
    (s : Finset (Fin n)) (hs : s.card = j)
    (v : Fin j → RetainedBlock o) :
    retainedIndices o (inflateRetainedWord o s hs v) = s := by
  ext i
  by_cases hi : i ∈ s
  · rw [mem_retainedIndices]
    simp [inflateRetainedWord, hi, (v _).property]
  · rw [mem_retainedIndices]
    simp [inflateRetainedWord, hi]

/-- Read the retained coordinates of a word in increasing order. -/
def extractRetainedWord (o : Orientation) {n j : ℕ}
    (u : Fin n → Block) (hu : (retainedIndices o u).card = j) :
    Fin j → RetainedBlock o :=
  fun k ↦ ⟨u ((retainedIndices o u).orderIsoOfFin hu k),
    (mem_retainedIndices o u _).mp ((retainedIndices o u).orderIsoOfFin hu k).property⟩

private lemma orderIsoOfFin_val_congr {n j : ℕ} (a b : Finset (Fin n))
    (h : a = b) (ha : a.card = j) (hb : b.card = j) (k : Fin j) :
    (↑(a.orderIsoOfFin ha k) : Fin n) = ↑(b.orderIsoOfFin hb k) := by
  subst b
  rfl

@[simp] theorem extractRetainedWord_inflateRetainedWord (o : Orientation) {n j : ℕ}
    (s : Finset (Fin n)) (hs : s.card = j)
    (v : Fin j → RetainedBlock o) :
    extractRetainedWord o (inflateRetainedWord o s hs v)
      (by rw [retainedIndices_inflateRetainedWord o s hs v]; exact hs) = v := by
  funext k
  apply Subtype.ext
  change inflateRetainedWord o s hs v
      (↑((retainedIndices o (inflateRetainedWord o s hs v)).orderIsoOfFin
        (by rw [retainedIndices_inflateRetainedWord o s hs v]; exact hs) k)) =
    (v k : Block)
  have hindex :
      (↑((retainedIndices o (inflateRetainedWord o s hs v)).orderIsoOfFin
        (by rw [retainedIndices_inflateRetainedWord o s hs v]; exact hs) k) : Fin n) =
        ↑(s.orderIsoOfFin hs k) := by
    exact orderIsoOfFin_val_congr _ _
      (retainedIndices_inflateRetainedWord o s hs v) _ _ k
  rw [hindex]
  exact inflateRetainedWord_on o s hs v k

lemma inflateRetainedWord_extractRetainedWord (o : Orientation) {n j : ℕ}
    (u : Fin n → Block) (hu : (retainedIndices o u).card = j) :
    inflateRetainedWord o (retainedIndices o u) hu
      (extractRetainedWord o u hu) = u := by
  funext i
  by_cases hi : i ∈ retainedIndices o u
  · simp only [inflateRetainedWord, hi, dif_pos]
    change u (↑((retainedIndices o u).orderIsoOfFin hu
      (((retainedIndices o u).orderIsoOfFin hu).symm ⟨i, hi⟩))) = u i
    simp
  · rw [inflateRetainedWord_off o _ hu _ hi]
    exact (not_ne_iff.mp ((mem_retainedIndices o u i).not.mp hi)).symm

/-! ## Displacement is unchanged by inserting deleted blocks -/

@[simp] lemma blockDisplacement_removable (o : Orientation) :
    ExternalWalk.blockDisplacement (removableBlock o) = 0 := by
  cases o <;> rfl

theorem sum_inflateRetainedWord_displacement (o : Orientation) {n j : ℕ}
    (s : Finset (Fin n)) (hs : s.card = j)
    (v : Fin j → RetainedBlock o) :
    (∑ i, ExternalWalk.blockDisplacement (inflateRetainedWord o s hs v i)) =
      externalWordDisplacement o v := by
  rw [externalWordDisplacement]
  calc
    (∑ i : Fin n, ExternalWalk.blockDisplacement (inflateRetainedWord o s hs v i)) =
        ∑ i ∈ s, ExternalWalk.blockDisplacement (inflateRetainedWord o s hs v i) := by
      symm
      apply Finset.sum_subset (Finset.subset_univ s)
      intro i hi his
      simp [inflateRetainedWord_off o s hs v his]
    _ = ∑ i : s, ExternalWalk.blockDisplacement
        (inflateRetainedWord o s hs v i) := by
      exact Finset.sum_subtype s (fun _ ↦ by simp)
        (fun i ↦ ExternalWalk.blockDisplacement (inflateRetainedWord o s hs v i))
    _ = ∑ k : Fin j, ExternalWalk.blockDisplacement
        (inflateRetainedWord o s hs v (s.orderIsoOfFin hs k)) := by
      symm
      exact Equiv.sum_comp (s.orderIsoOfFin hs).toEquiv
        (fun i : s ↦ ExternalWalk.blockDisplacement
          (inflateRetainedWord o s hs v i))
    _ = ∑ k : Fin j, retainedDisplacement o (v k) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [inflateRetainedWord_on]
      rfl

theorem sum_extractRetainedWord_displacement (o : Orientation) {n j : ℕ}
    (u : Fin n → Block) (hu : (retainedIndices o u).card = j) :
    externalWordDisplacement o (extractRetainedWord o u hu) =
      ∑ i, ExternalWalk.blockDisplacement (u i) := by
  rw [← sum_inflateRetainedWord_displacement o (retainedIndices o u) hu,
    inflateRetainedWord_extractRetainedWord]

/-! ## Returning words with a prescribed number of retained blocks -/

/-- Ordinary returning block words having exactly `j` retained coordinates. -/
def ReturningBlockWordsWithCount (o : Orientation) (n j : ℕ) :=
  {u : Fin n → Block //
    (∑ i, ExternalWalk.blockDisplacement (u i)) = 0 ∧
      (retainedIndices o u).card = j}

/-- A choice of `j` coordinates and a returning external word of length `j`. -/
def SupportAndExternalReturn (o : Orientation) (n j : ℕ) :=
  {s : Finset (Fin n) // s ∈ Finset.univ.powersetCard j} ×
    {v : Fin j → RetainedBlock o // externalWordDisplacement o v = 0}

noncomputable instance instFintypeReturningBlockWordsWithCount
    (o : Orientation) (n j : ℕ) : Fintype (ReturningBlockWordsWithCount o n j) := by
  unfold ReturningBlockWordsWithCount
  infer_instance

noncomputable instance instFintypeSupportAndExternalReturn
    (o : Orientation) (n j : ℕ) : Fintype (SupportAndExternalReturn o n j) := by
  unfold SupportAndExternalReturn
  infer_instance

/-- Exact equivalence behind the binomial transform. -/
noncomputable def returningBlockWordsWithCountEquiv (o : Orientation) (n j : ℕ) :
    ReturningBlockWordsWithCount o n j ≃ SupportAndExternalReturn o n j where
  toFun u :=
    (⟨retainedIndices o u.1, by
      rw [Finset.mem_powersetCard]
      exact ⟨Finset.subset_univ _, u.2.2⟩⟩,
      ⟨extractRetainedWord o u.1 u.2.2,
        (sum_extractRetainedWord_displacement o u.1 u.2.2).trans u.2.1⟩)
  invFun p :=
    let hs : p.1.1.card = j := (Finset.mem_powersetCard.mp p.1.2).2
    ⟨inflateRetainedWord o p.1.1 hs p.2.1,
      ⟨(sum_inflateRetainedWord_displacement o p.1.1 hs p.2.1).trans p.2.2,
        by rw [retainedIndices_inflateRetainedWord o p.1.1 hs p.2.1]; exact hs⟩⟩
  left_inv u := by
    apply Subtype.ext
    exact inflateRetainedWord_extractRetainedWord o u.1 u.2.2
  right_inv p := by
    rcases p with ⟨⟨s, hs⟩, ⟨v, hv⟩⟩
    apply Prod.ext
    · apply Subtype.ext
      exact retainedIndices_inflateRetainedWord o s
        (Finset.mem_powersetCard.mp hs).2 v
    · apply Subtype.ext
      simpa using extractRetainedWord_inflateRetainedWord o s
        (Finset.mem_powersetCard.mp hs).2 v

theorem card_returningBlockWordsWithCount (o : Orientation) (n j : ℕ) :
    Fintype.card (ReturningBlockWordsWithCount o n j) =
      n.choose j * (externalReturningWords o j).card := by
  classical
  rw [Fintype.card_congr (returningBlockWordsWithCountEquiv o n j)]
  let e : SupportAndExternalReturn o n j ≃
      ({s : Finset (Fin n) // s ∈ Finset.univ.powersetCard j} ×
        {v : Fin j → RetainedBlock o // externalWordDisplacement o v = 0}) :=
    Equiv.refl _
  rw [Fintype.card_congr e]
  rw [Fintype.card_prod]
  congr 1
  · rw [Fintype.card_subtype]
    simpa using Finset.card_powersetCard j (Finset.univ : Finset (Fin n))
  · rw [Fintype.card_subtype]
    rfl

/-! ## The exact finite binomial transform -/

/-- Returning ordinary words indexed by two-step blocks. -/
def returningBlockWords (n : ℕ) : Finset (Fin n → Block) :=
  Finset.univ.filter fun u ↦ ∑ i, ExternalWalk.blockDisplacement (u i) = 0

@[simp] lemma mem_returningBlockWords {n : ℕ} {u : Fin n → Block} :
    u ∈ returningBlockWords n ↔ ∑ i, ExternalWalk.blockDisplacement (u i) = 0 := by
  simp [returningBlockWords]

private def returningBlockWordEquivPaired (n : ℕ) :
    {u : Fin n → Block // ∑ i, ExternalWalk.blockDisplacement (u i) = 0} ≃
      {u : Fin (n * 2) → Direction // Erdos1165.blockDisplacement u = 0} :=
  Equiv.subtypeEquiv (blockWordEquivDirectionWord n) fun u ↦ by
    rw [blockWordEquivDirectionWord_displacement]

theorem card_returningBlockWords (n : ℕ) :
    (returningBlockWords n).card = Nat.centralBinom n ^ 2 := by
  calc
    (returningBlockWords n).card =
        Fintype.card {u : Fin n → Block //
          ∑ i, ExternalWalk.blockDisplacement (u i) = 0} := by
      rw [Fintype.card_subtype]
      rfl
    _ = Fintype.card {u : Fin (n * 2) → Direction //
          Erdos1165.blockDisplacement u = 0} :=
      Fintype.card_congr (returningBlockWordEquivPaired n)
    _ = (pairedReturningWords n).card := by
      rw [Fintype.card_subtype]
      rfl
    _ = Nat.centralBinom n ^ 2 := card_pairedReturningWords n

/-- Exact positive binomial transform relating ordinary and external return
counts.  No asymptotics or probability theory enter this identity. -/
theorem centralBinom_sq_eq_sum_choose_mul_externalReturns
    (o : Orientation) (n : ℕ) :
    Nat.centralBinom n ^ 2 =
      ∑ j ∈ Finset.range (n + 1),
        n.choose j * (externalReturningWords o j).card := by
  rw [← card_returningBlockWords n]
  calc
    (returningBlockWords n).card =
        ∑ j ∈ Finset.range (n + 1),
          ((returningBlockWords n).filter
            fun u ↦ (retainedIndices o u).card = j).card := by
      apply Finset.card_eq_sum_card_fiberwise
      intro u hu
      change (retainedIndices o u).card ∈ Finset.range (n + 1)
      rw [Finset.mem_range]
      exact Nat.lt_succ_of_le (by
        simpa using (Finset.card_le_univ (retainedIndices o u)))
    _ = ∑ j ∈ Finset.range (n + 1),
        n.choose j * (externalReturningWords o j).card := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [← card_returningBlockWordsWithCount o n j]
      change ((returningBlockWords n).filter
          fun u ↦ (retainedIndices o u).card = j).card =
        Fintype.card {u : Fin n → Block //
          (∑ i, ExternalWalk.blockDisplacement (u i)) = 0 ∧
            (retainedIndices o u).card = j}
      rw [Fintype.card_subtype]
      congr 1
      ext u
      simp [returningBlockWords]

/-! ## Probability form of the binomial transform -/

/-- The real-valued return probability of the external block chain. -/
noncomputable def externalReturnProbability (o : Orientation) (n : ℕ) : ℝ :=
  ((externalReturningWords o n).card : ℝ) / 15 ^ n

lemma externalReturnProbability_nonneg (o : Orientation) (n : ℕ) :
    0 ≤ externalReturnProbability o n := by
  unfold externalReturnProbability
  positivity

lemma externalReturnProbability_le_one (o : Orientation) (n : ℕ) :
    externalReturnProbability o n ≤ 1 := by
  unfold externalReturnProbability
  rw [div_le_one (by positivity : (0 : ℝ) < 15 ^ n)]
  exact_mod_cast (show (externalReturningWords o n).card ≤ 15 ^ n by
    simpa [Fintype.card_fun, card_retainedBlock] using
      (Finset.card_le_univ (externalReturningWords o n)))

private lemma thinning_weight_cancel {n j : ℕ} (hj : j ≤ n) :
    ((15 : ℝ) / 16) ^ j * ((1 : ℝ) / 16) ^ (n - j) /
        15 ^ j = 1 / 16 ^ n := by
  rw [div_pow, one_div, one_div, inv_pow]
  field_simp
  rw [← pow_add, Nat.add_sub_of_le hj]

/-- Probability version of the exact binomial transform.  Equivalently, an
ordinary two-step return probability is the expectation of the external
return probability at an independent `Binomial(n, 15/16)` time. -/
theorem planarReturnProbability_eq_binomial_average
    (o : Orientation) (n : ℕ) :
    Erdos1165.planarReturnProbability n =
      ∑ j ∈ Finset.range (n + 1),
        (n.choose j : ℝ) * ((15 : ℝ) / 16) ^ j *
          ((1 : ℝ) / 16) ^ (n - j) * externalReturnProbability o j := by
  unfold Erdos1165.planarReturnProbability externalReturnProbability
  rw [← Nat.cast_pow, centralBinom_sq_eq_sum_choose_mul_externalReturns o n,
    Nat.cast_sum]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mem_range] at hj
  have hjn : j ≤ n := Nat.le_of_lt_succ (by simpa only [Nat.lt_add_one_iff] using hj)
  push_cast
  rw [show ((n.choose j : ℝ) * (externalReturningWords o j).card) / 16 ^ n =
      (n.choose j : ℝ) * (externalReturningWords o j).card * (1 / 16 ^ n) by
        rw [div_eq_mul_inv, one_div]]
  rw [← thinning_weight_cancel hjn]
  ring

/-! ## Green power series -/

/-- Green power series of the ordinary even-time planar return sequence. -/
noncomputable def planarGreen (t : ℝ) : ℝ :=
  ∑' n : ℕ, Erdos1165.planarReturnProbability n * t ^ n

/-- Green power series of the external block-chain return sequence. -/
noncomputable def externalGreen (o : Orientation) (z : ℝ) : ℝ :=
  ∑' n : ℕ, externalReturnProbability o n * z ^ n

lemma planarReturnProbability_nonneg (n : ℕ) :
    0 ≤ Erdos1165.planarReturnProbability n :=
  (Erdos1165.planarReturnProbability_pos n).le

lemma planarReturnProbability_le_one (n : ℕ) :
    Erdos1165.planarReturnProbability n ≤ 1 := by
  unfold Erdos1165.planarReturnProbability
  have hc := StirlingLocalCLT.centralBinom_le_four_pow n
  rw [div_le_one (by positivity : (0 : ℝ) < 16 ^ n)]
  rw [show (16 : ℝ) ^ n = ((4 : ℝ) ^ n) ^ 2 by
    calc
      (16 : ℝ) ^ n = (4 ^ 2 : ℝ) ^ n := by norm_num
      _ = (4 : ℝ) ^ (2 * n) := (pow_mul 4 2 n).symm
      _ = (4 : ℝ) ^ (n * 2) := by rw [Nat.mul_comm]
      _ = ((4 : ℝ) ^ n) ^ 2 := pow_mul 4 n 2]
  nlinarith

theorem summable_planarReturnProbability_mul_pow {t : ℝ} (ht : |t| < 1) :
    Summable fun n : ℕ ↦ Erdos1165.planarReturnProbability n * t ^ n := by
  refine .of_norm_bounded (summable_geometric_of_lt_one (abs_nonneg t) ht) fun n ↦ ?_
  rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg (planarReturnProbability_nonneg n)]
  simpa using mul_le_mul_of_nonneg_right (planarReturnProbability_le_one n)
    (pow_nonneg (abs_nonneg t) n)

theorem summable_externalReturnProbability_mul_pow (o : Orientation)
    {z : ℝ} (hz : |z| < 1) :
    Summable fun n : ℕ ↦ externalReturnProbability o n * z ^ n := by
  refine .of_norm_bounded (summable_geometric_of_lt_one (abs_nonneg z) hz) fun n ↦ ?_
  rw [Real.norm_eq_abs, abs_mul, abs_pow,
    abs_of_nonneg (externalReturnProbability_nonneg o n)]
  simpa using mul_le_mul_of_nonneg_right (externalReturnProbability_le_one o n)
    (pow_nonneg (abs_nonneg z) n)

/-- Reindex the triangular set `0 ≤ j ≤ n` by `(j,k)` with `n=j+k`. -/
def triangularEquiv : (Σ n : ℕ, Fin (n + 1)) ≃ ℕ × ℕ where
  toFun p := (p.2, p.1 - p.2)
  invFun p := ⟨p.1 + p.2, ⟨p.1, by omega⟩⟩
  left_inv p := by
    rcases p with ⟨n, j⟩
    let hfirst : (j : ℕ) + (n - j) = n :=
      Nat.add_sub_of_le (Nat.le_of_lt_succ j.isLt)
    have hdim : (j : ℕ) + (n - j) + 1 = n + 1 := congrArg (· + 1) hfirst
    exact Sigma.ext hfirst <|
      (Fin.heq_ext_iff hdim).mpr rfl
  right_inv p := by
    apply Prod.ext
    · rfl
    · simp

@[simp] lemma triangularEquiv_symm_apply (j k : ℕ) :
    triangularEquiv.symm (j, k) = ⟨j + k, ⟨j, by omega⟩⟩ := rfl

/-- The nonnegative triangular summand in the binomial average, including
the power-series variable. -/
noncomputable def triangularReturnTerm (o : Orientation) (t : ℝ)
    (p : Σ n : ℕ, Fin (n + 1)) : ℝ :=
  (p.1.choose p.2 : ℝ) * ((15 : ℝ) / 16) ^ (p.2 : ℕ) *
    ((1 : ℝ) / 16) ^ (p.1 - p.2) *
      externalReturnProbability o p.2 * t ^ p.1

lemma triangularReturnTerm_nonneg (o : Orientation) {t : ℝ} (ht : 0 ≤ t)
    (p : Σ n : ℕ, Fin (n + 1)) : 0 ≤ triangularReturnTerm o t p := by
  unfold triangularReturnTerm
  have hq := externalReturnProbability_nonneg o p.2
  positivity

lemma sum_triangularReturnTerm_fiber (o : Orientation) (t : ℝ) (n : ℕ) :
    (∑ j : Fin (n + 1), triangularReturnTerm o t ⟨n, j⟩) =
      Erdos1165.planarReturnProbability n * t ^ n := by
  unfold triangularReturnTerm
  change (∑ j : Fin (n + 1),
      (n.choose (j : ℕ) : ℝ) * ((15 : ℝ) / 16) ^ (j : ℕ) *
        ((1 : ℝ) / 16) ^ (n - (j : ℕ)) *
          externalReturnProbability o (j : ℕ) * t ^ n) = _
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ ↦
    (n.choose j : ℝ) * ((15 : ℝ) / 16) ^ j *
      ((1 : ℝ) / 16) ^ (n - j) * externalReturnProbability o j * t ^ n) (n + 1)]
  rw [← Finset.sum_mul]
  rw [planarReturnProbability_eq_binomial_average o n]

theorem summable_triangularReturnTerm (o : Orientation) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t < 1) : Summable (triangularReturnTerm o t) := by
  rw [summable_sigma_of_nonneg (triangularReturnTerm_nonneg o ht0)]
  constructor
  · intro n
    exact (hasSum_fintype (fun j : Fin (n + 1) ↦
      triangularReturnTerm o t ⟨n, j⟩)).summable
  · simpa [tsum_fintype, sum_triangularReturnTerm_fiber] using
      summable_planarReturnProbability_mul_pow (by simpa [abs_of_nonneg ht0] using ht1)

lemma triangularReturnTerm_reindex (o : Orientation) (t : ℝ) (j k : ℕ) :
    triangularReturnTerm o t (triangularEquiv.symm (j, k)) =
      (externalReturnProbability o j * ((15 : ℝ) * t / 16) ^ j) *
        ((j + k).choose j * (t / 16) ^ k) := by
  rw [triangularEquiv_symm_apply]
  simp only [triangularReturnTerm, Nat.add_sub_cancel_left]
  rw [pow_add]
  ring

private lemma abs_div_sixteen_lt_one {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    |t / 16| < 1 := by
  rw [abs_of_nonneg (div_nonneg ht0 (by norm_num))]
  linarith

private lemma transformed_argument_nonneg {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    0 ≤ ((15 : ℝ) * t / 16) / (1 - t / 16) := by
  apply div_nonneg
  · positivity
  · linarith

private lemma transformed_argument_lt_one {t : ℝ} (_ht0 : 0 ≤ t) (ht1 : t < 1) :
    ((15 : ℝ) * t / 16) / (1 - t / 16) < 1 := by
  rw [div_lt_one (by linarith : (0 : ℝ) < 1 - t / 16)]
  linarith

private lemma green_transform_algebra (q a d : ℝ) (j : ℕ) :
    q * a ^ j * (1 / d ^ (j + 1)) =
      (1 / d) * q * (a / d) ^ j := by
  rw [pow_succ, div_pow]
  simp only [one_div, mul_inv_rev]
  ring

lemma tsum_triangularReturnTerm_reindex_second (o : Orientation) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t < 1) (j : ℕ) :
    (∑' k : ℕ, triangularReturnTerm o t (triangularEquiv.symm (j, k))) =
      (1 / (1 - t / 16)) * externalReturnProbability o j *
        ((((15 : ℝ) * t / 16) / (1 - t / 16)) ^ j) := by
  rw [tsum_congr (fun k ↦ triangularReturnTerm_reindex o t j k)]
  rw [tsum_mul_left]
  have hnegativeBinomial := tsum_choose_mul_geometric_of_norm_lt_one
    (𝕜 := ℝ) j (abs_div_sixteen_lt_one ht0 ht1)
  rw [show (∑' x : ℕ, ((j + x).choose j : ℝ) * (t / 16) ^ x) =
      1 / (1 - t / 16) ^ (j + 1) by
    simpa [Nat.add_comm] using hnegativeBinomial]
  exact green_transform_algebra (externalReturnProbability o j)
    ((15 : ℝ) * t / 16) (1 - t / 16) j

/-- Exact Green-function transform induced by deleting one of the sixteen
ordinary two-step blocks.  This is the analytic bridge from the ordinary
planar Green function to the external Green function. -/
theorem planarGreen_eq_externalGreen_transform (o : Orientation) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t < 1) :
    planarGreen t =
      (1 / (1 - t / 16)) *
        externalGreen o (((15 : ℝ) * t / 16) / (1 - t / 16)) := by
  have hsigma := summable_triangularReturnTerm o ht0 ht1
  have hprod : Summable (fun p : ℕ × ℕ ↦
      triangularReturnTerm o t (triangularEquiv.symm p)) :=
    (triangularEquiv.symm.summable_iff).2 hsigma
  unfold planarGreen
  calc
    (∑' n : ℕ, Erdos1165.planarReturnProbability n * t ^ n) =
        ∑' n : ℕ, ∑' j : Fin (n + 1), triangularReturnTerm o t ⟨n, j⟩ := by
      apply tsum_congr
      intro n
      rw [tsum_fintype, sum_triangularReturnTerm_fiber]
    _ = ∑' p : (Σ n : ℕ, Fin (n + 1)), triangularReturnTerm o t p :=
      hsigma.tsum_sigma.symm
    _ = ∑' p : ℕ × ℕ, triangularReturnTerm o t (triangularEquiv.symm p) := by
      symm
      exact triangularEquiv.symm.tsum_eq (triangularReturnTerm o t)
    _ = ∑' j : ℕ, ∑' k : ℕ,
        triangularReturnTerm o t (triangularEquiv.symm (j, k)) :=
      hprod.tsum_prod
    _ = ∑' j : ℕ, (1 / (1 - t / 16)) * externalReturnProbability o j *
        ((((15 : ℝ) * t / 16) / (1 - t / 16)) ^ j) := by
      apply tsum_congr
      intro j
      exact tsum_triangularReturnTerm_reindex_second o ht0 ht1 j
    _ = (1 / (1 - t / 16)) *
        externalGreen o (((15 : ℝ) * t / 16) / (1 - t / 16)) := by
      rw [externalGreen, ← tsum_mul_left]
      apply tsum_congr
      intro j
      ring

/-- Solved form of the Green transform.  The Möbius substitution
`t = 16z/(15+z)` maps `[0,1)` to itself. -/
theorem externalGreen_eq_planarGreen_transform (o : Orientation) {z : ℝ}
    (hz0 : 0 ≤ z) (hz1 : z < 1) :
    externalGreen o z =
      (15 / (15 + z)) * planarGreen (16 * z / (15 + z)) := by
  let t : ℝ := 16 * z / (15 + z)
  have hden : (15 + z : ℝ) ≠ 0 := by linarith
  have ht0 : 0 ≤ t := by
    dsimp [t]
    positivity
  have ht1 : t < 1 := by
    dsimp [t]
    rw [div_lt_one (by linarith : (0 : ℝ) < 15 + z)]
    linarith
  have hmain := planarGreen_eq_externalGreen_transform o ht0 ht1
  have harg : (((15 : ℝ) * t / 16) / (1 - t / 16)) = z := by
    dsimp [t]
    field_simp
    ring
  have hfactor : (1 / (1 - t / 16) : ℝ) = (15 + z) / 15 := by
    dsimp [t]
    field_simp
    ring
  rw [harg, hfactor] at hmain
  rw [hmain]
  field_simp

/-! ## Quantitative ordinary local limit and summable Green error -/

/-- Exact form of the ordinary planar return probability in terms of the
Robbins logarithmic error. -/
theorem planarReturnProbability_eq_exp_error {n : ℕ} (hn : n ≠ 0) :
    Erdos1165.planarReturnProbability n =
      Real.exp (2 * StirlingLocalCLT.centralBinomialLogError n) /
        (Real.pi * n) := by
  have hnorm := StirlingLocalCLT.centralBinom_normalized_eq_exp_error hn
  have hsq := congrArg (fun x : ℝ ↦ x ^ 2) hnorm
  have hsqrt : Real.sqrt (Real.pi * n) ^ 2 = Real.pi * n :=
    Real.sq_sqrt (by positivity)
  unfold Erdos1165.planarReturnProbability
  rw [show Real.exp (2 * StirlingLocalCLT.centralBinomialLogError n) =
      Real.exp (StirlingLocalCLT.centralBinomialLogError n) ^ 2 by
    rw [two_mul, Real.exp_add, pow_two]]
  apply (eq_div_iff (by positivity : (Real.pi * (n : ℝ)) ≠ 0)).2
  field_simp at hsq
  field_simp
  rw [hsqrt] at hsq
  have hpow : ((4 : ℝ) ^ n) ^ 2 = 16 ^ n := by
    calc
      ((4 : ℝ) ^ n) ^ 2 = (4 : ℝ) ^ (n * 2) := (pow_mul 4 n 2).symm
      _ = (4 : ℝ) ^ (2 * n) := by rw [Nat.mul_comm]
      _ = ((4 : ℝ) ^ 2) ^ n := pow_mul 4 2 n
      _ = (16 : ℝ) ^ n := by norm_num
  rw [hpow] at hsq
  nlinarith [hsq]

lemma abs_two_centralBinomialLogError_le {n : ℕ} (hn : n ≠ 0) :
    |2 * StirlingLocalCLT.centralBinomialLogError n| ≤
      4 * ((1 : ℝ) / (12 * n)) := by
  rw [abs_le]
  have h := StirlingLocalCLT.centralBinomialLogError_robbins_bounds hn
  constructor
  · linarith [h.1]
  · have hcompare : (1 : ℝ) / (12 * (2 * n)) ≤
        2 * ((1 : ℝ) / (12 * n)) := by
      have hnpos : (0 : ℝ) < n := by positivity
      field_simp
      nlinarith
    linarith [h.2, hcompare]

lemma abs_exp_two_centralBinomialLogError_sub_one_le {n : ℕ} (hn : n ≠ 0) :
    |Real.exp (2 * StirlingLocalCLT.centralBinomialLogError n) - 1| ≤
      8 * ((1 : ℝ) / (12 * n)) := by
  have he := abs_two_centralBinomialLogError_le hn
  have heone : |2 * StirlingLocalCLT.centralBinomialLogError n| ≤ 1 := by
    calc
      _ ≤ 4 * ((1 : ℝ) / (12 * n)) := he
      _ ≤ 1 := by
        have hnpos : (0 : ℝ) < n := by positivity
        have hnone : (1 : ℝ) ≤ n := by
          exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
        rw [show 4 * ((1 : ℝ) / (12 * n)) = 1 / (3 * n) by
          field_simp
          norm_num]
        rw [div_le_one (by positivity : (0 : ℝ) < 3 * n)]
        nlinarith
  calc
    _ ≤ 2 * |2 * StirlingLocalCLT.centralBinomialLogError n| :=
      Real.abs_exp_sub_one_le heone
    _ ≤ 8 * ((1 : ℝ) / (12 * n)) := by linarith

/-- A sharp explicit summable error in the ordinary planar local CLT.  The
constant is kept in terms of `π`; this is useful when estimating differences
of Green functions, where a coarse replacement of `π` loses too much. -/
theorem abs_planarReturnProbability_sub_main_le_sharp {n : ℕ} (hn : n ≠ 0) :
    |Erdos1165.planarReturnProbability n - 1 / (Real.pi * n)| ≤
      2 / (3 * Real.pi * (n : ℝ) ^ 2) := by
  rw [planarReturnProbability_eq_exp_error hn, ← sub_div, abs_div,
    abs_of_pos (by positivity : (0 : ℝ) < Real.pi * n)]
  calc
    |Real.exp (2 * StirlingLocalCLT.centralBinomialLogError n) - 1| /
          (Real.pi * ↑n) ≤
        (8 * ((1 : ℝ) / (12 * n))) / (Real.pi * n) := by
      gcongr
      exact abs_exp_two_centralBinomialLogError_sub_one_le hn
    _ = 2 / (3 * Real.pi * (n : ℝ) ^ 2) := by ring

/-- A denominator-free corollary of the sharp local-CLT error. -/
theorem abs_planarReturnProbability_sub_main_le {n : ℕ} (hn : n ≠ 0) :
    |Erdos1165.planarReturnProbability n - 1 / (Real.pi * n)| ≤
      1 / (n : ℝ) ^ 2 := by
  calc
    _ ≤ 2 / (3 * Real.pi * (n : ℝ) ^ 2) :=
      abs_planarReturnProbability_sub_main_le_sharp hn
    _ ≤ 1 / (n : ℝ) ^ 2 := by
      have hnpos : (0 : ℝ) < n := by positivity
      have hp := Real.two_le_pi
      field_simp
      nlinarith

/-- The shifted error sequence, avoiding the exceptional index zero. -/
noncomputable def planarGreenError (n : ℕ) : ℝ :=
  Erdos1165.planarReturnProbability (n + 1) -
    1 / (Real.pi * (n + 1))

theorem abs_planarGreenError_le (n : ℕ) :
    |planarGreenError n| ≤ 1 / ((n + 1 : ℕ) : ℝ) ^ 2 := by
  simpa [planarGreenError, Nat.succ_eq_add_one] using
    abs_planarReturnProbability_sub_main_le (Nat.succ_ne_zero n)

theorem abs_planarGreenError_le_sharp (n : ℕ) :
    |planarGreenError n| ≤
      2 / (3 * Real.pi * (((n + 1 : ℕ) : ℝ) ^ 2)) := by
  simpa [planarGreenError, Nat.succ_eq_add_one] using
    (abs_planarReturnProbability_sub_main_le_sharp
      (n := n + 1) (Nat.succ_ne_zero n))

theorem summable_abs_planarGreenError : Summable fun n : ℕ ↦ |planarGreenError n| := by
  have hp : Summable fun n : ℕ ↦ 1 / (n : ℝ) ^ 2 :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hpshift : Summable fun n : ℕ ↦ 1 / ((n + 1 : ℕ) : ℝ) ^ 2 := by
    change Summable fun n : ℕ ↦ (fun k : ℕ ↦ 1 / (k : ℝ) ^ 2) (n + 1)
    exact (summable_nat_add_iff 1).mpr hp
  exact hpshift.of_nonneg_of_le (fun n ↦ abs_nonneg _) abs_planarGreenError_le

/-- A finite absolute bound for the analytic remainder in the planar Green
function. -/
noncomputable def planarGreenErrorConstant : ℝ :=
  ∑' n : ℕ, |planarGreenError n|

lemma planarGreenErrorConstant_nonneg : 0 ≤ planarGreenErrorConstant := by
  exact tsum_nonneg fun _ ↦ abs_nonneg _

/-- The total analytic remainder is small enough for a strict dyadic Green
increment estimate.  The identity `∑ n⁻² = π² / 6` keeps the useful constant
instead of discarding it in a comparison test. -/
theorem planarGreenErrorConstant_le_pi_div_nine :
    planarGreenErrorConstant ≤ Real.pi / 9 := by
  have hs : Summable (fun n : ℕ ↦
      2 / (3 * Real.pi * (((n + 1 : ℕ) : ℝ) ^ 2))) := by
    have hs' : Summable (fun n : ℕ ↦ 1 / (((n + 1 : ℕ) : ℝ) ^ 2)) := by
      change Summable fun n : ℕ ↦ (fun k : ℕ ↦ 1 / (k : ℝ) ^ 2) (n + 1)
      exact (summable_nat_add_iff 1).mpr hasSum_zeta_two.summable
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      hs'.mul_left (2 / (3 * Real.pi))
  calc
    planarGreenErrorConstant ≤
        ∑' n : ℕ, 2 / (3 * Real.pi * (((n + 1 : ℕ) : ℝ) ^ 2)) := by
      exact summable_abs_planarGreenError.tsum_le_tsum
        abs_planarGreenError_le_sharp hs
    _ = (2 / (3 * Real.pi)) * (Real.pi ^ 2 / 6) := by
      have hshift : (∑' n : ℕ, 1 / (((n + 1 : ℕ) : ℝ) ^ 2)) =
          Real.pi ^ 2 / 6 := by
        have h := hasSum_zeta_two.summable.sum_add_tsum_nat_add 1
        rw [hasSum_zeta_two.tsum_eq] at h
        norm_num at h ⊢
        simpa [Nat.add_comm] using h
      rw [show (fun n : ℕ ↦ 2 / (3 * Real.pi * (((n + 1 : ℕ) : ℝ) ^ 2))) =
          fun n : ℕ ↦ (2 / (3 * Real.pi)) *
            (1 / (((n + 1 : ℕ) : ℝ) ^ 2)) by
        funext n
        ring, tsum_mul_left, hshift]
    _ = Real.pi / 9 := by
      field_simp
      ring

theorem summable_planarGreenError_mul_pow {t : ℝ} (ht : |t| ≤ 1) :
    Summable fun n : ℕ ↦ planarGreenError n * t ^ (n + 1) := by
  refine .of_norm_bounded summable_abs_planarGreenError fun n ↦ ?_
  rw [Real.norm_eq_abs, abs_mul, abs_pow]
  calc
    |planarGreenError n| * |t| ^ (n + 1) ≤ |planarGreenError n| * 1 := by
      gcongr
      exact pow_le_one₀ (abs_nonneg t) ht
    _ = |planarGreenError n| := mul_one _

theorem hasSum_planarHarmonic {t : ℝ} (ht : |t| < 1) :
    HasSum (fun n : ℕ ↦ 1 / (Real.pi * (n + 1)) * t ^ (n + 1))
      ((-Real.log (1 - t)) / Real.pi) := by
  have h := (Real.hasSum_pow_div_log_of_abs_lt_one ht).mul_left (1 / Real.pi)
  have hterms :
      (fun n : ℕ ↦ 1 / (Real.pi * (n + 1)) * t ^ (n + 1)) =
        fun n : ℕ ↦ (1 / Real.pi) * (t ^ (n + 1) / (n + 1)) := by
    funext n
    field_simp
  have hvalue : (-Real.log (1 - t)) / Real.pi =
      (1 / Real.pi) * (-Real.log (1 - t)) := by
    rw [div_eq_mul_inv]
    ring
  rw [hterms, hvalue]
  exact h

/-- Exact logarithmic singularity plus an absolutely summable remainder for
the ordinary planar Green function. -/
theorem planarGreen_eq_log_add_error {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    planarGreen t = 1 + (-Real.log (1 - t)) / Real.pi +
      ∑' n : ℕ, planarGreenError n * t ^ (n + 1) := by
  have htAbs : |t| < 1 := by simpa [abs_of_nonneg ht0] using ht1
  have hplanar := summable_planarReturnProbability_mul_pow htAbs
  have hharm := hasSum_planarHarmonic htAbs
  have herr := summable_planarGreenError_mul_pow (by
    rw [abs_of_nonneg ht0]
    exact ht1.le)
  have hsplit := hplanar.sum_add_tsum_nat_add 1
  unfold planarGreen
  calc
    (∑' n : ℕ, Erdos1165.planarReturnProbability n * t ^ n) =
        1 + ∑' n : ℕ,
          Erdos1165.planarReturnProbability (n + 1) * t ^ (n + 1) := by
      rw [← hsplit]
      norm_num [Erdos1165.planarReturnProbability, Nat.centralBinom]
    _ = 1 + ((∑' n : ℕ, 1 / (Real.pi * (n + 1)) * t ^ (n + 1)) +
        ∑' n : ℕ, planarGreenError n * t ^ (n + 1)) := by
      congr 1
      rw [← hharm.summable.tsum_add herr]
      apply tsum_congr
      intro n
      unfold planarGreenError
      ring
    _ = 1 + (-Real.log (1 - t)) / Real.pi +
        ∑' n : ℕ, planarGreenError n * t ^ (n + 1) := by
      rw [hharm.tsum_eq]
      ring

theorem tsum_planarGreenError_mul_pow_le_constant {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (∑' n : ℕ, planarGreenError n * t ^ (n + 1)) ≤
      planarGreenErrorConstant := by
  apply Summable.tsum_le_tsum
  · intro n
    calc
      planarGreenError n * t ^ (n + 1) ≤
          |planarGreenError n| * t ^ (n + 1) := by
        exact mul_le_mul_of_nonneg_right (le_abs_self _) (pow_nonneg ht0 _)
      _ ≤ |planarGreenError n| * 1 := by
        gcongr
        exact pow_le_one₀ ht0 ht1
      _ = |planarGreenError n| := mul_one _
  · exact summable_planarGreenError_mul_pow (by
      rw [abs_of_nonneg ht0]
      exact ht1)
  · exact summable_abs_planarGreenError

/-- Explicit global upper bound with the sharp logarithmic coefficient. -/
theorem planarGreen_le_log_add_constant {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    planarGreen t ≤
      1 + (-Real.log (1 - t)) / Real.pi + planarGreenErrorConstant := by
  rw [planarGreen_eq_log_add_error ht0 ht1]
  gcongr
  exact tsum_planarGreenError_mul_pow_le_constant ht0 ht1.le

theorem planarGreen_le_log_add_pi_div_nine {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t < 1) :
    planarGreen t ≤
      1 + (-Real.log (1 - t)) / Real.pi + Real.pi / 9 := by
  apply (planarGreen_le_log_add_constant ht0 ht1).trans
  gcongr
  exact planarGreenErrorConstant_le_pi_div_nine

/-- Exact external Green singular expansion.  The remainder is uniformly
absolutely bounded by `planarGreenErrorConstant`; the prefactor tends to
`15/16` and the logarithm has argument
`1 - 16z/(15+z) = 15(1-z)/(15+z)`. -/
theorem externalGreen_eq_log_add_error (o : Orientation) {z : ℝ}
    (hz0 : 0 ≤ z) (hz1 : z < 1) :
    externalGreen o z = (15 / (15 + z)) *
      (1 + (-Real.log (1 - 16 * z / (15 + z))) / Real.pi +
        ∑' n : ℕ, planarGreenError n *
          (16 * z / (15 + z)) ^ (n + 1)) := by
  rw [externalGreen_eq_planarGreen_transform o hz0 hz1]
  apply congrArg ((15 / (15 + z)) * ·)
  apply planarGreen_eq_log_add_error
  · positivity
  · rw [div_lt_one (by linarith : (0 : ℝ) < 15 + z)]
    linarith

/-- External Green upper bound carrying the sharp `15/(16π)` leading
coefficient at the singular endpoint. -/
theorem externalGreen_le_log_add_constant (o : Orientation) {z : ℝ}
    (hz0 : 0 ≤ z) (hz1 : z < 1) :
    externalGreen o z ≤ (15 / (15 + z)) *
      (1 + (-Real.log (1 - 16 * z / (15 + z))) / Real.pi +
        planarGreenErrorConstant) := by
  rw [externalGreen_eq_planarGreen_transform o hz0 hz1]
  have ht0 : (0 : ℝ) ≤ 16 * z / (15 + z) := by positivity
  have ht1 : (16 * z / (15 + z) : ℝ) < 1 := by
    rw [div_lt_one (by linarith : (0 : ℝ) < 15 + z)]
    linarith
  exact mul_le_mul_of_nonneg_left (planarGreen_le_log_add_constant ht0 ht1)
    (by positivity)

/-- Numerical version of the external Green upper bound, with no auxiliary
series constant left in the statement. -/
theorem externalGreen_le_log_add_pi_div_nine (o : Orientation) {z : ℝ}
    (hz0 : 0 ≤ z) (hz1 : z < 1) :
    externalGreen o z ≤ (15 / (15 + z)) *
      (1 + (-Real.log (1 - 16 * z / (15 + z))) / Real.pi +
        Real.pi / 9) := by
  rw [externalGreen_eq_planarGreen_transform o hz0 hz1]
  have ht0 : (0 : ℝ) ≤ 16 * z / (15 + z) := by positivity
  have ht1 : (16 * z / (15 + z) : ℝ) < 1 := by
    rw [div_lt_one (by linarith : (0 : ℝ) < 15 + z)]
    linarith
  exact mul_le_mul_of_nonneg_left (planarGreen_le_log_add_pi_div_nine ht0 ht1)
    (by positivity)

/-! ## Truncated Green consequences -/

/-- Truncated real Green function written directly from the checked external
return counts. -/
noncomputable def externalTruncatedGreenCount (o : Orientation) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (N + 1), externalReturnProbability o n

lemma externalTruncatedGreenCount_nonneg (o : Orientation) (N : ℕ) :
    0 ≤ externalTruncatedGreenCount o N := by
  exact Finset.sum_nonneg fun n hn ↦ externalReturnProbability_nonneg o n

lemma externalTruncatedGreenCount_add_sub (o : Orientation) (m n : ℕ) :
    externalTruncatedGreenCount o (n + m) - externalTruncatedGreenCount o m =
      ∑ j ∈ Finset.range n, externalReturnProbability o (m + 1 + j) := by
  rw [externalTruncatedGreenCount, externalTruncatedGreenCount]
  have hadd : n + m + 1 = (m + 1) + n := by omega
  rw [hadd, Finset.sum_range_add]
  ring

/-- A reciprocal pointwise return bound controls every distant Green
increment.  This coarse estimate is complementary to the sharp Tauberian
upper bound: only the latter needs the exact logarithmic coefficient. -/
theorem externalTruncatedGreenCount_increment_le_of_reciprocal
    (o : Orientation) (B : ℝ) (hB : 0 ≤ B)
    (hpoint : ∀ k : ℕ, 0 < k →
      externalReturnProbability o k ≤ B / (k : ℝ))
    (m n : ℕ) :
    externalTruncatedGreenCount o (n + m) -
        externalTruncatedGreenCount o m ≤
      B * (n : ℝ) / (m + 1 : ℝ) := by
  rw [externalTruncatedGreenCount_add_sub]
  calc
    (∑ j ∈ Finset.range n, externalReturnProbability o (m + 1 + j)) ≤
        ∑ _j ∈ Finset.range n, B / (m + 1 : ℝ) := by
      apply Finset.sum_le_sum
      intro j hj
      calc
        externalReturnProbability o (m + 1 + j) ≤
            B / ((m + 1 + j : ℕ) : ℝ) := hpoint _ (by omega)
        _ ≤ B / (m + 1 : ℝ) := by
          apply div_le_div_of_nonneg_left hB (by positivity)
          norm_cast
          omega
    _ = B * (n : ℝ) / (m + 1 : ℝ) := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      ring

lemma externalReturnProbability_eq_renewal (o : Orientation) (n : ℕ) :
    externalReturnProbability o n =
      Erdos1165.ExternalRenewal.externalReturnProbability o n := by
  rw [Erdos1165.ExternalRenewal.externalReturnProbability,
    Erdos1165.ExternalRenewal.externalReturnAt,
    ExternalOnePoint.externalBlocks_return_probability]
  unfold externalReturnProbability
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_pow]
  rw [div_eq_mul_inv]
  have hreal : ENNReal.toReal ((1 : ENNReal) / 15) = (1 : ℝ) / 15 := by
    norm_num
  rw [hreal, ← inv_pow]
  rw [one_div]

/-- Identification with the renewal module's genuine finite-horizon Green
function. -/
theorem externalTruncatedGreenCount_eq_renewal (o : Orientation) (N : ℕ) :
    externalTruncatedGreenCount o N =
      Erdos1165.ExternalRenewal.externalTruncatedGreenReal o N := by
  rw [externalTruncatedGreenCount,
    Erdos1165.ExternalRenewal.externalTruncatedGreenReal,
    RenewalTail.truncatedGreen]
  apply Finset.sum_congr rfl
  intro n hn
  exact externalReturnProbability_eq_renewal o n

/-- Abelian domination of a truncated Green sum by the Green power series.
The factor is left on the left-hand side so that no division side conditions
are hidden. -/
theorem pow_mul_externalTruncatedGreenCount_le_externalGreen
    (o : Orientation) (N : ℕ) {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z < 1) :
    z ^ N * externalTruncatedGreenCount o N ≤ externalGreen o z := by
  have hsumm := summable_externalReturnProbability_mul_pow o (by
    rw [abs_of_nonneg hz0]
    exact hz1)
  unfold externalTruncatedGreenCount externalGreen
  calc
    z ^ N * (∑ n ∈ Finset.range (N + 1), externalReturnProbability o n) =
        ∑ n ∈ Finset.range (N + 1),
          z ^ N * externalReturnProbability o n := by
      rw [Finset.mul_sum]
    _ ≤ ∑ n ∈ Finset.range (N + 1),
        externalReturnProbability o n * z ^ n := by
      apply Finset.sum_le_sum
      intro n hn
      rw [Finset.mem_range] at hn
      have hnN : n ≤ N := Nat.le_of_lt_succ (by simpa using hn)
      rw [mul_comm (z ^ N)]
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_of_le_one hz0 hz1.le hnN)
        (externalReturnProbability_nonneg o n)
    _ ≤ ∑' n : ℕ, externalReturnProbability o n * z ^ n := by
      exact hsumm.sum_le_tsum (Finset.range (N + 1)) fun n hn ↦
        mul_nonneg (externalReturnProbability_nonneg o n) (pow_nonneg hz0 n)

/-- Fully explicit sharp-coefficient truncated-Green bound at an arbitrary
Abelian parameter `z`.  Choosing `z` close to one trades the harmless factor
`z^N` against the logarithmic expression on the right. -/
theorem pow_mul_externalTruncatedGreenCount_le_log_bound
    (o : Orientation) (N : ℕ) {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z < 1) :
    z ^ N * externalTruncatedGreenCount o N ≤
      (15 / (15 + z)) *
        (1 + (-Real.log (1 - 16 * z / (15 + z))) / Real.pi +
          planarGreenErrorConstant) := by
  exact (pow_mul_externalTruncatedGreenCount_le_externalGreen o N hz0 hz1).trans
    (externalGreen_le_log_add_constant o hz0 hz1)

/-- Numerical Abelian bound obtained from the explicit `π / 9` remainder. -/
theorem pow_mul_externalTruncatedGreenCount_le_explicit_log_bound
    (o : Orientation) (N : ℕ) {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z < 1) :
    z ^ N * externalTruncatedGreenCount o N ≤
      (15 / (15 + z)) *
        (1 + (-Real.log (1 - 16 * z / (15 + z))) / Real.pi +
          Real.pi / 9) := by
  exact (pow_mul_externalTruncatedGreenCount_le_externalGreen o N hz0 hz1).trans
    (externalGreen_le_log_add_pi_div_nine o hz0 hz1)

/-- A finite Tauberian form of the explicit Abelian estimate.  The parameter
`D` is free: taking `D` much larger than `N` makes the factor on the left
arbitrarily close to one, while the logarithm on the right grows only like
`log D`.  Bernoulli's inequality is the only loss in passing from the power
series to the partial Green sum. -/
theorem one_sub_nat_div_mul_externalTruncatedGreenCount_le_explicit
    (o : Orientation) (N : ℕ) (D : ℝ) (hD : 1 ≤ D) :
    (1 - (N : ℝ) / D) * externalTruncatedGreenCount o N ≤
      (15 / (15 + (1 - 1 / D))) *
        (1 + (-Real.log
          (1 - 16 * (1 - 1 / D) / (15 + (1 - 1 / D)))) / Real.pi +
          Real.pi / 9) := by
  let z : ℝ := 1 - 1 / D
  have hDpos : 0 < D := zero_lt_one.trans_le hD
  have hz0 : 0 ≤ z := by
    dsimp [z]
    rw [sub_nonneg, div_le_one hDpos]
    exact hD
  have hz1 : z < 1 := by
    dsimp [z]
    have : 0 < 1 / D := one_div_pos.mpr hDpos
    linarith
  have hzneg : (-1 : ℝ) ≤ z := by linarith
  have hpow : 1 - (N : ℝ) / D ≤ z ^ N := by
    have h := one_add_mul_sub_le_pow hzneg N
    calc
      1 - (N : ℝ) / D = 1 + (N : ℝ) * (z - 1) := by
        dsimp [z]
        ring
      _ ≤ z ^ N := h
  calc
    (1 - (N : ℝ) / D) * externalTruncatedGreenCount o N ≤
        z ^ N * externalTruncatedGreenCount o N :=
      mul_le_mul_of_nonneg_right hpow (externalTruncatedGreenCount_nonneg o N)
    _ ≤ (15 / (15 + z)) *
        (1 + (-Real.log (1 - 16 * z / (15 + z))) / Real.pi +
          Real.pi / 9) :=
      pow_mul_externalTruncatedGreenCount_le_explicit_log_bound o N hz0 hz1
    _ = _ := by rfl

/-- Algebraically simplified form of the finite Tauberian bound.  Its leading
term is visibly `(15 / (16 * π)) * log D`; all other factors tend to constants
when `N / D` tends to zero. -/
theorem one_sub_nat_div_mul_externalTruncatedGreenCount_le_log_D
    (o : Orientation) (N : ℕ) (D : ℝ) (hD : 1 ≤ D) :
    (1 - (N : ℝ) / D) * externalTruncatedGreenCount o N ≤
      (15 * D / (16 * D - 1)) *
        (1 + Real.log ((16 * D - 1) / 15) / Real.pi + Real.pi / 9) := by
  have hD0 : D ≠ 0 := ne_of_gt (zero_lt_one.trans_le hD)
  have hden : 16 * D - 1 ≠ 0 := by nlinarith
  have hbase : 15 + (1 - 1 / D) = (16 * D - 1) / D := by
    field_simp [hD0]
    ring
  have hfactor : 15 / (15 + (1 - 1 / D)) = 15 * D / (16 * D - 1) := by
    rw [hbase]
    field_simp [hD0, hden]
  have harg : 1 - 16 * (1 - 1 / D) / (15 + (1 - 1 / D)) =
      15 / (16 * D - 1) := by
    rw [hbase]
    field_simp [hD0, hden]
    ring
  have hinv : 15 / (16 * D - 1) = (((16 * D - 1) / 15)⁻¹ : ℝ) := by
    field_simp [hden]
  have hlog : -Real.log (15 / (16 * D - 1)) =
      Real.log ((16 * D - 1) / 15) := by
    rw [hinv, Real.log_inv]
    ring
  simpa only [hfactor, harg, hlog] using
    one_sub_nat_div_mul_externalTruncatedGreenCount_le_explicit o N D hD

end Erdos1165.ExternalGreenRenewal
