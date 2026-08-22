/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import ErdosProblems.Erdos1165.ExternalOnePoint
import ErdosProblems.Erdos1165.RenewalTail

/-!
# Renewal estimates for the retained-block external walk

This file proves the exact first-return renewal equation for the IID external
walk.  It also isolates the purely renewal-theoretic reduction of high local
time to a truncated Green-function estimate.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace Erdos1165.ExternalRenewal

open ExternalWalk ExternalOnePoint LazyDecomposition

variable (o : Orientation)

/-! ## Deterministic blocks and their independence -/

/-- Drop the first `n` retained blocks. -/
def externalShift (n : ℕ) (η : ℕ → RetainedBlock o) : ℕ → RetainedBlock o :=
  fun j ↦ η (n + j)

/-- The `m` retained blocks beginning at index `n`. -/
def externalBlock (n m : ℕ) (η : ℕ → RetainedBlock o) : Fin m → RetainedBlock o :=
  fun j ↦ η (n + j)

lemma measurable_externalShift (n : ℕ) : Measurable (externalShift o n) := by
  exact measurable_pi_lambda _ fun _ ↦ measurable_pi_apply _

lemma measurable_externalBlock (n m : ℕ) : Measurable (externalBlock o n m) := by
  exact measurable_pi_lambda _ fun j ↦ measurable_pi_apply (n + j)

theorem externalBlocks_map_externalShift (n : ℕ) :
    (externalBlocks o).map (externalShift o n) = externalBlocks o := by
  unfold externalBlocks externalShift
  exact Measure.map_infinitePi_infinitePi_of_inj
    (P := fun _ : ℕ ↦ retainedBlockLaw o) (f := fun j : ℕ ↦ n + j)
      fun _ _ ↦ Nat.add_left_cancel

theorem externalBlocks_map_externalBlock (n m : ℕ) :
    (externalBlocks o).map (externalBlock o n m) = externalBlockLaw o m := by
  unfold externalBlocks externalBlockLaw externalBlock
  exact Measure.map_infinitePi_infinitePi_of_inj
    (P := fun _ : ℕ ↦ retainedBlockLaw o) (f := fun j : Fin m ↦ n + j)
      fun i j h ↦ Fin.ext (Nat.add_left_cancel h)

private def externalPrefixIndexSet (n : ℕ) : Finset ℕ := Finset.range n

private def externalBlockIndexSet (n m : ℕ) : Finset ℕ :=
  (Finset.range m).image fun j ↦ n + j

private lemma externalPrefixIndexSet_disjoint_externalBlockIndexSet (n m : ℕ) :
    Disjoint (externalPrefixIndexSet n) (externalBlockIndexSet n m) := by
  rw [Finset.disjoint_left]
  intro i hi h'i
  rw [externalPrefixIndexSet, Finset.mem_range] at hi
  rw [externalBlockIndexSet, Finset.mem_image] at h'i
  obtain ⟨j, hj, rfl⟩ := h'i
  omega

theorem indepFun_externalPrefix_externalBlock (n m : ℕ) :
    IndepFun (externalPrefix o n) (externalBlock o n m) (externalBlocks o) := by
  let S := externalPrefixIndexSet n
  let T := externalBlockIndexSet n m
  have h := (externalBlocks_independent o).indepFun_finset S T
    (externalPrefixIndexSet_disjoint_externalBlockIndexSet n m)
    (fun _ ↦ measurable_pi_apply _)
  let toPrefix : (S → RetainedBlock o) → (Fin n → RetainedBlock o) :=
    fun u i ↦ u ⟨i, by simp [S, externalPrefixIndexSet]⟩
  let toBlock : (T → RetainedBlock o) → (Fin m → RetainedBlock o) :=
    fun u i ↦ u ⟨n + i, by
      simp only [T, externalBlockIndexSet, Finset.mem_image]
      exact ⟨i, by simp, rfl⟩⟩
  have hc := h.comp (measurable_of_countable toPrefix) (measurable_of_countable toBlock)
  have hp : externalPrefix o n = fun x i ↦ x (i : ℕ) := rfl
  have hb : externalBlock o n m = fun x i ↦ x (n + (i : ℕ)) := rfl
  rw [hp, hb]
  simpa only [Function.comp_def, toPrefix, toBlock] using hc

theorem measure_externalPrefix_inter_externalBlock
    (n m : ℕ) (A : Set (Fin n → RetainedBlock o))
    (B : Set (Fin m → RetainedBlock o)) :
    externalBlocks o (externalPrefix o n ⁻¹' A ∩ externalBlock o n m ⁻¹' B) =
      externalBlockLaw o n A * externalBlockLaw o m B := by
  have h := (indepFun_externalPrefix_externalBlock o n m).measure_inter_preimage_eq_mul
    A B (Set.to_countable A).measurableSet (Set.to_countable B).measurableSet
  rw [← Measure.map_apply (measurable_externalPrefix o n)
      (Set.to_countable A).measurableSet, externalBlocks_map_externalPrefix] at h
  rw [← Measure.map_apply (measurable_externalBlock o n m)
      (Set.to_countable B).measurableSet, externalBlocks_map_externalBlock] at h
  exact h

/-! ## Finite-word return events -/

/-- Position after `j` letters of a retained-block word of length `n`. -/
def externalWordPosition {n : ℕ} (u : Fin n → RetainedBlock o) (j : Fin (n + 1)) : Point :=
  ∑ i : Fin j, retainedDisplacement o
    (u ⟨i, lt_of_lt_of_le i.isLt (Nat.le_of_lt_succ j.isLt)⟩)

@[simp] lemma externalWordPosition_zero {n : ℕ} (u : Fin n → RetainedBlock o) :
    externalWordPosition o u 0 = 0 := by
  change (∑ i : Fin 0, retainedDisplacement o (u ⟨i, by omega⟩)) = (0 : Point)
  exact Finset.sum_empty

lemma externalWordPosition_externalPrefix (η : ℕ → RetainedBlock o) (n : ℕ)
    (j : Fin (n + 1)) :
    externalWordPosition o (externalPrefix o n η) j = externalPosition o η j := by
  rw [externalWordPosition, externalPosition]
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i hi
  rfl

lemma externalWordPosition_last_eq_displacement {n : ℕ}
    (u : Fin n → RetainedBlock o) :
    externalWordPosition o u (Fin.last n) = externalWordDisplacement o u := by
  rw [externalWordPosition, externalWordDisplacement]
  apply Finset.sum_congr rfl
  intro i hi
  congr 2

/-- Finite words which make their first strictly positive return at their final time. -/
def externalFirstReturnWords (n : ℕ) : Set (Fin n → RetainedBlock o) :=
  {u | 0 < n ∧ externalWordPosition o u (Fin.last n) = 0 ∧
    ∀ j : Fin n, (0 : ℕ) < j → externalWordPosition o u j.castSucc ≠ 0}

/-- The external walk first returns at time `n`. -/
def externalFirstReturnAt (n : ℕ) : Set (ℕ → RetainedBlock o) :=
  {η | 0 < n ∧ externalPosition o η n = 0 ∧
    ∀ j, 0 < j → j < n → externalPosition o η j ≠ 0}

lemma externalFirstReturnAt_eq_prefix_preimage (n : ℕ) :
    externalFirstReturnAt o n =
      externalPrefix o n ⁻¹' externalFirstReturnWords o n := by
  ext η
  simp only [externalFirstReturnAt, externalFirstReturnWords, mem_ofPred_eq, mem_preimage]
  constructor
  · rintro ⟨hn, hreturn, hbefore⟩
    refine ⟨hn, ?_, ?_⟩
    · rw [externalWordPosition_externalPrefix]
      simpa using hreturn
    · intro j hj
      rw [externalWordPosition_externalPrefix]
      exact hbefore j hj j.isLt
  · rintro ⟨hn, hreturn, hbefore⟩
    refine ⟨hn, ?_, ?_⟩
    · rw [externalWordPosition_externalPrefix] at hreturn
      simpa using hreturn
    · intro j hjpos hjlt
      let j' : Fin n := ⟨j, hjlt⟩
      have hj' := hbefore j' hjpos
      rw [externalWordPosition_externalPrefix] at hj'
      simpa [j'] using hj'

lemma measurableSet_externalFirstReturnAt (n : ℕ) :
    MeasurableSet (externalFirstReturnAt o n) := by
  rw [externalFirstReturnAt_eq_prefix_preimage]
  exact (Set.to_countable (externalFirstReturnWords o n)).measurableSet.preimage
    (measurable_externalPrefix o n)

lemma externalFirstReturnAt_pairwise_disjoint :
    Pairwise fun i j ↦ Disjoint (externalFirstReturnAt o i) (externalFirstReturnAt o j) := by
  intro i j hij
  rw [Set.disjoint_left]
  intro η hi hj
  rcases lt_trichotomy i j with hlt | heq | hgt
  · exact (hj.2.2 i hi.1 hlt) hi.2.1
  · exact hij heq
  · exact (hi.2.2 j hj.1 hgt) hj.2.1

/-- The displacement of the `m` external increments beginning at `n`. -/
def externalRelativeReturnAt (n m : ℕ) : Set (ℕ → RetainedBlock o) :=
  {η | externalPosition o η (n + m) - externalPosition o η n = 0}

lemma externalPosition_add_sub (η : ℕ → RetainedBlock o) (n m : ℕ) :
    externalPosition o η (n + m) - externalPosition o η n =
      externalWordDisplacement o (externalBlock o n m η) := by
  simp only [externalPosition, externalWordDisplacement, externalBlock]
  rw [Finset.sum_range_add, add_sub_cancel_left]
  rw [← Fin.sum_univ_eq_sum_range]

lemma externalRelativeReturnAt_eq_block_preimage (n m : ℕ) :
    externalRelativeReturnAt o n m =
      externalBlock o n m ⁻¹' (externalReturningWords o m :
        Set (Fin m → RetainedBlock o)) := by
  ext η
  simp only [externalRelativeReturnAt, mem_ofPred_eq, mem_preimage,
    Finset.mem_coe, mem_externalReturningWords]
  rw [externalPosition_add_sub]

lemma externalReturnAt_eq_prefix_preimage (n : ℕ) :
    {η : ℕ → RetainedBlock o | externalPosition o η n = 0} =
      externalPrefix o n ⁻¹' (externalReturningWords o n :
        Set (Fin n → RetainedBlock o)) := by
  ext η
  simp only [mem_ofPred_eq, mem_preimage, Finset.mem_coe, mem_externalReturningWords]
  rw [externalPosition_eq_externalWordDisplacement]

lemma externalBlockLaw_returningWords (n : ℕ) :
    externalBlockLaw o n (externalReturningWords o n) =
      externalBlocks o {η | externalPosition o η n = 0} := by
  rw [← externalBlocks_map_externalPrefix]
  rw [Measure.map_apply (measurable_externalPrefix o n) (by measurability)]
  rw [externalReturnAt_eq_prefix_preimage]

lemma measure_externalFirstReturn_inter_relative (k m : ℕ) :
    externalBlocks o (externalFirstReturnAt o k ∩ externalRelativeReturnAt o k m) =
      externalBlocks o (externalFirstReturnAt o k) *
        externalBlocks o {η | externalPosition o η m = 0} := by
  rw [externalFirstReturnAt_eq_prefix_preimage,
    externalRelativeReturnAt_eq_block_preimage]
  rw [measure_externalPrefix_inter_externalBlock]
  rw [← Measure.map_apply (measurable_externalPrefix o k)
      (Set.to_countable (externalFirstReturnWords o k)).measurableSet,
    externalBlocks_map_externalPrefix]
  rw [externalBlockLaw_returningWords]

/-! ## Exact renewal identity -/

/-- The external chain is at the origin at time `n`. -/
def externalReturnAt (n : ℕ) : Set (ℕ → RetainedBlock o) :=
  {η | externalPosition o η n = 0}

lemma measurableSet_externalReturnAt (n : ℕ) : MeasurableSet (externalReturnAt o n) :=
  measurableSet_externalPosition_eq_zero o n

lemma externalFirstReturnAt_exists_of_return {η : ℕ → RetainedBlock o} {n : ℕ}
    (hn : 0 < n) (hreturn : η ∈ externalReturnAt o n) :
    ∃ k ∈ Finset.Icc 1 n, η ∈ externalFirstReturnAt o k := by
  let k := Nat.find (show ∃ k, 0 < k ∧ externalPosition o η k = 0 from
    ⟨n, hn, hreturn⟩)
  have hk := Nat.find_spec (show ∃ k, 0 < k ∧ externalPosition o η k = 0 from
    ⟨n, hn, hreturn⟩)
  have hkn : k ≤ n := Nat.find_min' _ ⟨hn, hreturn⟩
  refine ⟨k, Finset.mem_Icc.mpr ⟨Nat.succ_le_iff.mpr hk.1, hkn⟩,
    hk.1, hk.2, ?_⟩
  intro j hjpos hjlt hjzero
  exact (Nat.not_lt_of_ge (Nat.find_min'
    (show ∃ k, 0 < k ∧ externalPosition o η k = 0 from ⟨n, hn, hreturn⟩)
    ⟨hjpos, hjzero⟩)) hjlt

lemma externalReturnAt_subset_renewal_union {n : ℕ} (hn : 0 < n) :
    externalReturnAt o n ⊆ ⋃ k ∈ Finset.Icc 1 n,
      externalFirstReturnAt o k ∩ externalRelativeReturnAt o k (n - k) := by
  intro η hη
  obtain ⟨k, hk, hkfirst⟩ := externalFirstReturnAt_exists_of_return o hn hη
  rw [mem_iUnion₂]
  refine ⟨k, hk, hkfirst, ?_⟩
  have hkn : k ≤ n := (Finset.mem_Icc.mp hk).2
  change externalPosition o η (k + (n - k)) - externalPosition o η k = 0
  rw [Nat.add_sub_of_le hkn, hη, hkfirst.2.1]
  simp

lemma externalRenewalPiece_subset_returnAt {n k : ℕ} (hk : k ≤ n) :
    externalFirstReturnAt o k ∩ externalRelativeReturnAt o k (n - k) ⊆
      externalReturnAt o n := by
  intro η hη
  change externalPosition o η n = 0
  have hrel : externalPosition o η (k + (n - k)) - externalPosition o η k = 0 := hη.2
  rw [Nat.add_sub_of_le hk, hη.1.2.1] at hrel
  change externalPosition o η n - (0 : Point) = 0 at hrel
  simpa using hrel

lemma externalReturnAt_eq_renewal_union {n : ℕ} (hn : 0 < n) :
    externalReturnAt o n = ⋃ k ∈ Finset.Icc 1 n,
      externalFirstReturnAt o k ∩ externalRelativeReturnAt o k (n - k) := by
  apply Set.Subset.antisymm (externalReturnAt_subset_renewal_union o hn)
  rw [iUnion_subset_iff]
  intro k
  rw [iUnion_subset_iff]
  intro hk
  exact externalRenewalPiece_subset_returnAt o (Finset.mem_Icc.mp hk).2

lemma measurableSet_externalRelativeReturnAt (n m : ℕ) :
    MeasurableSet (externalRelativeReturnAt o n m) := by
  rw [externalRelativeReturnAt_eq_block_preimage]
  exact (Set.to_countable (externalReturningWords o m :
    Set (Fin m → RetainedBlock o))).measurableSet.preimage
      (measurable_externalBlock o n m)

lemma externalRenewalPiece_pairwiseDisjoint (n : ℕ) :
    Set.PairwiseDisjoint (↑(Finset.Icc 1 n) : Set ℕ)
      fun k ↦ externalFirstReturnAt o k ∩ externalRelativeReturnAt o k (n - k) := by
  intro i hi j hj hij
  exact (externalFirstReturnAt_pairwise_disjoint o hij).mono
    inter_subset_left inter_subset_left

/-- Exact first-return renewal equation for the retained-block external walk. -/
theorem externalReturnProbability_renewal {n : ℕ} (hn : 0 < n) :
    externalBlocks o (externalReturnAt o n) =
      ∑ k ∈ Finset.Icc 1 n,
        externalBlocks o (externalFirstReturnAt o k) *
          externalBlocks o (externalReturnAt o (n - k)) := by
  rw [externalReturnAt_eq_renewal_union o hn]
  rw [measure_biUnion_finset (externalRenewalPiece_pairwiseDisjoint o n)]
  · apply Finset.sum_congr rfl
    intro k hk
    simpa only [externalReturnAt] using
      measure_externalFirstReturn_inter_relative o k (n - k)
  · intro k hk
    exact (measurableSet_externalFirstReturnAt o k).inter
      (measurableSet_externalRelativeReturnAt o k (n - k))

/-! ## Truncated Green-function reductions -/

/-- Real-valued external return probability. -/
noncomputable def externalReturnProbability (n : ℕ) : ℝ :=
  (externalBlocks o (externalReturnAt o n)).toReal

/-- Real-valued external first-return probability. -/
noncomputable def externalFirstReturnProbability (n : ℕ) : ℝ :=
  (externalBlocks o (externalFirstReturnAt o n)).toReal

lemma externalReturnProbability_nonneg (n : ℕ) :
    0 ≤ externalReturnProbability o n := ENNReal.toReal_nonneg

lemma externalFirstReturnProbability_nonneg (n : ℕ) :
    0 ≤ externalFirstReturnProbability o n := ENNReal.toReal_nonneg

@[simp] lemma externalReturnProbability_zero : externalReturnProbability o 0 = 1 := by
  have hset : externalReturnAt o 0 = Set.univ := by
    ext η
    simp [externalReturnAt, externalPosition_zero]
  simp [externalReturnProbability, hset]

@[simp] lemma externalFirstReturnProbability_zero :
    externalFirstReturnProbability o 0 = 0 := by
  have hset : externalFirstReturnAt o 0 = ∅ := by
    ext η
    simp [externalFirstReturnAt]
  simp [externalFirstReturnProbability, hset]

theorem externalReturnProbabilityReal_renewal {n : ℕ} (hn : 0 < n) :
    externalReturnProbability o n =
      ∑ k ∈ Finset.Icc 1 n,
        externalFirstReturnProbability o k * externalReturnProbability o (n - k) := by
  rw [externalReturnProbability, externalReturnProbability_renewal o hn]
  rw [ENNReal.toReal_sum]
  · apply Finset.sum_congr rfl
    intro k hk
    rw [ENNReal.toReal_mul]
    rfl
  · intro k hk
    exact ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)

/-- Real truncated Green function, including the visit at time zero. -/
noncomputable def externalTruncatedGreenReal (n : ℕ) : ℝ :=
  RenewalTail.truncatedGreen (externalReturnProbability o) n

/-- Cumulative real first-return mass through time `n`. -/
noncomputable def externalFirstReturnMass (n : ℕ) : ℝ :=
  RenewalTail.firstReturnMass (externalFirstReturnProbability o) n

/-- Renewal reduces the cumulative first-return mass to a ratio of two
truncated Green functions. -/
theorem externalFirstReturnMass_mul_green_le (n : ℕ) :
    externalFirstReturnMass o n * externalTruncatedGreenReal o n ≤
      externalTruncatedGreenReal o (2 * n) - 1 := by
  exact RenewalTail.firstReturnMass_mul_truncatedGreen_le
    (externalFirstReturnProbability o) (externalReturnProbability o)
    (externalFirstReturnProbability_nonneg o) (externalReturnProbability_nonneg o)
    (externalFirstReturnProbability_zero o) (externalReturnProbability_zero o)
    (fun m hm ↦ externalReturnProbabilityReal_renewal o hm) n

/-- ENNReal truncated Green function for the external walk. -/
noncomputable def externalTruncatedGreen (n : ℕ) : ℝ≥0∞ :=
  ∑ j ∈ Finset.range (n + 1), externalBlocks o (externalReturnAt o j)

/-! ## Excursion recursion for the local-time tail -/

lemma externalOriginLocalTime_eq_sum_indicator_nat
    (η : ℕ → RetainedBlock o) (n : ℕ) :
    externalOriginLocalTime o η n =
      ∑ j ∈ Finset.range (n + 1), if externalPosition o η j = 0 then 1 else 0 := by
  rw [externalOriginLocalTime, Finset.card_filter]

lemma externalPosition_shift (η : ℕ → RetainedBlock o) (k j : ℕ) :
    externalPosition o (externalShift o k η) j =
      externalPosition o η (k + j) - externalPosition o η k := by
  simp only [externalPosition, externalShift]
  rw [Finset.sum_range_add, add_sub_cancel_left]

lemma externalOriginLocalTime_decompose_firstReturn
    {η : ℕ → RetainedBlock o} {k n : ℕ}
    (hk : η ∈ externalFirstReturnAt o k) (hkn : k ≤ n) :
    externalOriginLocalTime o η n =
      externalOriginLocalTime o (externalShift o k η) (n - k) + 1 := by
  rw [externalOriginLocalTime_eq_sum_indicator_nat,
    externalOriginLocalTime_eq_sum_indicator_nat]
  have hsplit : n + 1 = k + (n - k + 1) := by omega
  rw [hsplit, Finset.sum_range_add]
  have hbefore :
      (∑ j ∈ Finset.range k, if externalPosition o η j = 0 then 1 else 0) = 1 := by
    calc
      (∑ j ∈ Finset.range k, if externalPosition o η j = 0 then 1 else 0) =
          ∑ j ∈ Finset.range k, if j = 0 then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro j hj
        by_cases hj0 : j = 0
        · subst j
          simp [externalPosition_zero]
        · have hjlt : j < k := Finset.mem_range.mp hj
          have hjpos : 0 < j := Nat.pos_of_ne_zero hj0
          have hne := hk.2.2 j hjpos hjlt
          simp [hj0, hne]
      _ = 1 := by simp [hk.1]
  rw [hbefore]
  have htail :
      (∑ x ∈ Finset.range (n - k + 1),
          if externalPosition o η (k + x) = 0 then 1 else 0) =
        ∑ x ∈ Finset.range (n - k + 1),
          if externalPosition o (externalShift o k η) x = 0 then 1 else 0 := by
    apply Finset.sum_congr rfl
    intro x hx
    have hshift := externalPosition_shift o η k x
    rw [hk.2.1] at hshift
    change externalPosition o (externalShift o k η) x =
      externalPosition o η (k + x) - (0 : Point) at hshift
    rw [sub_zero] at hshift
    rw [hshift]
  rw [htail]
  omega

/-- Origin local time computed intrinsically from a finite retained word. -/
def externalWordOriginLocalTime {n : ℕ} (u : Fin n → RetainedBlock o) : ℕ :=
  (Finset.univ.filter fun j : Fin (n + 1) ↦ externalWordPosition o u j = 0).card

lemma externalWordOriginLocalTime_externalPrefix
    (η : ℕ → RetainedBlock o) (n : ℕ) :
    externalWordOriginLocalTime o (externalPrefix o n η) =
      externalOriginLocalTime o η n := by
  unfold externalWordOriginLocalTime externalOriginLocalTime
  rw [Finset.card_filter, Finset.card_filter]
  rw [← Fin.sum_univ_eq_sum_range
    (fun j : ℕ ↦ if externalPosition o η j = 0 then 1 else 0) (n + 1)]
  apply Finset.sum_congr rfl
  intro j hj
  rw [externalWordPosition_externalPrefix]

/-- Finite words with at least `r` positive returns, equivalently local time
at least `r + 1` after including time zero. -/
def externalReturnTailWords (r n : ℕ) : Set (Fin n → RetainedBlock o) :=
  {u | r + 1 ≤ externalWordOriginLocalTime o u}

lemma externalReturnTail_eq_prefix_preimage (r n : ℕ) :
    {η : ℕ → RetainedBlock o | r + 1 ≤ externalOriginLocalTime o η n} =
      externalPrefix o n ⁻¹' externalReturnTailWords o r n := by
  ext η
  simp only [externalReturnTailWords, mem_ofPred_eq, mem_preimage]
  rw [externalWordOriginLocalTime_externalPrefix]

lemma externalShiftReturnTail_eq_block_preimage (r k n : ℕ) :
    {η : ℕ → RetainedBlock o |
        r + 1 ≤ externalOriginLocalTime o (externalShift o k η) n} =
      externalBlock o k n ⁻¹' externalReturnTailWords o r n := by
  ext η
  simp only [mem_ofPred_eq, mem_preimage, externalReturnTailWords]
  rw [← externalWordOriginLocalTime_externalPrefix o (externalShift o k η) n]
  rfl

lemma externalBlockLaw_returnTailWords (r n : ℕ) :
    externalBlockLaw o n (externalReturnTailWords o r n) =
      externalBlocks o {η | r + 1 ≤ externalOriginLocalTime o η n} := by
  rw [← externalBlocks_map_externalPrefix]
  rw [Measure.map_apply (measurable_externalPrefix o n)
    (Set.to_countable (externalReturnTailWords o r n)).measurableSet]
  rw [externalReturnTail_eq_prefix_preimage]

lemma measure_externalFirstReturn_inter_shiftReturnTail (r k n : ℕ) :
    externalBlocks o (externalFirstReturnAt o k ∩
        {η | r + 1 ≤ externalOriginLocalTime o (externalShift o k η) n}) =
      externalBlocks o (externalFirstReturnAt o k) *
        externalBlocks o {η | r + 1 ≤ externalOriginLocalTime o η n} := by
  rw [externalFirstReturnAt_eq_prefix_preimage,
    externalShiftReturnTail_eq_block_preimage]
  rw [measure_externalPrefix_inter_externalBlock]
  rw [← Measure.map_apply (measurable_externalPrefix o k)
      (Set.to_countable (externalFirstReturnWords o k)).measurableSet,
    externalBlocks_map_externalPrefix]
  rw [externalBlockLaw_returnTailWords]

/-- The probability of at least `r` strictly positive returns through time
`n`; equivalently, the origin local time is at least `r + 1`. -/
noncomputable def externalReturnTail (r n : ℕ) : ℝ≥0∞ :=
  externalBlocks o {η | r + 1 ≤ externalOriginLocalTime o η n}

/-- Probability of making a first positive return by time `n`. -/
noncomputable def externalFirstReturnMassENNReal (n : ℕ) : ℝ≥0∞ :=
  ∑ k ∈ Finset.Icc 1 n, externalBlocks o (externalFirstReturnAt o k)

lemma externalOriginLocalTime_mono {η : ℕ → RetainedBlock o} {m n : ℕ}
    (hmn : m ≤ n) :
    externalOriginLocalTime o η m ≤ externalOriginLocalTime o η n := by
  unfold externalOriginLocalTime
  apply Finset.card_le_card
  intro j hj
  rw [Finset.mem_filter] at hj ⊢
  exact ⟨Finset.range_mono (Nat.succ_le_succ hmn) hj.1, hj.2⟩

lemma externalReturnTail_mono_horizon (r : ℕ) {m n : ℕ} (hmn : m ≤ n) :
    externalReturnTail o r m ≤ externalReturnTail o r n := by
  apply measure_mono
  intro η hη
  exact hη.trans (externalOriginLocalTime_mono o hmn)

lemma exists_positive_external_return_of_two_le_localTime
    {η : ℕ → RetainedBlock o} {n : ℕ}
    (hη : 2 ≤ externalOriginLocalTime o η n) :
    ∃ j ∈ Finset.Icc 1 n, η ∈ externalReturnAt o j := by
  by_contra h
  push Not at h
  have hlocal : externalOriginLocalTime o η n = 1 := by
    rw [externalOriginLocalTime_eq_sum_indicator_nat]
    calc
      (∑ j ∈ Finset.range (n + 1),
          if externalPosition o η j = 0 then 1 else 0) =
          ∑ j ∈ Finset.range (n + 1), if j = 0 then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro j hj
        by_cases hj0 : j = 0
        · subst j
          simp [externalPosition_zero]
        · have hjpos : 1 ≤ j := Nat.one_le_iff_ne_zero.mpr hj0
          have hjle : j ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
          have hne := h j (Finset.mem_Icc.mpr ⟨hjpos, hjle⟩)
          have hnepos : externalPosition o η j ≠ 0 := hne
          simp only [hnepos, hj0, if_false]
      _ = 1 := by simp
  omega

lemma externalReturnTail_succ_subset_renewal_union (r n : ℕ) :
    {η : ℕ → RetainedBlock o | r + 2 ≤ externalOriginLocalTime o η n} ⊆
      ⋃ k ∈ Finset.Icc 1 n, externalFirstReturnAt o k ∩
        {η | r + 1 ≤ externalOriginLocalTime o (externalShift o k η) (n - k)} := by
  intro η hη
  change r + 2 ≤ externalOriginLocalTime o η n at hη
  have htwo : 2 ≤ externalOriginLocalTime o η n := by omega
  obtain ⟨j, hj, hjreturn⟩ :=
    exists_positive_external_return_of_two_le_localTime o htwo
  obtain ⟨k, hk, hkfirst⟩ := externalFirstReturnAt_exists_of_return o
    (Finset.mem_Icc.mp hj).1 hjreturn
  have hkN : k ∈ Finset.Icc 1 n := Finset.mem_Icc.mpr
    ⟨(Finset.mem_Icc.mp hk).1, (Finset.mem_Icc.mp hk).2.trans (Finset.mem_Icc.mp hj).2⟩
  have hkn : k ≤ n := (Finset.mem_Icc.mp hkN).2
  rw [mem_iUnion₂]
  refine ⟨k, hkN, hkfirst, ?_⟩
  have hdecomp := externalOriginLocalTime_decompose_firstReturn o hkfirst hkn
  change r + 1 ≤ externalOriginLocalTime o (externalShift o k η) (n - k)
  omega

/-- Exact one-excursion recursion for the finite-horizon local-time tail. -/
theorem externalReturnTail_succ_le (r n : ℕ) :
    externalReturnTail o (r + 1) n ≤
      externalFirstReturnMassENNReal o n * externalReturnTail o r n := by
  calc
    externalReturnTail o (r + 1) n ≤
        externalBlocks o (⋃ k ∈ Finset.Icc 1 n,
          externalFirstReturnAt o k ∩
            {η | r + 1 ≤ externalOriginLocalTime o
              (externalShift o k η) (n - k)}) :=
      measure_mono (externalReturnTail_succ_subset_renewal_union o r n)
    _ ≤ ∑ k ∈ Finset.Icc 1 n,
        externalBlocks o (externalFirstReturnAt o k ∩
          {η | r + 1 ≤ externalOriginLocalTime o
            (externalShift o k η) (n - k)}) :=
      measure_biUnion_finset_le (μ := externalBlocks o) (Finset.Icc 1 n) _
    _ = ∑ k ∈ Finset.Icc 1 n,
        externalBlocks o (externalFirstReturnAt o k) *
          externalReturnTail o r (n - k) := by
      apply Finset.sum_congr rfl
      intro k hk
      exact measure_externalFirstReturn_inter_shiftReturnTail o r k (n - k)
    _ ≤ ∑ k ∈ Finset.Icc 1 n,
        externalBlocks o (externalFirstReturnAt o k) * externalReturnTail o r n := by
      apply Finset.sum_le_sum
      intro k hk
      exact mul_le_mul_right (externalReturnTail_mono_horizon o r (Nat.sub_le n k)) _
    _ = externalFirstReturnMassENNReal o n * externalReturnTail o r n := by
      rw [externalFirstReturnMassENNReal, Finset.sum_mul]

@[simp] lemma externalReturnTail_zero (n : ℕ) : externalReturnTail o 0 n = 1 := by
  have hset : {η : ℕ → RetainedBlock o | 0 + 1 ≤ externalOriginLocalTime o η n} =
      Set.univ := by
    ext η
    simp only [mem_ofPred_eq, mem_univ, iff_true]
    unfold externalOriginLocalTime
    rw [Finset.one_le_card]
    exact ⟨0, by simp [externalPosition_zero]⟩
  rw [externalReturnTail, hset, measure_univ]

/-- Iterating the first-return recursion gives the exact geometric majorant
by the finite-horizon hitting probability. -/
theorem externalReturnTail_le_firstReturnMass_pow (r n : ℕ) :
    externalReturnTail o r n ≤ (externalFirstReturnMassENNReal o n) ^ r := by
  induction r with
  | zero => simp
  | succ r ih =>
      calc
        externalReturnTail o (r + 1) n ≤
            externalFirstReturnMassENNReal o n * externalReturnTail o r n :=
          externalReturnTail_succ_le o r n
        _ ≤ externalFirstReturnMassENNReal o n *
            (externalFirstReturnMassENNReal o n) ^ r := mul_le_mul_right ih _
        _ = (externalFirstReturnMassENNReal o n) ^ (r + 1) := by
          rw [pow_succ']

/-- Geometric external-local-time tail from a Green-scaled hitting estimate.
The hypothesis concerns only the first-return/hitting probability, never the
target local-time tail. -/
theorem externalOriginLocalTime_tail_le_geometric
    (r n : ℕ) (c : ℝ≥0∞)
    (hhit : externalFirstReturnMassENNReal o n ≤
      1 - c / externalTruncatedGreen o n) :
    externalBlocks o {η | r + 1 ≤ externalOriginLocalTime o η n} ≤
      (1 - c / externalTruncatedGreen o n) ^ r := by
  exact (externalReturnTail_le_firstReturnMass_pow o r n).trans
    (pow_le_pow_left' hhit r)

/-- Threshold-indexed form: local time at least `k` requires `k - 1`
strictly positive returns. -/
theorem externalOriginLocalTime_tail_le_geometric_threshold
    (k n : ℕ) (hk : 0 < k) (c : ℝ≥0∞)
    (hhit : externalFirstReturnMassENNReal o n ≤
      1 - c / externalTruncatedGreen o n) :
    externalBlocks o {η | k ≤ externalOriginLocalTime o η n} ≤
      (1 - c / externalTruncatedGreen o n) ^ (k - 1) := by
  have hk_eq : k - 1 + 1 = k := by omega
  simpa only [hk_eq] using
    externalOriginLocalTime_tail_le_geometric o (k - 1) n c hhit

lemma externalTruncatedGreen_eq_returningWords (n : ℕ) :
    externalTruncatedGreen o n =
      ∑ j ∈ Finset.range (n + 1),
        ((externalReturningWords o j).card : ℝ≥0∞) * (1 / 15) ^ j := by
  unfold externalTruncatedGreen externalReturnAt
  apply Finset.sum_congr rfl
  intro j hj
  exact externalBlocks_return_probability o j

/-- A direct, assumption-free reduction of the `k`-visit tail to the
truncated Green function. -/
theorem externalOriginLocalTime_tail_le_green (n k : ℕ) (hk : 0 < k) :
    externalBlocks o {η | k ≤ externalOriginLocalTime o η n} ≤
      externalTruncatedGreen o n / k := by
  rw [externalTruncatedGreen_eq_returningWords]
  exact externalOriginLocalTime_tail_le o n k hk

/-- Any upper estimate for the truncated Green function immediately yields
the corresponding explicit local-time tail estimate. -/
theorem externalOriginLocalTime_tail_le_of_green_bound
    (n k : ℕ) (hk : 0 < k) (G : ℝ≥0∞)
    (hG : externalTruncatedGreen o n ≤ G) :
    externalBlocks o {η | k ≤ externalOriginLocalTime o η n} ≤ G / k := by
  exact (externalOriginLocalTime_tail_le_green o n k hk).trans
    (ENNReal.div_le_div_right hG k)

end Erdos1165.ExternalRenewal
