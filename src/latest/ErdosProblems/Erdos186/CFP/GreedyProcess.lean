/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.GrowthLemmas
import ErdosProblems.Erdos186.CFP.SubsetSumGrowth

/-!
# The greedy subset-sum process in the CFP argument

This file formalizes the iterative process on pages 23--25 of
Conlon--Fox--Pham, *Homogeneous structures in subset sums and non-averaging
sets*.  Starting from a finite set `A` of integers, at every nonterminal
step we select an available element whose translate creates the largest
boundary of the current subset-sum set.

The construction below is unconditional and finite.  The last section
separates the numerical conclusion of the argument from its deep structural
inputs: high-fold sumset estimates and comparisons between consecutive
dyadic thresholds are explicit hypotheses.
-/

namespace Erdos186.CFP.Greedy

open scoped BigOperators
open GrowthLemmas

/-! ## Subset sums and a maximal boundary point -/

/-- The finite set of all subset sums of a finite set of integers. -/
def subsetSums (A : Finset ℤ) : Finset ℤ :=
  SubsetSumGrowth.weightedSubsetSums A id

@[simp] theorem subsetSums_empty : subsetSums (∅ : Finset ℤ) = {0} := by
  simp [subsetSums, SubsetSumGrowth.weightedSubsetSums]

@[simp] theorem zero_mem_subsetSums (A : Finset ℤ) : 0 ∈ subsetSums A := by
  exact SubsetSumGrowth.zero_mem_weightedSubsetSums A id

theorem subsetSums_insert {A : Finset ℤ} {a : ℤ} (ha : a ∉ A) :
    subsetSums (insert a A) =
      subsetSums A ∪ translate a (subsetSums A) := by
  simpa [subsetSums, GrowthLemmas.translate, SubsetSumGrowth.translate] using
    (SubsetSumGrowth.weightedSubsetSums_insert
      (A := A) (w := id) (a := a) ha)

/-- Choose an element of `available` whose boundary of `S` is maximal.
The value on the empty set is irrelevant and is fixed to be zero. -/
noncomputable def maximalBoundaryElement
    (S available : Finset ℤ) : ℤ :=
  if h : available.Nonempty then
    Classical.choose
      (available.exists_max_image (fun a ↦ (boundary S a).card) h)
  else 0

theorem maximalBoundaryElement_mem {S available : Finset ℤ}
    (havailable : available.Nonempty) :
    maximalBoundaryElement S available ∈ available := by
  rw [maximalBoundaryElement, dif_pos havailable]
  exact (Classical.choose_spec
    (available.exists_max_image (fun a ↦ (boundary S a).card) havailable)).1

theorem boundary_card_le_maximal {S available : Finset ℤ}
    (havailable : available.Nonempty) {a : ℤ} (ha : a ∈ available) :
    (boundary S a).card ≤
      (boundary S (maximalBoundaryElement S available)).card := by
  rw [maximalBoundaryElement, dif_pos havailable]
  exact (Classical.choose_spec
    (available.exists_max_image (fun a ↦ (boundary S a).card) havailable)).2 a ha

/-! ## The finite recursion -/

/-- The elements selected in the first `j` steps of the greedy process. -/
noncomputable def selected (A : Finset ℤ) : ℕ → Finset ℤ
  | 0 => ∅
  | j + 1 =>
      let B := selected A j
      let R := A \ B
      if _h : R.Nonempty then
        insert (maximalBoundaryElement (subsetSums B) R) B
      else B

/-- The elements which remain available after `j` selections. -/
noncomputable def available (A : Finset ℤ) (j : ℕ) : Finset ℤ :=
  A \ selected A j

/-- The subset sums after `j` greedy selections. -/
noncomputable def sums (A : Finset ℤ) (j : ℕ) : Finset ℤ :=
  subsetSums (selected A j)

/-- The element selected at the next step. -/
noncomputable def nextElement (A : Finset ℤ) (j : ℕ) : ℤ :=
  maximalBoundaryElement (sums A j) (available A j)

@[simp] theorem selected_zero (A : Finset ℤ) : selected A 0 = ∅ := rfl

@[simp] theorem available_zero (A : Finset ℤ) : available A 0 = A := by
  simp [available]

@[simp] theorem sums_zero (A : Finset ℤ) : sums A 0 = {0} := by
  simp [sums]

theorem selected_succ_of_available_nonempty {A : Finset ℤ} {j : ℕ}
    (havailable : (available A j).Nonempty) :
    selected A (j + 1) = insert (nextElement A j) (selected A j) := by
  have havailable' : (A \ selected A j).Nonempty := by
    simpa only [available] using havailable
  simp only [selected, nextElement, sums, available]
  rw [dif_pos havailable']

theorem nextElement_mem_available {A : Finset ℤ} {j : ℕ}
    (havailable : (available A j).Nonempty) :
    nextElement A j ∈ available A j :=
  maximalBoundaryElement_mem havailable

theorem nextElement_maximal {A : Finset ℤ} {j : ℕ}
    (havailable : (available A j).Nonempty) {a : ℤ}
    (ha : a ∈ available A j) :
    (boundary (sums A j) a).card ≤
      (boundary (sums A j) (nextElement A j)).card :=
  boundary_card_le_maximal havailable ha

theorem selected_subset (A : Finset ℤ) (j : ℕ) : selected A j ⊆ A := by
  induction j with
  | zero => simp
  | succ j ih =>
      by_cases havailable : (available A j).Nonempty
      · rw [selected_succ_of_available_nonempty havailable]
        exact Finset.insert_subset
          ((Finset.mem_sdiff.mp (nextElement_mem_available havailable)).1) ih
      · simp only [selected, available] at havailable ⊢
        rw [dif_neg havailable]
        exact ih

/-- After `j` steps exactly `min j |A|` elements have been selected. -/
theorem card_selected (A : Finset ℤ) (j : ℕ) :
    (selected A j).card = min j A.card := by
  induction j with
  | zero => simp
  | succ j ih =>
      by_cases hj : j < A.card
      · have hcardlt : (selected A j).card < A.card := by
          simpa [ih, Nat.min_eq_left (Nat.le_of_lt hj)] using hj
        have havailable : (available A j).Nonempty := by
          exact Finset.sdiff_nonempty_of_card_lt_card hcardlt
        rw [selected_succ_of_available_nonempty havailable,
          Finset.card_insert_of_notMem]
        · rw [ih]
          simp [Nat.min_eq_left (Nat.succ_le_iff.mpr hj),
            Nat.min_eq_left (Nat.le_of_lt hj)]
        · exact (Finset.mem_sdiff.mp
            (nextElement_mem_available havailable)).2
      · have hcard : (selected A j).card = A.card := by
          rw [ih, Nat.min_eq_right (Nat.le_of_not_gt hj)]
        have hselected : selected A j = A :=
          Finset.eq_of_subset_of_card_le (selected_subset A j) (by omega)
        have havailable : ¬ (available A j).Nonempty := by
          simp [available, hselected]
        simp only [selected, available] at havailable ⊢
        rw [dif_neg havailable, hcard]
        exact (Nat.min_eq_right (by omega)).symm

theorem card_selected_eq {A : Finset ℤ} {j : ℕ} (hj : j ≤ A.card) :
    (selected A j).card = j := by
  rw [card_selected, Nat.min_eq_left hj]

theorem available_nonempty {A : Finset ℤ} {j : ℕ} (hj : j < A.card) :
    (available A j).Nonempty := by
  apply Finset.sdiff_nonempty_of_card_lt_card
  rw [card_selected_eq hj.le]
  exact hj

theorem card_available (A : Finset ℤ) (j : ℕ) :
    (available A j).card = A.card - min j A.card := by
  rw [available, Finset.card_sdiff_of_subset (selected_subset A j), card_selected]

theorem card_available_eq {A : Finset ℤ} {j : ℕ} (hj : j ≤ A.card) :
    (available A j).card = A.card - j := by
  rw [card_available, Nat.min_eq_left hj]

/-! ## Exact subset-sum and cardinal growth at a step -/

theorem sums_succ {A : Finset ℤ} {j : ℕ} (hj : j < A.card) :
    sums A (j + 1) = sums A j ∪ translate (nextElement A j) (sums A j) := by
  have havailable := available_nonempty hj
  have hnotmem : nextElement A j ∉ selected A j :=
    (Finset.mem_sdiff.mp (nextElement_mem_available havailable)).2
  change subsetSums (selected A (j + 1)) =
    subsetSums (selected A j) ∪
      translate (nextElement A j) (subsetSums (selected A j))
  rw [selected_succ_of_available_nonempty havailable,
    subsetSums_insert hnotmem]

/-- The exact increment in the number of subset sums is the maximal
boundary cardinality chosen at that step. -/
theorem card_sums_succ {A : Finset ℤ} {j : ℕ} (hj : j < A.card) :
    (sums A (j + 1)).card = (sums A j).card +
      (boundary (sums A j) (nextElement A j)).card := by
  rw [sums_succ hj, boundary]
  calc
    (sums A j ∪ translate (nextElement A j) (sums A j)).card =
        (translate (nextElement A j) (sums A j) ∪ sums A j).card := by
      rw [Finset.union_comm]
    _ = (translate (nextElement A j) (sums A j) \ sums A j).card +
        (sums A j).card :=
      (Finset.card_sdiff_add_card
        (translate (nextElement A j) (sums A j)) (sums A j)).symm
    _ = (sums A j).card +
        (translate (nextElement A j) (sums A j) \ sums A j).card :=
      Nat.add_comm _ _

theorem sums_mono_step {A : Finset ℤ} {j : ℕ} (hj : j < A.card) :
    sums A j ⊆ sums A (j + 1) := by
  rw [sums_succ hj]
  exact Finset.subset_union_left

/-- In one step the subset-sum cardinality can grow by at most a factor of
two. -/
theorem card_sums_succ_le_two_mul {A : Finset ℤ} {j : ℕ}
    (hj : j < A.card) :
    (sums A (j + 1)).card ≤ 2 * (sums A j).card := by
  rw [sums_succ hj]
  calc
    (sums A j ∪ translate (nextElement A j) (sums A j)).card ≤
        (sums A j).card +
          (translate (nextElement A j) (sums A j)).card :=
      Finset.card_union_le _ _
    _ = 2 * (sums A j).card := by simp; omega

@[simp] theorem zero_mem_sums (A : Finset ℤ) (j : ℕ) :
    0 ∈ sums A j := zero_mem_subsetSums _

theorem sums_nonempty (A : Finset ℤ) (j : ℕ) :
    (sums A j).Nonempty := ⟨0, zero_mem_sums A j⟩

/-! ## Growth supplied by a large multifold sumset -/

/-- If a high-fold sumset of the currently available elements is at least
twice as large as the current subset-sum set, maximality of the greedy
choice gives the CFP one-step growth inequality.  This is the
division-free form of

`|sums (j+1)| / |sums j| ≥ 1 + 1 / (2*k)`.
-/
theorem card_sums_le_two_mul_mul_increment
    {A : Finset ℤ} {j k : ℕ} (hj : j < A.card)
    (hfold : 2 * (sums A j).card ≤
      (multifoldSumset k (insert 0 (available A j))).card) :
    (sums A j).card ≤ 2 * k *
      ((sums A (j + 1)).card - (sums A j).card) := by
  have havailable := available_nonempty hj
  have hwithZero : (insert 0 (available A j)).Nonempty := by simp
  obtain ⟨a, ha, hlarge⟩ :=
    exists_large_boundary_of_two_mul_card_le_multifoldSumset
      (sums A j) (insert 0 (available A j)) k
      (sums_nonempty A j) hwithZero hfold
  have haAvailable : a ∈ available A j := by
    rcases Finset.mem_insert.mp ha with ha0 | ha
    · subst a
      simp only [boundary_zero, Finset.card_empty, mul_zero] at hlarge
      exact False.elim ((Finset.card_pos.mpr (sums_nonempty A j)).ne'
        (Nat.eq_zero_of_le_zero hlarge))
    · exact ha
  have hmax := nextElement_maximal havailable haAvailable
  have hboundary : (sums A j).card ≤
      2 * k * (boundary (sums A j) (nextElement A j)).card :=
    hlarge.trans (Nat.mul_le_mul_left (2 * k) hmax)
  rw [card_sums_succ hj, Nat.add_sub_cancel_left]
  exact hboundary

/-- Multiplicative form of the preceding one-step inequality. -/
theorem succ_mul_card_sums_le_mul_card_sums_succ
    {A : Finset ℤ} {j k : ℕ} (hj : j < A.card)
    (hfold : 2 * (sums A j).card ≤
      (multifoldSumset k (insert 0 (available A j))).card) :
    (2 * k + 1) * (sums A j).card ≤
      (2 * k) * (sums A (j + 1)).card := by
  have hgrowth := card_sums_le_two_mul_mul_increment hj hfold
  have hmono : (sums A j).card ≤ (sums A (j + 1)).card := by
    exact Finset.card_le_card (sums_mono_step hj)
  calc
    (2 * k + 1) * (sums A j).card =
        (2 * k) * (sums A j).card + (sums A j).card := by ring
    _ ≤ (2 * k) * (sums A j).card +
        (2 * k) * ((sums A (j + 1)).card - (sums A j).card) :=
      Nat.add_le_add_left hgrowth _
    _ = (2 * k) * (sums A (j + 1)).card := by
      rw [← Nat.mul_add, Nat.add_sub_of_le hmono]

/-- The dyadic specialization used in the threshold argument. -/
theorem dyadic_growth
    {A : Finset ℤ} {j h : ℕ} (hj : j < A.card)
    (hfold : 2 * (sums A j).card ≤
      (multifoldSumset (2 ^ h) (insert 0 (available A j))).card) :
    (2 ^ (h + 1) + 1) * (sums A j).card ≤
      2 ^ (h + 1) * (sums A (j + 1)).card := by
  simpa [pow_succ, mul_comm, mul_left_comm, mul_assoc] using
    succ_mul_card_sums_le_mul_card_sums_succ hj hfold

/-! ## The source thresholds -/

/-- The finite family over which CFP takes the minimum defining `t_h`:
all subsets obtained after deleting at most `deletionBudget` elements. -/
def largeSubsets (A : Finset ℤ) (deletionBudget : ℕ) : Finset (Finset ℤ) :=
  A.powerset.filter fun B ↦ A.card ≤ B.card + deletionBudget

@[simp]
theorem mem_largeSubsets_iff {A B : Finset ℤ} {deletionBudget : ℕ} :
    B ∈ largeSubsets A deletionBudget ↔
      B ⊆ A ∧ A.card ≤ B.card + deletionBudget := by
  simp [largeSubsets]

theorem largeSubsets_nonempty (A : Finset ℤ) (deletionBudget : ℕ) :
    (largeSubsets A deletionBudget).Nonempty := by
  refine ⟨A, ?_⟩
  simp [largeSubsets]

/-- The set of high-fold cardinalities occurring in the definition of the
source threshold. -/
def multifoldCardinalities (A : Finset ℤ) (deletionBudget fold : ℕ) :
    Finset ℕ :=
  (largeSubsets A deletionBudget).image fun B ↦
    (multifoldSumset fold (insert 0 B)).card

theorem multifoldCardinalities_nonempty
    (A : Finset ℤ) (deletionBudget fold : ℕ) :
    (multifoldCardinalities A deletionBudget fold).Nonempty := by
  obtain ⟨B, hB⟩ := largeSubsets_nonempty A deletionBudget
  exact ⟨(multifoldSumset fold (insert 0 B)).card,
    Finset.mem_image.mpr ⟨B, hB, rfl⟩⟩

/-- The least high-fold cardinality before taking the source's factor
`1/2`. -/
noncomputable def minimumMultifoldCardinality
    (A : Finset ℤ) (deletionBudget fold : ℕ) : ℕ :=
  (multifoldCardinalities A deletionBudget fold).min'
    (multifoldCardinalities_nonempty A deletionBudget fold)

/-- A minimizing large subset exists because the source minimum is over a
nonempty finite family. -/
theorem exists_largeSubset_card_multifold_eq_minimum
    (A : Finset ℤ) (deletionBudget fold : ℕ) :
    ∃ B : Finset ℤ, B ⊆ A ∧ A.card ≤ B.card + deletionBudget ∧
      (multifoldSumset fold (insert 0 B)).card =
        minimumMultifoldCardinality A deletionBudget fold := by
  have hmem := Finset.min'_mem
    (multifoldCardinalities A deletionBudget fold)
    (multifoldCardinalities_nonempty A deletionBudget fold)
  obtain ⟨B, hBlarge, hBcard⟩ := Finset.mem_image.mp hmem
  have hlarge := mem_largeSubsets_iff.mp hBlarge
  refine ⟨B, hlarge.1, hlarge.2, ?_⟩
  simpa only [minimumMultifoldCardinality] using hBcard

/-- The minimum is bounded by the value at every admissible large subset. -/
theorem minimumMultifoldCardinality_le {A B : Finset ℤ}
    {deletionBudget fold : ℕ} (hB : B ⊆ A)
    (hcard : A.card ≤ B.card + deletionBudget) :
    minimumMultifoldCardinality A deletionBudget fold ≤
      (multifoldSumset fold (insert 0 B)).card := by
  apply Finset.min'_le
  exact Finset.mem_image.mpr
    ⟨B, mem_largeSubsets_iff.mpr ⟨hB, hcard⟩, rfl⟩

/-- The exact finite version of the threshold used on page 24 of CFP:
half the least `fold`-fold sumset cardinality among subsets obtained after
the allowed number of deletions. -/
noncomputable def foldThreshold
    (A : Finset ℤ) (deletionBudget fold : ℕ) : ℕ :=
  minimumMultifoldCardinality A deletionBudget fold / 2

/-- Every admissible large subset has high-fold sumset cardinality at least
twice the source threshold. -/
theorem two_mul_foldThreshold_le {A B : Finset ℤ}
    {deletionBudget fold : ℕ} (hB : B ⊆ A)
    (hcard : A.card ≤ B.card + deletionBudget) :
    2 * foldThreshold A deletionBudget fold ≤
      (multifoldSumset fold (insert 0 B)).card := by
  have hmin := minimumMultifoldCardinality_le
    (fold := fold) hB hcard
  calc
    2 * foldThreshold A deletionBudget fold =
        2 * (minimumMultifoldCardinality A deletionBudget fold / 2) := by
      rfl
    _ ≤ minimumMultifoldCardinality A deletionBudget fold := by
      omega
    _ ≤ (multifoldSumset fold (insert 0 B)).card := hmin

/-- The elements still available after a permitted number of greedy steps
are one of the subsets entering the source minimum. -/
theorem available_mem_largeSubsets {A : Finset ℤ}
    {j deletionBudget : ℕ} (hj : j ≤ A.card)
    (hbudget : j ≤ deletionBudget) :
    available A j ∈ largeSubsets A deletionBudget := by
  apply mem_largeSubsets_iff.mpr
  constructor
  · exact Finset.sdiff_subset
  · rw [card_available_eq hj]
    omega

/-- Once the current subset-sum set is below the source threshold, the
high-fold hypothesis required by the one-step greedy lemma follows
automatically. -/
theorem highFold_of_card_sums_le_foldThreshold {A : Finset ℤ}
    {j deletionBudget fold : ℕ} (hj : j ≤ A.card)
    (hbudget : j ≤ deletionBudget)
    (hsums : (sums A j).card ≤ foldThreshold A deletionBudget fold) :
    2 * (sums A j).card ≤
      (multifoldSumset fold (insert 0 (available A j))).card := by
  calc
    2 * (sums A j).card ≤ 2 * foldThreshold A deletionBudget fold := by
      gcongr
    _ ≤ (multifoldSumset fold (insert 0 (available A j))).card := by
      exact two_mul_foldThreshold_le
        (Finset.sdiff_subset : available A j ⊆ A)
        ((mem_largeSubsets_iff.mp
          (available_mem_largeSubsets hj hbudget)).2)

/-- Dyadic notation for the threshold `t_h` used in the proof of CFP
Theorem 1.5. -/
noncomputable def dyadicThreshold
    (A : Finset ℤ) (deletionBudget h : ℕ) : ℕ :=
  foldThreshold A deletionBudget (2 ^ h)

/-- Positive, rounding-safe threshold used to partition all possible
subset-sum cardinalities into consecutive bins. -/
noncomputable def positiveDyadicThreshold
    (A : Finset ℤ) (deletionBudget h : ℕ) : ℕ :=
  dyadicThreshold A deletionBudget h + 1

theorem positiveDyadicThreshold_pos
    (A : Finset ℤ) (deletionBudget h : ℕ) :
    0 < positiveDyadicThreshold A deletionBudget h := by
  simp [positiveDyadicThreshold]

/-- The minimizing cardinality is at most twice the positive rounded
threshold. -/
theorem minimumMultifoldCardinality_le_two_mul_positiveDyadicThreshold
    (A : Finset ℤ) (deletionBudget h : ℕ) :
    minimumMultifoldCardinality A deletionBudget (2 ^ h) ≤
      2 * positiveDyadicThreshold A deletionBudget h := by
  simp only [positiveDyadicThreshold, dyadicThreshold, foldThreshold]
  omega

/-- Source-threshold form of the high-fold input to the greedy growth
engine. -/
theorem dyadicHighFold_of_card_sums_le_threshold {A : Finset ℤ}
    {j deletionBudget h : ℕ} (hj : j ≤ A.card)
    (hbudget : j ≤ deletionBudget)
    (hsums : (sums A j).card ≤ dyadicThreshold A deletionBudget h) :
    2 * (sums A j).card ≤
      (multifoldSumset (2 ^ h) (insert 0 (available A j))).card := by
  exact highFold_of_card_sums_le_foldThreshold hj hbudget hsums

/-- Strict upper-bin membership for the positive threshold is exactly what
is needed to activate the high-fold estimate. -/
theorem dyadicHighFold_of_card_sums_lt_positiveThreshold {A : Finset ℤ}
    {j deletionBudget h : ℕ} (hj : j ≤ A.card)
    (hbudget : j ≤ deletionBudget)
    (hsums : (sums A j).card <
      positiveDyadicThreshold A deletionBudget h) :
    2 * (sums A j).card ≤
      (multifoldSumset (2 ^ h) (insert 0 (available A j))).card := by
  apply dyadicHighFold_of_card_sums_le_threshold hj hbudget
  simpa [positiveDyadicThreshold] using hsums

/-! ## Threshold-bin residence time -/

/-- Telescoping form of the elementary residence-time argument.  If a
nondecreasing natural-valued process has current value at least `lower` and
each current value is at most `q` times its increment, then a run of `r`
steps consumes at least `r * lower` units of the available `q`-weighted
growth.

This formulation avoids logarithms and rounding.  When consecutive
thresholds have bounded ratio it gives the same `O(q)` bound per bin that
is used on pages 24--25 of CFP. -/
theorem threshold_run_accumulation
    (c : ℕ → ℕ) (p r lower q : ℕ)
    (hmono : ∀ i < r, c (p + i) ≤ c (p + i + 1))
    (hlower : ∀ i < r, lower ≤ c (p + i))
    (hgrowth : ∀ i < r,
      c (p + i) ≤ q * (c (p + i + 1) - c (p + i))) :
    r * lower + q * c p ≤ q * c (p + r) := by
  induction r with
  | zero => simp
  | succ r ih =>
      have ih' := ih
        (fun i hi ↦ hmono i (hi.trans (Nat.lt_succ_self r)))
        (fun i hi ↦ hlower i (hi.trans (Nat.lt_succ_self r)))
        (fun i hi ↦ hgrowth i (hi.trans (Nat.lt_succ_self r)))
      have hstepMono := hmono r (Nat.lt_succ_self r)
      have hstepGrowth := hgrowth r (Nat.lt_succ_self r)
      have hstepLower := hlower r (Nat.lt_succ_self r)
      have hlowerIncrement :
          lower ≤ q * (c (p + r + 1) - c (p + r)) :=
        hstepLower.trans hstepGrowth
      calc
        (r + 1) * lower + q * c p =
            (r * lower + q * c p) + lower := by ring
        _ ≤ q * c (p + r) + lower := Nat.add_le_add_right ih' _
        _ ≤ q * c (p + r) +
            q * (c (p + r + 1) - c (p + r)) :=
          Nat.add_le_add_left hlowerIncrement _
        _ = q * c (p + (r + 1)) := by
          rw [← Nat.mul_add, Nat.add_sub_of_le hstepMono]
          congr 2

/-- A complete threshold-bin bound for a consecutive run.  In addition to
the hypotheses of `threshold_run_accumulation`, suppose one step grows by
at most a factor of two and all pre-step values lie below `upper`.  Then
the number `r` of steps spent in the half-open bin `[lower, upper)` satisfies
the exact estimate

`r * lower < 2 * q * upper`.
-/
theorem threshold_run_length_bound
    (c : ℕ → ℕ) (p r lower upper q : ℕ)
    (hr : 0 < r) (hq : 0 < q)
    (hmono : ∀ i < r, c (p + i) ≤ c (p + i + 1))
    (hdouble : ∀ i < r, c (p + i + 1) ≤ 2 * c (p + i))
    (hlower : ∀ i < r, lower ≤ c (p + i))
    (hupper : ∀ i < r, c (p + i) < upper)
    (hgrowth : ∀ i < r,
      c (p + i) ≤ q * (c (p + i + 1) - c (p + i))) :
    r * lower < 2 * q * upper := by
  have hacc := threshold_run_accumulation c p r lower q hmono hlower hgrowth
  have hrpred : r - 1 < r := Nat.sub_lt (by omega) (by omega)
  have hlastDouble := hdouble (r - 1) hrpred
  have hlastUpper := hupper (r - 1) hrpred
  have hindex : p + (r - 1) + 1 = p + r := by omega
  rw [hindex] at hlastDouble
  have hend : c (p + r) < 2 * upper :=
    hlastDouble.trans_lt ((Nat.mul_lt_mul_left (by omega)).mpr hlastUpper)
  have hqend : q * c (p + r) < q * (2 * upper) :=
    (Nat.mul_lt_mul_left hq).mpr hend
  calc
    r * lower ≤ r * lower + q * c p := Nat.le_add_right _ _
    _ ≤ q * c (p + r) := hacc
    _ < q * (2 * upper) := hqend
    _ = 2 * q * upper := by ring

/-- Threshold-bin residence for the actual greedy subset-sum process.
The high-fold hypothesis is the explicit abstract input which later follows
from stability and the `h`-dimension estimates. -/
theorem greedy_threshold_run_length_bound
    {A : Finset ℤ} {p r h lower upper : ℕ}
    (hr : 0 < r) (hsteps : p + r ≤ A.card)
    (hlower : ∀ i < r, lower ≤ (sums A (p + i)).card)
    (hupper : ∀ i < r, (sums A (p + i)).card < upper)
    (hfold : ∀ i < r,
      2 * (sums A (p + i)).card ≤
        (multifoldSumset (2 ^ h)
          (insert 0 (available A (p + i)))).card) :
    r * lower < 2 * (2 ^ (h + 1)) * upper := by
  apply threshold_run_length_bound
    (fun j ↦ (sums A j).card) p r lower upper (2 ^ (h + 1)) hr
    (pow_pos (by decide) _)
  · intro i hi
    exact Finset.card_le_card (sums_mono_step (by omega))
  · intro i hi
    exact card_sums_succ_le_two_mul (by omega)
  · exact hlower
  · exact hupper
  · intro i hi
    have hgrowth := card_sums_le_two_mul_mul_increment
      (A := A) (j := p + i) (k := 2 ^ h) (by omega) (hfold i hi)
    simpa [pow_succ, mul_comm, mul_left_comm, mul_assoc] using hgrowth

/-- Residence-time bound with the high-fold premise discharged by the
actual source minimum `dyadicThreshold`.  This is the first concrete
post-stability input to the greedy argument: it only asks that the run stay
below `t_h` and that its deletions remain within the threshold budget. -/
theorem greedy_threshold_run_length_bound_of_dyadicThreshold
    {A : Finset ℤ} {p r h deletionBudget lower : ℕ}
    (hr : 0 < r) (hsteps : p + r ≤ A.card)
    (hbudget : p + r ≤ deletionBudget)
    (hlower : ∀ i < r, lower ≤ (sums A (p + i)).card)
    (hupper : ∀ i < r,
      (sums A (p + i)).card <
        positiveDyadicThreshold A deletionBudget h) :
    r * lower <
      2 * (2 ^ (h + 1)) *
        positiveDyadicThreshold A deletionBudget h := by
  apply greedy_threshold_run_length_bound hr hsteps hlower hupper
  intro i hi
  apply dyadicHighFold_of_card_sums_lt_positiveThreshold
    (j := p + i) (deletionBudget := deletionBudget) (h := h)
  · omega
  · omega
  · exact hupper i hi

/-- If the upper endpoint of a threshold bin is at most `ratio` times its
positive lower endpoint, the preceding run estimate turns into a bound
which is independent of the threshold values themselves. -/
theorem greedy_threshold_run_length_le_of_ratio
    {A : Finset ℤ} {p r h lower upper ratio : ℕ}
    (hr : 0 < r) (hsteps : p + r ≤ A.card) (hlowerPos : 0 < lower)
    (hratio : upper ≤ ratio * lower)
    (hlower : ∀ i < r, lower ≤ (sums A (p + i)).card)
    (hupper : ∀ i < r, (sums A (p + i)).card < upper)
    (hfold : ∀ i < r,
      2 * (sums A (p + i)).card ≤
        (multifoldSumset (2 ^ h)
          (insert 0 (available A (p + i)))).card) :
    r ≤ 4 * ratio * 2 ^ h := by
  have hrun := greedy_threshold_run_length_bound hr hsteps
    hlower hupper hfold
  have hscaled :
      r * lower < (4 * ratio * 2 ^ h) * lower := by
    calc
      r * lower < 2 * (2 ^ (h + 1)) * upper := hrun
      _ ≤ 2 * (2 ^ (h + 1)) * (ratio * lower) :=
        Nat.mul_le_mul_left (2 * 2 ^ (h + 1)) hratio
      _ = (4 * ratio * 2 ^ h) * lower := by rw [pow_succ]; ring
  exact (Nat.le_of_lt ((Nat.mul_lt_mul_right hlowerPos).mp hscaled))

/-- The exact geometric sum used when the threshold-bin bounds are added. -/
theorem sum_range_two_pow (n : ℕ) :
    (∑ h ∈ Finset.range n, 2 ^ h) = 2 ^ n - 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih, pow_succ]
      have hpow : 0 < 2 ^ n := pow_pos (by decide) _
      omega

/-- Summing a geometric bound for the lengths of all bins. -/
theorem sum_bin_lengths_le
    {terminalLevel K : ℕ} (binLength : ℕ → ℕ)
    (hbin : ∀ h ≤ terminalLevel, binLength h ≤ K * 2 ^ h) :
    (∑ h ∈ Finset.range (terminalLevel + 1), binLength h) ≤
      K * (2 ^ (terminalLevel + 1) - 1) := by
  calc
    (∑ h ∈ Finset.range (terminalLevel + 1), binLength h) ≤
        ∑ h ∈ Finset.range (terminalLevel + 1), K * 2 ^ h := by
      exact Finset.sum_le_sum fun h hh ↦
        hbin h (Nat.le_of_lt_succ (Finset.mem_range.mp hh))
    _ = K * (∑ h ∈ Finset.range (terminalLevel + 1), 2 ^ h) := by
      rw [Finset.mul_sum]
    _ = K * (2 ^ (terminalLevel + 1) - 1) := by
      rw [sum_range_two_pow]

/-- The complete abstract dyadic-threshold engine for the greedy process.

The functions `binStart` and `binLength` give a consecutive block of steps
for every threshold bin.  `hcover` says that these blocks account for all
steps.  The two analytic inputs are completely explicit:

* `hratio` uniformly bounds consecutive thresholds; and
* `hfold` supplies the required `2^h`-fold sumset growth throughout bin `h`.

In the source proof, these are the conclusions supplied by CFP Lemma 2.31
(stability under deletion) together with the bounding-box estimates and
rank bound in CFP Lemma 2.26.  Thus this theorem is the conditional
finite/numerical part of the CFP argument; it is not, by itself, the full
unconditional conclusion of Theorem 1.5.

Under these assumptions the terminal dyadic scale is linear in the number
of greedy selections, up to the displayed constant:
`steps ≤ 8 * ratio * 2^terminalLevel`.
-/
theorem greedy_final_dyadic_scale_lower_bound
    {A : Finset ℤ} {steps terminalLevel ratio : ℕ}
    (threshold binStart binLength : ℕ → ℕ)
    (hsteps : steps ≤ A.card)
    (hcover : steps =
      ∑ h ∈ Finset.range (terminalLevel + 1), binLength h)
    (hblocks : ∀ h ≤ terminalLevel,
      binStart h + binLength h ≤ steps)
    (hthresholdPos : ∀ h ≤ terminalLevel, 0 < threshold h)
    (hratio : ∀ h ≤ terminalLevel,
      threshold (h + 1) ≤ ratio * threshold h)
    (hbin : ∀ h ≤ terminalLevel, ∀ i < binLength h,
      threshold h ≤ (sums A (binStart h + i)).card ∧
        (sums A (binStart h + i)).card < threshold (h + 1))
    (hfold : ∀ h ≤ terminalLevel, ∀ i < binLength h,
      2 * (sums A (binStart h + i)).card ≤
        (multifoldSumset (2 ^ h)
          (insert 0 (available A (binStart h + i)))).card) :
    steps ≤ 8 * ratio * 2 ^ terminalLevel := by
  have hlength : ∀ h ≤ terminalLevel,
      binLength h ≤ (4 * ratio) * 2 ^ h := by
    intro h hh
    by_cases hz : binLength h = 0
    · simp [hz]
    · have hpos : 0 < binLength h := Nat.pos_of_ne_zero hz
      apply greedy_threshold_run_length_le_of_ratio hpos
        ((hblocks h hh).trans hsteps) (hthresholdPos h hh) (hratio h hh)
      · intro i hi
        exact (hbin h hh i hi).1
      · intro i hi
        exact (hbin h hh i hi).2
      · intro i hi
        exact hfold h hh i hi
  have htotal : steps ≤
      (4 * ratio) * (2 ^ (terminalLevel + 1) - 1) := by
    rw [hcover]
    exact sum_bin_lengths_le binLength hlength
  calc
    steps ≤ (4 * ratio) * (2 ^ (terminalLevel + 1) - 1) := htotal
    _ ≤ (4 * ratio) * 2 ^ (terminalLevel + 1) :=
      Nat.mul_le_mul_left (4 * ratio) (Nat.sub_le _ _)
    _ = 8 * ratio * 2 ^ terminalLevel := by rw [pow_succ]; ring

/-! ## Final abstract numerical extraction -/

/-- The final arithmetic extraction in the CFP scale argument.  The first
hypothesis is what threshold-bin counting supplies: `steps` is at most one
unit per occupied scale plus a geometric contribution.  If the scale-index
overhead is at most half the run, the terminal dyadic scale is at least a
fixed fraction of the number of greedy steps.

All constants and rounding are explicit.  In applications, `K` packages
the uniform ratio bound between consecutive thresholds and the structural
constants from the high-fold sumset estimates. -/
theorem final_dyadic_scale_lower_bound
    {steps terminalLevel K : ℕ}
    (hcount : steps ≤
      (terminalLevel + 1) + K * (2 ^ (terminalLevel + 1) - 1))
    (hoverhead : 2 * (terminalLevel + 1) ≤ steps) :
    steps ≤ 4 * K * 2 ^ terminalLevel := by
  have hcount' : steps ≤
      (terminalLevel + 1) + K * 2 ^ (terminalLevel + 1) := by
    exact hcount.trans (Nat.add_le_add_left
      (Nat.mul_le_mul_left K (Nat.sub_le _ _)) _)
  have hmain : steps ≤ 2 * (K * 2 ^ (terminalLevel + 1)) := by
    omega
  calc
    steps ≤ 2 * (K * 2 ^ (terminalLevel + 1)) := hmain
    _ = 4 * K * 2 ^ terminalLevel := by rw [pow_succ]; ring

end Erdos186.CFP.Greedy
