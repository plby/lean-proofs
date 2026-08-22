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

import ErdosProblems.Erdos1165.Markov
import ErdosProblems.Erdos1165.LazyDecomposition

/-!
# The external two-step chain in the HLOZ deletion

The deletion in `LazyDecomposition` groups the canonical simple-random-walk
increments into disjoint pairs.  Of the sixteen possible ordered pairs, one
(`e₁,-e₁` in the even orientation and `-e₁,e₁` in the shifted orientation) is
removed.  This file connects that pathwise deletion to the IID product law.

We prove directly from `fairSteps_iIndep` that each paired block has mass
`1/16`, different paired blocks are independent, the probability of retaining
a block is `15/16`, and the conditional law of a retained block is uniform on
the fifteen possibilities.  The external block product measure therefore has
exactly the finite-dimensional law supplied by the insertion calculation in
`PathInsertion`.

Finally, the displacement law is enumerated without an asymptotic theorem.  It
has mean zero and covariance `(16/15) I₂`, the constant used by HLOZ before
their local central limit estimate (2.19), reproduced as estimate (7.4) in
`tex/1165.tex`.  That local central limit theorem and its return-probability
error term are not consequences of the finite computations proved here.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace Erdos1165.ExternalWalk

open LazyDecomposition

/-! ## The sixteen two-step blocks -/

/-- A block consists of two consecutive random-walk directions. -/
abbrev Block := Direction × Direction

/-- The unique ordered block erased in the selected orientation. -/
def removableBlock : Orientation → Block
  | .even => (0, 1)
  | .shifted => (1, 0)

/-- Position after the first increment of a block based at `x`. -/
def blockMiddle (x : Point) (b : Block) : Point := x + directionVector b.1

/-- Position after both increments of a block based at `x`. -/
def blockEnd (x : Point) (b : Block) : Point :=
  x + directionVector b.1 + directionVector b.2

/-- The increment-block formulation agrees with pathwise removability. -/
theorem removable_block_iff (o : Orientation) (x : Point) (b : Block) :
    Removable o x (blockMiddle x b) (blockEnd x b) ↔ b = removableBlock o := by
  rcases x with ⟨x₁, x₂⟩
  rcases b with ⟨d₁, d₂⟩
  cases o <;> fin_cases d₁ <;> fin_cases d₂ <;>
    norm_num [Removable, excursionMiddle, removableBlock, blockMiddle, blockEnd,
      directionVector, e₁, Prod.ext_iff] <;> omega

/-- The fifteen blocks retained by deletion. -/
abbrev RetainedBlock (o : Orientation) := {b : Block // b ≠ removableBlock o}

@[simp] theorem card_retainedBlock (o : Orientation) :
    Fintype.card (RetainedBlock o) = 15 := by
  cases o <;> decide

/-! ## IID two-step blocks of the canonical walk -/

/-- The ordered pair of directions used in deletion block `k`. -/
def pairedBlock (k : ℕ) (ω : StepPath) : Block :=
  (ω (2 * k), ω (2 * k + 1))

lemma measurable_pairedBlock (k : ℕ) : Measurable (pairedBlock k) := by
  change Measurable fun ω : StepPath ↦ (ω (2 * k), ω (2 * k + 1))
  exact Measurable.prod (measurable_pi_apply _) (measurable_pi_apply _)

private lemma fairSteps_coordinate_mass (n : ℕ) (d : Direction) :
    fairSteps {ω | ω n = d} = 1 / 4 := by
  calc
    fairSteps {ω | ω n = d} = (fairSteps.map (fun ω : StepPath ↦ ω n)) {d} := by
      rw [Measure.map_apply (by fun_prop) (measurableSet_singleton d)]
      rfl
    _ = fairStep {d} := by rw [fairSteps_map_eval]
    _ = 1 / 4 := fairStep_singleton d

/-- Every ordered two-step block has probability `1/16`. -/
theorem pairedBlock_mass (k : ℕ) (b : Block) :
    fairSteps {ω | pairedBlock k ω = b} = 1 / 16 := by
  rcases b with ⟨d₀, d₁⟩
  have hind := fairSteps_iIndep.indepFun (show 2 * k ≠ 2 * k + 1 by omega)
  have h := hind.measure_inter_preimage_eq_mul ({d₀} : Set Direction) ({d₁} : Set Direction)
    (measurableSet_singleton d₀) (measurableSet_singleton d₁)
  rw [show (fun ω : StepPath ↦ ω (2 * k)) ⁻¹' {d₀} = {ω | ω (2 * k) = d₀} by ext; simp,
    show (fun ω : StepPath ↦ ω (2 * k + 1)) ⁻¹' {d₁} =
      {ω | ω (2 * k + 1) = d₁} by ext; simp,
    fairSteps_coordinate_mass, fairSteps_coordinate_mass] at h
  rw [show {ω | pairedBlock k ω = (d₀, d₁)} =
      {ω | ω (2 * k) = d₀} ∩ {ω | ω (2 * k + 1) = d₁} by
        ext ω; simp [pairedBlock]]
  calc
    fairSteps ({ω | ω (2 * k) = d₀} ∩ {ω | ω (2 * k + 1) = d₁}) =
        1 / 4 * (1 / 4) := h
    _ = 1 / 16 := by
      apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
      norm_num

/-- Different disjoint paired blocks are independent. -/
theorem pairedBlock_indep {k l : ℕ} (hkl : k ≠ l) :
    IndepFun (pairedBlock k) (pairedBlock l) fairSteps := by
  apply fairSteps_iIndep.indepFun_prodMk_prodMk (fun _ ↦ measurable_pi_apply _)
  all_goals omega

/-- A block is retained exactly when the corresponding three-point path is
not removable by `LazyDecomposition`. -/
theorem retained_iff_not_removable (o : Orientation) (k : ℕ) (ω : StepPath) (x : Point) :
    pairedBlock k ω ≠ removableBlock o ↔
      ¬ Removable o x (blockMiddle x (pairedBlock k ω)) (blockEnd x (pairedBlock k ω)) := by
  rw [removable_block_iff]

/-- On a single block, `LazyDecomposition.externalPath` deletes exactly the
special ordered pair and retains every other ordered pair. -/
theorem externalPath_single_block (o : Orientation) (x : Point) (b : Block) :
    externalPath o [x, blockMiddle x b, blockEnd x b] =
      if b = removableBlock o then [x] else [x, blockMiddle x b, blockEnd x b] := by
  by_cases h : b = removableBlock o
  · subst b
    have hr : Removable o x (blockMiddle x (removableBlock o))
        (blockEnd x (removableBlock o)) :=
      (removable_block_iff o x (removableBlock o)).2 rfl
    simp [externalPath, compressTail, hr]
  · have hr : ¬ Removable o x (blockMiddle x b) (blockEnd x b) :=
      fun hb ↦ h ((removable_block_iff o x b).1 hb)
    simp [externalPath, compressTail, h, hr]

lemma measurableSet_retained (o : Orientation) (k : ℕ) :
    MeasurableSet {ω | pairedBlock k ω ≠ removableBlock o} := by
  have heq : MeasurableSet {ω | pairedBlock k ω = removableBlock o} :=
    (measurableSet_singleton _).preimage (measurable_pairedBlock k)
  exact heq.compl

/-- A two-step block survives deletion with probability `15/16`. -/
theorem retained_probability (o : Orientation) (k : ℕ) :
    fairSteps {ω | pairedBlock k ω ≠ removableBlock o} = 15 / 16 := by
  have hcomp : {ω | pairedBlock k ω ≠ removableBlock o} =
      {ω | pairedBlock k ω = removableBlock o}ᶜ := by ext; simp
  have heq : MeasurableSet {ω | pairedBlock k ω = removableBlock o} :=
    (measurableSet_singleton _).preimage (measurable_pairedBlock k)
  rw [hcomp, measure_compl heq, measure_univ, pairedBlock_mass]
  · apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    rw [ENNReal.toReal_sub_of_le] <;> norm_num
  · exact (measure_lt_top fairSteps _).ne

/-- Conditional on survival, each of the fifteen retained ordered blocks has
probability `1/15`.  The quotient is the elementary conditional probability;
no regular conditional distribution is assumed. -/
theorem conditional_retained_block (o : Orientation) (k : ℕ) (b : RetainedBlock o) :
    fairSteps {ω | pairedBlock k ω = (b : Block)} /
        fairSteps {ω | pairedBlock k ω ≠ removableBlock o} = 1 / 15 := by
  rw [pairedBlock_mass, retained_probability]
  apply (ENNReal.toReal_eq_toReal_iff'
    (ENNReal.div_ne_top (by finiteness) (by norm_num)) (by finiteness)).mp
  norm_num

/-! ## The retained-block product law -/

/-- The common conditional law of a retained two-step block. -/
noncomputable def retainedBlockLaw (o : Orientation) : Measure (RetainedBlock o) :=
  ProbabilityTheory.uniformOn Set.univ

noncomputable instance (o : Orientation) : Nonempty (RetainedBlock o) :=
  Fintype.card_pos_iff.mp (by rw [card_retainedBlock]; norm_num)

noncomputable instance (o : Orientation) : IsProbabilityMeasure (retainedBlockLaw o) := by
  unfold retainedBlockLaw
  infer_instance

@[simp] theorem retainedBlockLaw_singleton (o : Orientation) (b : RetainedBlock o) :
    retainedBlockLaw o {b} = 1 / 15 := by
  rw [retainedBlockLaw, uniformOn_univ]
  simp

/-- The IID law of the external retained blocks. -/
noncomputable def externalBlocks (o : Orientation) : Measure (ℕ → RetainedBlock o) :=
  Measure.infinitePi fun _ : ℕ ↦ retainedBlockLaw o

noncomputable instance (o : Orientation) : IsProbabilityMeasure (externalBlocks o) := by
  unfold externalBlocks
  infer_instance

theorem externalBlocks_map_eval (o : Orientation) (n : ℕ) :
    (externalBlocks o).map (fun η ↦ η n) = retainedBlockLaw o := by
  exact Measure.infinitePi_map_eval (fun _ : ℕ ↦ retainedBlockLaw o) n

/-- The first `n` retained blocks. -/
def externalBlockPrefix (n : ℕ) (η : ℕ → RetainedBlock o) : Fin n → RetainedBlock o :=
  fun j ↦ η j

lemma measurable_externalBlockPrefix (o : Orientation) (n : ℕ) :
    Measurable (externalBlockPrefix (o := o) n) := by
  exact measurable_pi_lambda _ fun j ↦ measurable_pi_apply (j : ℕ)

theorem externalBlocks_map_prefix (o : Orientation) (n : ℕ) :
    (externalBlocks o).map (externalBlockPrefix (o := o) n) =
      Measure.infinitePi fun _ : Fin n ↦ retainedBlockLaw o := by
  unfold externalBlocks externalBlockPrefix
  exact Measure.map_infinitePi_infinitePi_of_inj
    (P := fun _ : ℕ ↦ retainedBlockLaw o) (f := fun j : Fin n ↦ (j : ℕ))
      Fin.val_injective

/-- Exact finite-dimensional cylinder probability for the external blocks. -/
theorem externalBlockPrefix_mass (o : Orientation) (n : ℕ)
    (w : Fin n → RetainedBlock o) :
    externalBlocks o {η | externalBlockPrefix (o := o) n η = w} = (1 / 15) ^ n := by
  calc
    externalBlocks o {η | externalBlockPrefix (o := o) n η = w} =
        ((externalBlocks o).map (externalBlockPrefix (o := o) n)) {w} := by
      rw [Measure.map_apply (measurable_externalBlockPrefix o n) (measurableSet_singleton w)]
      rfl
    _ = (Measure.infinitePi fun _ : Fin n ↦ retainedBlockLaw o) {w} := by
      rw [externalBlocks_map_prefix]
    _ = ∏ j : Fin n, retainedBlockLaw o {w j} := by
      rw [Measure.infinitePi_singleton_of_fintype]
    _ = (1 / 15) ^ n := by
      simp [retainedBlockLaw_singleton]

/-- All retained blocks of the external chain are mutually independent. -/
theorem externalBlocks_independent (o : Orientation) :
    iIndepFun (fun n (η : ℕ → RetainedBlock o) ↦ η n) (externalBlocks o) := by
  exact iIndepFun_infinitePi (P := fun _ : ℕ ↦ retainedBlockLaw o) fun _ ↦ measurable_id

/-! ## External displacements and transition law -/

/-- The displacement across an ordered two-step block. -/
def blockDisplacement (b : Block) : Point :=
  directionVector b.1 + directionVector b.2

/-- The displacement of one retained external block. -/
def retainedDisplacement (o : Orientation) (b : RetainedBlock o) : Point :=
  blockDisplacement b

lemma measurable_retainedDisplacement (o : Orientation) :
    Measurable (retainedDisplacement o) := measurable_of_countable _

/-- The one-step increment law of the even-time external Markov chain. -/
noncomputable def externalIncrementLaw (o : Orientation) : Measure Point :=
  (retainedBlockLaw o).map (retainedDisplacement o)

noncomputable instance (o : Orientation) : IsProbabilityMeasure (externalIncrementLaw o) := by
  unfold externalIncrementLaw
  exact Measure.isProbabilityMeasure_map (measurable_retainedDisplacement o).aemeasurable

/-- Number of retained ordered blocks having displacement `z`. -/
def displacementMultiplicity (o : Orientation) (z : Point) : ℕ :=
  ((Finset.univ : Finset (RetainedBlock o)).filter
    fun b ↦ retainedDisplacement o b = z).card

/-- Exact transition mass: multiplicity among the fifteen retained ordered
blocks, divided by fifteen. -/
theorem externalIncrementLaw_singleton (o : Orientation) (z : Point) :
    externalIncrementLaw o {z} = displacementMultiplicity o z / 15 := by
  rw [externalIncrementLaw, Measure.map_apply (measurable_retainedDisplacement o)
    (measurableSet_singleton z), retainedBlockLaw, uniformOn_univ]
  have hset : retainedDisplacement o ⁻¹' {z} =
      ↑((Finset.univ : Finset (RetainedBlock o)).filter
        fun b ↦ retainedDisplacement o b = z) := by
    ext b
    simp
  rw [hset, Measure.count_apply_finset]
  simp [displacementMultiplicity]

/-- The four nonzero axial displacements of a two-step walk. -/
def axialDisplacements : Finset Point :=
  {(2, 0), (-2, 0), (0, 2), (0, -2)}

/-- The four diagonal displacements of a two-step walk. -/
def diagonalDisplacements : Finset Point :=
  {(1, 1), (1, -1), (-1, 1), (-1, -1)}

/-- Complete support of the external increment law. -/
def externalIncrementSupport : Finset Point :=
  insert (0, 0) (axialDisplacements ∪ diagonalDisplacements)

lemma blockDisplacement_mem_support (b : Block) :
    blockDisplacement b ∈ externalIncrementSupport := by
  rcases b with ⟨d₀, d₁⟩
  fin_cases d₀ <;> fin_cases d₁ <;>
    simp [externalIncrementSupport, axialDisplacements, diagonalDisplacements,
      blockDisplacement, directionVector]

@[simp] theorem displacementMultiplicity_zero (o : Orientation) :
    displacementMultiplicity o (0, 0) = 3 := by
  cases o <;> decide

theorem displacementMultiplicity_axial (o : Orientation) {z : Point}
    (hz : z ∈ axialDisplacements) : displacementMultiplicity o z = 1 := by
  simp only [axialDisplacements, Finset.mem_insert, Finset.mem_singleton] at hz
  rcases hz with h | h | h | h <;> subst z <;> cases o <;> decide

theorem displacementMultiplicity_diagonal (o : Orientation) {z : Point}
    (hz : z ∈ diagonalDisplacements) : displacementMultiplicity o z = 2 := by
  simp only [diagonalDisplacements, Finset.mem_insert, Finset.mem_singleton] at hz
  rcases hz with h | h | h | h <;> subst z <;> cases o <;> decide

theorem displacementMultiplicity_eq_zero_of_notMem (o : Orientation) {z : Point}
    (hz : z ∉ externalIncrementSupport) : displacementMultiplicity o z = 0 := by
  rw [displacementMultiplicity, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro b _ hb
  apply hz
  rw [← hb]
  exact blockDisplacement_mem_support b

/-- The external transition kernel, from a current even-time state `x`. -/
noncomputable def externalTransitionLaw (o : Orientation) (x : Point) : Measure Point :=
  (externalIncrementLaw o).map fun z ↦ x + z

noncomputable instance (o : Orientation) (x : Point) :
    IsProbabilityMeasure (externalTransitionLaw o x) := by
  unfold externalTransitionLaw
  exact Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable

/-- Exact state-to-state transition law.  Combined with
`displacementMultiplicity_zero`, `displacementMultiplicity_axial`,
`displacementMultiplicity_diagonal`, and
`displacementMultiplicity_eq_zero_of_notMem`, this gives respectively the
probabilities `3/15`, `1/15`, `2/15`, and `0`. -/
theorem externalTransitionLaw_singleton (o : Orientation) (x y : Point) :
    externalTransitionLaw o x {y} = displacementMultiplicity o (y - x) / 15 := by
  rw [externalTransitionLaw, Measure.map_apply (measurable_of_countable _)
    (measurableSet_singleton y)]
  have hpre : (fun z : Point ↦ x + z) ⁻¹' {y} = {y - x} := by
    ext z
    simp only [mem_preimage, mem_singleton_iff]
    constructor <;> intro h
    · apply (eq_sub_iff_add_eq).2
      simpa [add_comm] using h
    · rw [h]
      abel
  rw [hpre, externalIncrementLaw_singleton]

@[simp] theorem externalTransitionLaw_self (o : Orientation) (x : Point) :
    externalTransitionLaw o x {x} = (3 : ENNReal) / 15 := by
  rw [externalTransitionLaw_singleton]
  rw [sub_self]
  have hm : displacementMultiplicity o (0 : Point) = 3 := by
    change displacementMultiplicity o (0, 0) = 3
    exact displacementMultiplicity_zero o
  rw [hm]
  congr 1

theorem externalTransitionLaw_axial (o : Orientation) {x y : Point}
    (hxy : y - x ∈ axialDisplacements) :
    externalTransitionLaw o x {y} = (1 : ENNReal) / 15 := by
  rw [externalTransitionLaw_singleton, displacementMultiplicity_axial o hxy]
  congr 1
  norm_num

theorem externalTransitionLaw_diagonal (o : Orientation) {x y : Point}
    (hxy : y - x ∈ diagonalDisplacements) :
    externalTransitionLaw o x {y} = (2 : ENNReal) / 15 := by
  rw [externalTransitionLaw_singleton, displacementMultiplicity_diagonal o hxy]
  congr 1

theorem externalTransitionLaw_eq_zero (o : Orientation) {x y : Point}
    (hxy : y - x ∉ externalIncrementSupport) :
    externalTransitionLaw o x {y} = 0 := by
  rw [externalTransitionLaw_singleton,
    displacementMultiplicity_eq_zero_of_notMem o hxy]
  simp

/-- Position of the external chain after `n` retained two-step blocks. -/
def externalPosition (o : Orientation) (η : ℕ → RetainedBlock o) (n : ℕ) : Point :=
  ∑ j ∈ Finset.range n, retainedDisplacement o (η j)

@[simp] theorem externalPosition_zero (o : Orientation) (η : ℕ → RetainedBlock o) :
    externalPosition o η 0 = (0, 0) := by rfl

theorem externalPosition_succ (o : Orientation) (η : ℕ → RetainedBlock o) (n : ℕ) :
    externalPosition o η (n + 1) =
      externalPosition o η n + retainedDisplacement o (η n) := by
  simp [externalPosition, Finset.sum_range_succ]

lemma measurable_externalPosition (o : Orientation) : Measurable (externalPosition o) := by
  apply measurable_pi_lambda
  intro n
  unfold externalPosition
  fun_prop

/-- The law on external-chain trajectories. -/
noncomputable def externalWalkLaw (o : Orientation) : Measure WalkPath :=
  (externalBlocks o).map (externalPosition o)

noncomputable instance (o : Orientation) : IsProbabilityMeasure (externalWalkLaw o) := by
  unfold externalWalkLaw
  exact Measure.isProbabilityMeasure_map (measurable_externalPosition o).aemeasurable

/-- Every external-chain increment has the retained displacement law. -/
theorem external_increment_map (o : Orientation) (n : ℕ) :
    (externalBlocks o).map
        (fun η ↦ externalPosition o η (n + 1) - externalPosition o η n) =
      externalIncrementLaw o := by
  have h := congrArg (fun μ : Measure (RetainedBlock o) ↦
      μ.map (retainedDisplacement o)) (externalBlocks_map_eval o n)
  rw [Measure.map_map (measurable_retainedDisplacement o)
    (measurable_pi_apply n)] at h
  simpa [externalPosition_succ, externalIncrementLaw, add_sub_cancel_left,
    Function.comp_def] using h

/-- External increments are mutually independent, not merely pairwise
independent. -/
theorem external_increments_independent (o : Orientation) :
    iIndepFun
      (fun n (η : ℕ → RetainedBlock o) ↦
        externalPosition o η (n + 1) - externalPosition o η n)
      (externalBlocks o) := by
  have h := (externalBlocks_independent o).comp
    (fun _ ↦ retainedDisplacement o) (fun _ ↦ measurable_retainedDisplacement o)
  simpa [externalPosition_succ, add_sub_cancel_left, Function.comp_def] using h

/-! ## Exact first and second moments -/

private theorem sum_retainedBlock (o : Orientation) (f : Block → ℝ) :
    (∑ b : RetainedBlock o, f b) =
      ∑ b : Block, if b ≠ removableBlock o then f b else 0 := by
  rw [← Finset.sum_subtype
    ((Finset.univ : Finset Block).filter fun b ↦ b ≠ removableBlock o)
    (by simp) f]
  rw [Finset.sum_filter]

/-- A real coordinate of an integer lattice displacement. -/
def displacementCoordinate : Fin 2 → Point → ℝ
  | ⟨0, _⟩, z => z.1
  | ⟨1, _⟩, z => z.2

/-- Coordinatewise mean of one external increment, written as a finite average
over its fifteen equiprobable ordered blocks. -/
noncomputable def externalMean (o : Orientation) (i : Fin 2) : ℝ :=
  (∑ b : RetainedBlock o, displacementCoordinate i (retainedDisplacement o b)) / 15

/-- Coordinatewise second moment.  Since the mean is zero, this is also the
covariance matrix. -/
noncomputable def externalCovariance (o : Orientation) (i j : Fin 2) : ℝ :=
  (∑ b : RetainedBlock o,
      displacementCoordinate i (retainedDisplacement o b) *
        displacementCoordinate j (retainedDisplacement o b)) / 15

/-- Each external increment is centered. -/
theorem externalMean_eq_zero (o : Orientation) (i : Fin 2) :
    externalMean o i = 0 := by
  unfold externalMean
  simp only [retainedDisplacement]
  rw [sum_retainedBlock o (fun b ↦ displacementCoordinate i (blockDisplacement b))]
  cases o <;> fin_cases i <;> rw [Fintype.sum_prod_type] <;>
    simp only [Fin.sum_univ_four] <;>
    norm_num [displacementCoordinate, retainedDisplacement,
      blockDisplacement, removableBlock, directionVector, Fin.ext_iff]

/-- The exact covariance computation quoted by HLOZ:
`Cov(ΔS̃) = (16/15) I₂`. -/
theorem externalCovariance_eq (o : Orientation) (i j : Fin 2) :
    externalCovariance o i j = if i = j then 16 / 15 else 0 := by
  unfold externalCovariance
  simp only [retainedDisplacement]
  rw [sum_retainedBlock o (fun b ↦
    displacementCoordinate i (blockDisplacement b) *
      displacementCoordinate j (blockDisplacement b))]
  cases o <;> fin_cases i <;> fin_cases j <;> rw [Fintype.sum_prod_type] <;>
    simp only [Fin.sum_univ_four] <;>
    norm_num [externalCovariance, displacementCoordinate, retainedDisplacement,
      blockDisplacement, removableBlock, directionVector, Fin.ext_iff]

end Erdos1165.ExternalWalk
