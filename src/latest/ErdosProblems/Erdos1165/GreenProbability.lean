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

import ErdosProblems.Erdos1165.GreenFunction
import ErdosProblems.Erdos1165.PlanarPotential
import ErdosProblems.Erdos1165.Markov
import ErdosProblems.Erdos1165.Recurrence
import ErdosProblems.Erdos1165.ExitTail

/-!
# Probabilistic realization of killed Green functions

The matrix powers in `GreenFunction` are identified here with the canonical
IID-increment construction of planar simple random walk.  We then take the
monotone infinite-horizon limit and prove the exact infinite first-hit/Green
factorization.  All values live in `ENNReal`, so the factorization remains
valid without a finiteness hypothesis; the quotient form is stated when the
diagonal Green function is finite.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal Topology

namespace Erdos1165
namespace GreenProbability

open GreenFunction PlanarPotential
open ExitTail Annulus

/-! ## Finite killed path events -/

/-- Starting from `x`, the path stays in `A` through time `n` and is at `y`
at time `n`. -/
def killedPathEvent (A : Finset Point) (n : ℕ) (x y : Point) : Set StepPath :=
  {ω | (∀ k ≤ n, x + trajectory ω k ∈ A) ∧ x + trajectory ω n = y}

lemma trajectory_from_first_step (x : Point) (ω : StepPath) (k : ℕ) :
    x + trajectory ω (k + 1) =
      (x + directionVector (ω 0)) + trajectory (shiftSteps 1 ω) k := by
  have hshift := trajectory_add_sub_trajectory ω 1 k
  have hone : trajectory ω 1 = directionVector (ω 0) := by
    simpa [show ((0, 0) : Point) = 0 by rfl] using trajectory_succ ω 0
  rw [show 1 + k = k + 1 by omega, hone] at hshift
  rw [← hshift]
  abel

lemma mem_killedPathEvent_succ_iff (A : Finset Point) (n : ℕ)
    (x y : Point) (ω : StepPath) :
    ω ∈ killedPathEvent A (n + 1) x y ↔
      x ∈ A ∧ shiftSteps 1 ω ∈
        killedPathEvent A n (x + directionVector (ω 0)) y := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · simpa [show ((0, 0) : Point) = 0 by rfl] using h.1 0 (Nat.zero_le _)
    · intro k hk
      rw [← trajectory_from_first_step]
      exact h.1 (k + 1) (Nat.succ_le_succ hk)
    · rw [← trajectory_from_first_step]
      exact h.2
  · rintro ⟨hx, htail, hend⟩
    refine ⟨?_, ?_⟩
    · intro k hk
      rcases k with _ | k
      · simpa [show ((0, 0) : Point) = 0 by rfl] using hx
      · rw [trajectory_from_first_step]
        exact htail k (Nat.le_of_succ_le_succ hk)
    · rw [trajectory_from_first_step]
      exact hend

/-- The killed event depends only on the first `n` increments. -/
lemma measurableSet_killedPathEvent_filtration (A : Finset Point) (n : ℕ)
    (x y : Point) :
    MeasurableSet[incrementFiltration n] (killedPathEvent A n x y) := by
  let extend : (Fin n → Direction) → StepPath := fun u j ↦
    if hj : j < n then u ⟨j, hj⟩ else 0
  let C : Set (Fin n → Direction) := {u | extend u ∈ killedPathEvent A n x y}
  have htraj (ω : StepPath) (k : ℕ) (hk : k ≤ n) :
      trajectory (extend (stepPrefix n ω)) k = trajectory ω k := by
    unfold trajectory
    apply Finset.sum_congr rfl
    intro j hj
    have hjn : j < n := (Finset.mem_range.mp hj).trans_le hk
    simp [extend, stepPrefix, hjn]
  have heq : killedPathEvent A n x y = stepPrefix n ⁻¹' C := by
    ext ω
    constructor
    · intro h
      refine ⟨?_, ?_⟩
      · intro k hk
        rw [htraj ω k hk]
        exact h.1 k hk
      · rw [htraj ω n le_rfl]
        exact h.2
    · intro h
      refine ⟨?_, ?_⟩
      · intro k hk
        rw [← htraj ω k hk]
        exact h.1 k hk
      · rw [← htraj ω n le_rfl]
        exact h.2
  rw [incrementFiltration_apply, heq]
  exact ⟨C, (Set.to_countable C).measurableSet, rfl⟩

lemma measurableSet_killedPathEvent (A : Finset Point) (n : ℕ)
    (x y : Point) : MeasurableSet (killedPathEvent A n x y) :=
  incrementFiltration.le n _ (measurableSet_killedPathEvent_filtration A n x y)

private def firstDirectionSet (d : Direction) : Set (Fin 1 → Direction) :=
  {u | u 0 = d}

private lemma firstDirection_preimage (d : Direction) :
    stepPrefix 1 ⁻¹' firstDirectionSet d = {ω : StepPath | ω 0 = d} := by
  ext ω
  simp [firstDirectionSet, stepPrefix]

/-- A first increment and a killed event of the shifted path factor exactly. -/
lemma measure_firstDirection_inter_shift_killedPathEvent
    (A : Finset Point) (n : ℕ) (z y : Point) (d : Direction) :
    fairSteps ({ω : StepPath | ω 0 = d} ∩
        shiftSteps 1 ⁻¹' killedPathEvent A n z y) =
      (1 / 4 : ℝ≥0∞) * fairSteps (killedPathEvent A n z y) := by
  have hfil := measurableSet_killedPathEvent_filtration A n z y
  rw [incrementFiltration_apply] at hfil
  obtain ⟨C, hC, hCeq⟩ := hfil
  have htail : shiftSteps 1 ⁻¹' killedPathEvent A n z y =
      stepBlock 1 n ⁻¹' C := by
    rw [← hCeq]
    rfl
  have hind := (indepFun_stepPrefix_stepBlock 1 n).measure_inter_preimage_eq_mul
    (firstDirectionSet d) C (Set.to_countable _).measurableSet hC
  rw [firstDirection_preimage, ← htail] at hind
  rw [hind]
  have hfirst : fairSteps {ω : StepPath | ω 0 = d} = 1 / 4 := by
    change fairSteps ((fun ω : StepPath ↦ ω 0) ⁻¹' {d}) = 1 / 4
    rw [← Measure.map_apply (measurable_pi_apply 0) (MeasurableSet.singleton d),
      fairSteps_eval, fairStep_singleton]
  have hshift : fairSteps (shiftSteps 1 ⁻¹' killedPathEvent A n z y) =
      fairSteps (killedPathEvent A n z y) := by
    rw [← Measure.map_apply (measurable_shiftSteps 1)
      (measurableSet_killedPathEvent A n z y), fairSteps_map_shiftSteps]
  rw [hfirst, hshift]

private def firstStepPiece (A : Finset Point) (n : ℕ) (x y : Point)
    (d : Direction) : Set StepPath :=
  {ω | ω 0 = d} ∩ shiftSteps 1 ⁻¹'
    killedPathEvent A n (x + directionVector d) y

lemma killedPathEvent_succ_eq_iUnion (A : Finset Point) (n : ℕ)
    {x y : Point} (hx : x ∈ A) :
    killedPathEvent A (n + 1) x y = ⋃ d : Direction, firstStepPiece A n x y d := by
  ext ω
  rw [mem_killedPathEvent_succ_iff]
  simp only [mem_iUnion, firstStepPiece, mem_inter_iff, mem_ofPred_eq, mem_preimage]
  constructor
  · rintro ⟨_, htail⟩
    exact ⟨ω 0, rfl, htail⟩
  · rintro ⟨d, hd, htail⟩
    subst d
    exact ⟨hx, htail⟩

lemma firstStepPiece_pairwise_disjoint (A : Finset Point) (n : ℕ)
    (x y : Point) : Pairwise fun d e : Direction ↦
      Disjoint (firstStepPiece A n x y d) (firstStepPiece A n x y e) := by
  intro d e hde
  rw [Set.disjoint_left]
  intro ω hd he
  exact hde (hd.1.symm.trans he.1)

lemma measurableSet_firstStepPiece (A : Finset Point) (n : ℕ)
    (x y : Point) (d : Direction) : MeasurableSet (firstStepPiece A n x y d) := by
  exact (measurableSet_eq_fun (measurable_pi_apply 0) measurable_const).inter
    ((measurable_shiftSteps 1) (measurableSet_killedPathEvent A n
      (x + directionVector d) y))

lemma measure_killedPathEvent_succ (A : Finset Point) (n : ℕ)
    (x y : Point) :
    fairSteps (killedPathEvent A (n + 1) x y) =
      if x ∈ A then
        ∑ d : Direction, (1 / 4 : ℝ≥0∞) *
          fairSteps (killedPathEvent A n (x + directionVector d) y)
      else 0 := by
  by_cases hx : x ∈ A
  · rw [if_pos hx, killedPathEvent_succ_eq_iUnion A n hx]
    rw [measure_iUnion (firstStepPiece_pairwise_disjoint A n x y)
      (measurableSet_firstStepPiece A n x y)]
    rw [tsum_fintype]
    apply Finset.sum_congr rfl
    intro d hd
    exact measure_firstDirection_inter_shift_killedPathEvent A n
      (x + directionVector d) y d
  · rw [if_neg hx]
    have hempty : killedPathEvent A (n + 1) x y = ∅ := by
      ext ω
      rw [mem_killedPathEvent_succ_iff]
      simp [hx]
    simp [hempty]

/-! ## Identification with the kernel powers -/

lemma sum_planarKernel_mul_of_zero_outside (A : Finset Point) (x : Point)
    (f : Point → ℝ≥0∞) (hf : ∀ z, z ∉ A → f z = 0) :
    (∑ z ∈ A, planarKernel x z * f z) =
      ∑ d : Direction, (1 / 4 : ℝ≥0∞) * f (x + directionVector d) := by
  rw [show (∑ z ∈ A, planarKernel x z * f z) =
      ∑ z ∈ A, (∑ d : Direction,
        if z = x + directionVector d then (4 : ℝ≥0∞)⁻¹ else 0) * f z by
        simp only [planarKernel]]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hmem : x + directionVector d ∈ A
  · rw [Finset.sum_eq_single (x + directionVector d)]
    · simp
    · intro z hz hne
      simp [hne]
    · exact fun h ↦ (h hmem).elim
  · rw [hf _ hmem]
    simp only [mul_zero]
    apply Finset.sum_eq_zero
    intro z hz
    rw [if_neg (by
      intro heq
      apply hmem
      simpa [heq] using hz)]
    simp

theorem fairSteps_killedPathEvent (A : Finset Point) (n : ℕ) (x y : Point) :
    fairSteps (killedPathEvent A n x y) =
      killedPower planarKernel A n x y := by
  induction n generalizing x with
  | zero =>
      by_cases hx : x ∈ A <;> by_cases hxy : x = y
      · subst x
        simp [killedPathEvent, killedPower, hx,
          show ((0, 0) : Point) = 0 by rfl]
      · have hempty : killedPathEvent A 0 x y = ∅ := by
          ext ω
          simp [killedPathEvent, hxy, show ((0, 0) : Point) = 0 by rfl]
        simp [hempty, killedPower, hxy]
      · subst x
        simp [killedPathEvent, killedPower, hx,
          show ((0, 0) : Point) = 0 by rfl]
      · have hempty : killedPathEvent A 0 x y = ∅ := by
          ext ω
          simp [killedPathEvent, hxy, show ((0, 0) : Point) = 0 by rfl]
        simp [hempty, killedPower, hxy]
  | succ n ih =>
      rw [measure_killedPathEvent_succ]
      rw [killedPower_succ]
      by_cases hx : x ∈ A
      · rw [if_pos hx, if_pos hx]
        simp_rw [ih]
        exact (sum_planarKernel_mul_of_zero_outside A x
          (fun z ↦ killedPower planarKernel A n z y)
          (fun z hz ↦ killedPower_eq_zero_of_notMem_left planarKernel A hz n y)).symm
      · simp [hx]

/-! ## Canonical path-space version -/

/-- The canonical path-space event corresponding to `killedPathEvent`. -/
def walkKilledAt (A : Finset Point) (n : ℕ) (y : Point) : Set WalkPath :=
  {s | (∀ k ≤ n, s k ∈ A) ∧ s n = y}

lemma measurableSet_walkKilledAt (A : Finset Point) (n : ℕ) (y : Point) :
    MeasurableSet (walkKilledAt A n y) := by
  unfold walkKilledAt
  measurability

theorem simpleRandomWalkFrom_walkKilledAt (A : Finset Point) (n : ℕ)
    (x y : Point) :
    simpleRandomWalkFrom x (walkKilledAt A n y) =
      killedPower planarKernel A n x y := by
  rw [simpleRandomWalkFrom, Measure.map_apply (measurable_trajectoryFrom x)
    (measurableSet_walkKilledAt A n y)]
  have hpre : trajectoryFrom x ⁻¹' walkKilledAt A n y = killedPathEvent A n x y := by
    rfl
  rw [hpre, fairSteps_killedPathEvent]

/-- Infinite-horizon killed Green function. -/
noncomputable def infiniteGreen (A : Finset Point) (x y : Point) : ℝ≥0∞ :=
  ∑' n, killedPower planarKernel A n x y

/-- Infinite total first-hit mass. -/
noncomputable def infiniteHitMass (A : Finset Point) (x y : Point) : ℝ≥0∞ :=
  ∑' n, firstHitWeight planarKernel A y n x

/-! ## First-hit events -/

/-- The first visit to `y` occurs exactly at time `n`, without leaving `A`
through that time. -/
def firstHitPathEvent (A : Finset Point) (n : ℕ) (x y : Point) : Set StepPath :=
  {ω | ω ∈ killedPathEvent A n x y ∧
    ∀ k < n, x + trajectory ω k ≠ y}

lemma mem_firstHitPathEvent_succ_iff (A : Finset Point) (n : ℕ)
    (x y : Point) (ω : StepPath) :
    ω ∈ firstHitPathEvent A (n + 1) x y ↔
      x ∈ A ∧ x ≠ y ∧ shiftSteps 1 ω ∈
        firstHitPathEvent A n (x + directionVector (ω 0)) y := by
  constructor
  · rintro ⟨hkilled, hfirst⟩
    rw [mem_killedPathEvent_succ_iff] at hkilled
    refine ⟨hkilled.1, ?_, hkilled.2, ?_⟩
    · intro hxy
      apply hfirst 0 (by omega)
      simp [hxy, show ((0, 0) : Point) = 0 by rfl]
    · intro k hk
      rw [← trajectory_from_first_step]
      exact hfirst (k + 1) (Nat.succ_lt_succ hk)
  · rintro ⟨hx, hxy, htailKilled, htailFirst⟩
    refine ⟨(mem_killedPathEvent_succ_iff A n x y ω).2
      ⟨hx, htailKilled⟩, ?_⟩
    intro k hk
    rcases k with _ | k
    · simpa [show ((0, 0) : Point) = 0 by rfl] using hxy
    · rw [trajectory_from_first_step]
      exact htailFirst k (Nat.lt_of_succ_lt_succ hk)

private def extendPrefix {n : ℕ} (u : Fin n → Direction) : StepPath := fun j ↦
  if hj : j < n then u ⟨j, hj⟩ else 0

private lemma trajectory_extendPrefix (ω : StepPath) {k n : ℕ} (hk : k ≤ n) :
    trajectory (extendPrefix (stepPrefix n ω)) k = trajectory ω k := by
  unfold trajectory
  apply Finset.sum_congr rfl
  intro j hj
  have hjn : j < n := (Finset.mem_range.mp hj).trans_le hk
  simp [extendPrefix, stepPrefix, hjn]

lemma measurableSet_firstHitPathEvent_filtration (A : Finset Point) (n : ℕ)
    (x y : Point) :
    MeasurableSet[incrementFiltration n] (firstHitPathEvent A n x y) := by
  let C : Set (Fin n → Direction) :=
    {u | extendPrefix u ∈ firstHitPathEvent A n x y}
  have heq : firstHitPathEvent A n x y = stepPrefix n ⁻¹' C := by
    ext ω
    constructor
    · rintro ⟨hkilled, hfirst⟩
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · intro k hk
        rw [trajectory_extendPrefix ω hk]
        exact hkilled.1 k hk
      · rw [trajectory_extendPrefix ω le_rfl]
        exact hkilled.2
      · intro k hk
        rw [trajectory_extendPrefix ω hk.le]
        exact hfirst k hk
    · rintro ⟨hkilled, hfirst⟩
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · intro k hk
        rw [← trajectory_extendPrefix ω hk]
        exact hkilled.1 k hk
      · rw [← trajectory_extendPrefix ω le_rfl]
        exact hkilled.2
      · intro k hk
        rw [← trajectory_extendPrefix ω hk.le]
        exact hfirst k hk
  rw [incrementFiltration_apply, heq]
  exact ⟨C, (Set.to_countable C).measurableSet, rfl⟩

lemma measurableSet_firstHitPathEvent (A : Finset Point) (n : ℕ)
    (x y : Point) : MeasurableSet (firstHitPathEvent A n x y) :=
  incrementFiltration.le n _ (measurableSet_firstHitPathEvent_filtration A n x y)

lemma measure_firstDirection_inter_shift_firstHitPathEvent
    (A : Finset Point) (n : ℕ) (z y : Point) (d : Direction) :
    fairSteps ({ω : StepPath | ω 0 = d} ∩
        shiftSteps 1 ⁻¹' firstHitPathEvent A n z y) =
      (1 / 4 : ℝ≥0∞) * fairSteps (firstHitPathEvent A n z y) := by
  have hfil := measurableSet_firstHitPathEvent_filtration A n z y
  rw [incrementFiltration_apply] at hfil
  obtain ⟨C, hC, hCeq⟩ := hfil
  have htail : shiftSteps 1 ⁻¹' firstHitPathEvent A n z y =
      stepBlock 1 n ⁻¹' C := by
    rw [← hCeq]
    rfl
  have hind := (indepFun_stepPrefix_stepBlock 1 n).measure_inter_preimage_eq_mul
    (firstDirectionSet d) C (Set.to_countable _).measurableSet hC
  rw [firstDirection_preimage, ← htail] at hind
  rw [hind]
  have hfirst : fairSteps {ω : StepPath | ω 0 = d} = 1 / 4 := by
    change fairSteps ((fun ω : StepPath ↦ ω 0) ⁻¹' {d}) = 1 / 4
    rw [← Measure.map_apply (measurable_pi_apply 0) (MeasurableSet.singleton d),
      fairSteps_eval, fairStep_singleton]
  have hshift : fairSteps (shiftSteps 1 ⁻¹' firstHitPathEvent A n z y) =
      fairSteps (firstHitPathEvent A n z y) := by
    rw [← Measure.map_apply (measurable_shiftSteps 1)
      (measurableSet_firstHitPathEvent A n z y), fairSteps_map_shiftSteps]
  rw [hfirst, hshift]

private def firstHitStepPiece (A : Finset Point) (n : ℕ) (x y : Point)
    (d : Direction) : Set StepPath :=
  {ω | ω 0 = d} ∩ shiftSteps 1 ⁻¹'
    firstHitPathEvent A n (x + directionVector d) y

lemma firstHitPathEvent_succ_eq_iUnion (A : Finset Point) (n : ℕ)
    {x y : Point} (hx : x ∈ A) (hxy : x ≠ y) :
    firstHitPathEvent A (n + 1) x y =
      ⋃ d : Direction, firstHitStepPiece A n x y d := by
  ext ω
  rw [mem_firstHitPathEvent_succ_iff]
  simp only [mem_iUnion, firstHitStepPiece, mem_inter_iff, mem_ofPred_eq, mem_preimage]
  constructor
  · rintro ⟨_, _, htail⟩
    exact ⟨ω 0, rfl, htail⟩
  · rintro ⟨d, hd, htail⟩
    subst d
    exact ⟨hx, hxy, htail⟩

lemma firstHitStepPiece_pairwise_disjoint (A : Finset Point) (n : ℕ)
    (x y : Point) : Pairwise fun d e : Direction ↦
      Disjoint (firstHitStepPiece A n x y d) (firstHitStepPiece A n x y e) := by
  intro d e hde
  rw [Set.disjoint_left]
  intro ω hd he
  exact hde (hd.1.symm.trans he.1)

lemma measurableSet_firstHitStepPiece (A : Finset Point) (n : ℕ)
    (x y : Point) (d : Direction) : MeasurableSet (firstHitStepPiece A n x y d) := by
  exact (measurableSet_eq_fun (measurable_pi_apply 0) measurable_const).inter
    ((measurable_shiftSteps 1) (measurableSet_firstHitPathEvent A n
      (x + directionVector d) y))

lemma measure_firstHitPathEvent_succ (A : Finset Point) (n : ℕ)
    (x y : Point) :
    fairSteps (firstHitPathEvent A (n + 1) x y) =
      if x ∈ A ∧ x ≠ y then
        ∑ d : Direction, (1 / 4 : ℝ≥0∞) *
          fairSteps (firstHitPathEvent A n (x + directionVector d) y)
      else 0 := by
  by_cases h : x ∈ A ∧ x ≠ y
  · rw [if_pos h, firstHitPathEvent_succ_eq_iUnion A n h.1 h.2]
    rw [measure_iUnion (firstHitStepPiece_pairwise_disjoint A n x y)
      (measurableSet_firstHitStepPiece A n x y), tsum_fintype]
    apply Finset.sum_congr rfl
    intro d hd
    exact measure_firstDirection_inter_shift_firstHitPathEvent A n
      (x + directionVector d) y d
  · rw [if_neg h]
    have hempty : firstHitPathEvent A (n + 1) x y = ∅ := by
      ext ω
      rw [mem_firstHitPathEvent_succ_iff]
      constructor
      · intro hw
        exact (h ⟨hw.1, hw.2.1⟩).elim
      · simp
    simp [hempty]

theorem fairSteps_firstHitPathEvent (A : Finset Point) (n : ℕ)
    (x y : Point) :
    fairSteps (firstHitPathEvent A n x y) =
      firstHitWeight planarKernel A y n x := by
  induction n generalizing x with
  | zero =>
      by_cases hx : x ∈ A <;> by_cases hxy : x = y
      · subst x
        simp [firstHitPathEvent, killedPathEvent, firstHitWeight, hx,
          show ((0, 0) : Point) = 0 by rfl]
      · have hempty : firstHitPathEvent A 0 x y = ∅ := by
          ext ω
          simp [firstHitPathEvent, killedPathEvent, hxy,
            show ((0, 0) : Point) = 0 by rfl]
        simp [hempty, firstHitWeight, hxy]
      · subst x
        simp [firstHitPathEvent, killedPathEvent, firstHitWeight, hx,
          show ((0, 0) : Point) = 0 by rfl]
      · have hempty : firstHitPathEvent A 0 x y = ∅ := by
          ext ω
          simp [firstHitPathEvent, killedPathEvent, hxy,
            show ((0, 0) : Point) = 0 by rfl]
        simp [hempty, firstHitWeight, hxy]
  | succ n ih =>
      rw [measure_firstHitPathEvent_succ, firstHitWeight_succ]
      by_cases h : x ∈ A ∧ x ≠ y
      · rw [if_pos h, if_pos h]
        simp_rw [ih]
        exact (sum_planarKernel_mul_of_zero_outside A x
          (fun z ↦ firstHitWeight planarKernel A y n z)
          (fun z hz ↦ firstHitWeight_eq_zero_of_notMem planarKernel A hz n y)).symm
      · simp [h]

/-- Event of hitting `y` before leaving `A`, at an arbitrary finite time. -/
def hitBeforeExitEvent (A : Finset Point) (x y : Point) : Set StepPath :=
  ⋃ n, firstHitPathEvent A n x y

lemma firstHitPathEvent_pairwise_disjoint (A : Finset Point) (x y : Point) :
    Pairwise fun m n ↦ Disjoint (firstHitPathEvent A m x y)
      (firstHitPathEvent A n x y) := by
  intro m n hmn
  rw [Set.disjoint_left]
  intro ω hm hn
  rcases lt_trichotomy m n with hlt | heq | hgt
  · exact (hn.2 m hlt) hm.1.2
  · exact hmn heq
  · exact (hm.2 n hgt) hn.1.2

lemma measurableSet_hitBeforeExitEvent (A : Finset Point) (x y : Point) :
    MeasurableSet (hitBeforeExitEvent A x y) := by
  exact MeasurableSet.iUnion (measurableSet_firstHitPathEvent A · x y)

theorem fairSteps_hitBeforeExitEvent (A : Finset Point) (x y : Point) :
    fairSteps (hitBeforeExitEvent A x y) = infiniteHitMass A x y := by
  rw [hitBeforeExitEvent, measure_iUnion
    (firstHitPathEvent_pairwise_disjoint A x y)
    (measurableSet_firstHitPathEvent A · x y)]
  simp_rw [fairSteps_firstHitPathEvent]
  rfl

/-- The corresponding hit-before-exit event on canonical path space. -/
def walkHitBeforeExit (A : Finset Point) (y : Point) : Set WalkPath :=
  ⋃ n, {s | ((∀ k ≤ n, s k ∈ A) ∧ s n = y) ∧ ∀ k < n, s k ≠ y}

lemma measurableSet_walkHitBeforeExit (A : Finset Point) (y : Point) :
    MeasurableSet (walkHitBeforeExit A y) := by
  unfold walkHitBeforeExit
  measurability

theorem simpleRandomWalkFrom_walkHitBeforeExit (A : Finset Point) (x y : Point) :
    simpleRandomWalkFrom x (walkHitBeforeExit A y) = infiniteHitMass A x y := by
  rw [simpleRandomWalkFrom, Measure.map_apply (measurable_trajectoryFrom x)
    (measurableSet_walkHitBeforeExit A y)]
  have hpre : trajectoryFrom x ⁻¹' walkHitBeforeExit A y = hitBeforeExitEvent A x y := by
    ext ω
    simp [walkHitBeforeExit, hitBeforeExitEvent, firstHitPathEvent,
      killedPathEvent, trajectoryFrom]
  rw [hpre, fairSteps_hitBeforeExitEvent]

theorem infiniteHitMass_le_one (A : Finset Point) (x y : Point) :
    infiniteHitMass A x y ≤ 1 := by
  rw [← fairSteps_hitBeforeExitEvent]
  exact prob_le_one

/-! ## Infinite Green functions and exact quotient identity -/

theorem tendsto_planarFiniteGreen (A : Finset Point) (x y : Point) :
    Tendsto (fun N ↦ planarFiniteGreen A N x y) atTop
      (𝓝 (infiniteGreen A x y)) := by
  have h := ENNReal.tendsto_nat_tsum
    (fun n ↦ killedPower planarKernel A n x y)
  have hc : Tendsto
      (fun N ↦ ∑ n ∈ Finset.range (N + 1), killedPower planarKernel A n x y)
      atTop (𝓝 (∑' n, killedPower planarKernel A n x y)) := by
    convert h.comp (tendsto_add_atTop_nat 1) using 1
    rfl
  simpa only [planarFiniteGreen, GreenFunction.finiteGreen, infiniteGreen] using hc

/-- Monotone-convergence representation as the sum of canonical killed path
probabilities. -/
theorem infiniteGreen_eq_tsum_path_probabilities (A : Finset Point) (x y : Point) :
    infiniteGreen A x y = ∑' n, fairSteps (killedPathEvent A n x y) := by
  simp_rw [fairSteps_killedPathEvent]
  rfl

/-- Indicator that the path contributes a killed visit to `y` at time `n`. -/
noncomputable def killedVisitIndicator (A : Finset Point) (n : ℕ) (x y : Point) :
    StepPath → ℝ≥0∞ :=
  (killedPathEvent A n x y).indicator fun _ ↦ 1

lemma measurable_killedVisitIndicator (A : Finset Point) (n : ℕ) (x y : Point) :
    Measurable (killedVisitIndicator A n x y) := by
  exact Measurable.indicator measurable_const (measurableSet_killedPathEvent A n x y)

/-- Total killed occupation count.  The `ENNReal` value is allowed to be
infinite on a path, though it is finite almost surely in every finite domain. -/
noncomputable def killedOccupation (A : Finset Point) (x y : Point)
    (ω : StepPath) : ℝ≥0∞ :=
  ∑' n, killedVisitIndicator A n x y ω

/-- Monotone convergence identifies the expectation of killed occupation
with the infinite killed Green function. -/
theorem lintegral_killedOccupation (A : Finset Point) (x y : Point) :
    ∫⁻ ω, killedOccupation A x y ω ∂fairSteps = infiniteGreen A x y := by
  change (∫⁻ ω, ∑' n, killedVisitIndicator A n x y ω ∂fairSteps) = _
  rw [lintegral_tsum]
  · rw [infiniteGreen]
    congr 1
    funext n
    rw [killedVisitIndicator, lintegral_indicator
      (measurableSet_killedPathEvent A n x y)]
    simp [fairSteps_killedPathEvent]
  · exact fun n ↦ (measurable_killedVisitIndicator A n x y).aemeasurable

/-- Exact infinite first-entrance factorization. -/
private lemma tsum_mul_tsum_eq_tsum_antidiagonal
    (f g : ℕ → ℝ≥0∞) :
    (∑' n, f n) * (∑' n, g n) =
      ∑' n, ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n,
        f kl.1 * g kl.2 := by
  let F : ℕ × ℕ → ℝ≥0∞ := fun p ↦ f p.1 * g p.2
  let S : ℕ → Type := fun n ↦
    (Finset.HasAntidiagonal.antidiagonal n : Set (ℕ × ℕ))
  let H : (Σ n, S n) → ℝ≥0∞ := fun q ↦ F q.2
  have hequiv : (∑' p : ℕ × ℕ, F p) = ∑' q : Σ n, S n, H q := by
    exact (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.tsum_eq F).symm
  have hsigma : (∑' q : Σ n, S n, H q) = ∑' n, ∑' kl : S n, H ⟨n, kl⟩ := by
    exact ENNReal.summable.tsum_sigma' (fun _ ↦ ENNReal.summable)
  calc
    (∑' n, f n) * (∑' n, g n) =
        ∑' k, f k * (∑' n, g n) := ENNReal.tsum_mul_right.symm
    _ = ∑' k, ∑' m, f k * g m := by
      congr 1
      funext k
      rw [ENNReal.tsum_mul_left]
    _ = ∑' p : ℕ × ℕ, f p.1 * g p.2 := by
      simpa using (ENNReal.tsum_prod'
        (f := fun p : ℕ × ℕ ↦ f p.1 * g p.2)).symm
    _ = ∑' q : Σ n : ℕ,
        (Finset.HasAntidiagonal.antidiagonal n : Set (ℕ × ℕ)),
        f (q.2 : ℕ × ℕ).1 * g (q.2 : ℕ × ℕ).2 := by simpa [F, S, H] using hequiv
    _ = ∑' n : ℕ, ∑' kl :
        (Finset.HasAntidiagonal.antidiagonal n : Set (ℕ × ℕ)),
        f (kl : ℕ × ℕ).1 * g (kl : ℕ × ℕ).2 := by simpa [F, S, H] using hsigma
    _ = ∑' n : ℕ, ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n,
        f kl.1 * g kl.2 := by
      congr 1
      funext n
      rw [tsum_fintype]
      exact (Finset.sum_subtype (Finset.HasAntidiagonal.antidiagonal n)
        (fun _ ↦ Iff.rfl) (fun kl ↦ f kl.1 * g kl.2)).symm

theorem infiniteGreen_eq_hit_mul_diagonal (A : Finset Point) (x y : Point) :
    infiniteGreen A x y =
      infiniteHitMass A x y * infiniteGreen A y y := by
  rw [infiniteGreen, infiniteHitMass, infiniteGreen]
  rw [tsum_mul_tsum_eq_tsum_antidiagonal]
  congr 1
  funext n
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun k l ↦ firstHitWeight planarKernel A y k x *
      killedPower planarKernel A l y y) n]
  exact killedPower_eq_sum_firstHitWeight planarKernel A n x y

/-! ## Finiteness in a finite box -/

private lemma tsum_pow_div_ne_top (r : ℝ≥0∞) (L : ℕ) (hL : 0 < L)
    (hr : r < 1) : (∑' n : ℕ, r ^ (n / L)) ≠ ⊤ := by
  let _ : NeZero L := ⟨Nat.ne_of_gt hL⟩
  have hreindex : (∑' n : ℕ, r ^ (n / L)) =
      ∑' p : ℕ × Fin L, r ^ p.1 := by
    simpa [Nat.divModEquiv] using
      (Nat.divModEquiv L).tsum_eq (fun p : ℕ × Fin L ↦ r ^ p.1)
  have hprod : (∑' p : ℕ × Fin L, r ^ p.1) =
      (L : ℝ≥0∞) * (1 - r)⁻¹ := by
    rw [ENNReal.tsum_prod']
    simp only [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
  rw [hreindex, hprod]
  apply ENNReal.mul_ne_top
  · exact ENNReal.natCast_ne_top L
  · rw [ENNReal.inv_ne_top]
    exact ne_of_gt (tsub_pos_iff_lt.2 hr)

lemma killedPathEvent_subset_boxSurvival (A : Finset Point) (R n : ℕ)
    (x y : Point) (hA : A ⊆ coordinateBox R) :
    killedPathEvent A n x y ⊆ staysInCoordinateBoxThrough x R n := by
  intro ω hω k hk
  exact hA (hω.1 k hk)

/-- In a finite coordinate box the killed Green function is finite.  The
proof uses the uniform geometric exit tail, grouping horizons by complete
escape blocks. -/
theorem infiniteGreen_ne_top_of_subset_coordinateBox
    (A : Finset Point) (R : ℕ) (x y : Point)
    (hA : A ⊆ coordinateBox R) : infiniteGreen A x y ≠ ⊤ := by
  let L := escapeBlockLength R
  let r : ℝ≥0∞ := 1 - (4 : ℝ≥0∞)⁻¹ ^ L
  have hL : 0 < L := by simp [L, escapeBlockLength]
  have hp0 : (0 : ℝ≥0∞) < (4 : ℝ≥0∞)⁻¹ ^ L := by
    exact ENNReal.pow_pos (ENNReal.inv_pos.2 (by norm_num)) L
  have hr : r < 1 := by
    exact ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero (ne_of_gt hp0)
  have hterm (n : ℕ) : killedPower planarKernel A n x y ≤ r ^ (n / L) := by
    rw [← fairSteps_killedPathEvent]
    calc
      fairSteps (killedPathEvent A n x y) ≤
          fairSteps (staysInCoordinateBoxThrough x R n) :=
        measure_mono (killedPathEvent_subset_boxSurvival A R n x y hA)
      _ ≤ r ^ (n / L) := by
        simpa [r, L] using
          fairSteps_staysInCoordinateBoxThrough_le_geometric_div x R n
  have hsum : infiniteGreen A x y ≤ ∑' n : ℕ, r ^ (n / L) := by
    rw [infiniteGreen]
    exact ENNReal.tsum_le_tsum hterm
  exact ne_top_of_le_ne_top (tsum_pow_div_ne_top r L hL hr) hsum

/-- The standard Green-function quotient formula.  Finiteness of the
diagonal term is exactly what is needed to cancel it in `ENNReal`. -/
theorem infiniteHitMass_eq_green_div (A : Finset Point) (x y : Point)
    (hy : y ∈ A) (hfinite : infiniteGreen A y y ≠ ⊤) :
    infiniteHitMass A x y = infiniteGreen A x y / infiniteGreen A y y := by
  have hpos : infiniteGreen A y y ≠ 0 := by
    have hone : (1 : ℝ≥0∞) ≤ infiniteGreen A y y := by
      have hzero : killedPower planarKernel A 0 y y ≤
          ∑' n, killedPower planarKernel A n y y := ENNReal.le_tsum 0
      simpa [infiniteGreen, killedPower, hy] using hzero
    exact ne_of_gt (lt_of_lt_of_le zero_lt_one hone)
  apply (ENNReal.eq_div_iff hpos hfinite).2
  rw [mul_comm]
  exact (infiniteGreen_eq_hit_mul_diagonal A x y).symm

/-- Probability form of the killed Green quotient. -/
theorem simpleRandomWalkFrom_hitBeforeExit_eq_green_div
    (A : Finset Point) (x y : Point) (hy : y ∈ A)
    (hfinite : infiniteGreen A y y ≠ ⊤) :
    simpleRandomWalkFrom x (walkHitBeforeExit A y) =
      infiniteGreen A x y / infiniteGreen A y y := by
  rw [simpleRandomWalkFrom_walkHitBeforeExit,
    infiniteHitMass_eq_green_div A x y hy hfinite]

/-- The Green quotient in any domain contained in a coordinate box, with
finiteness discharged by the geometric exit estimate. -/
theorem infiniteHitMass_eq_green_div_of_subset_coordinateBox
    (A : Finset Point) (R : ℕ) (x y : Point)
    (hA : A ⊆ coordinateBox R) (hy : y ∈ A) :
    infiniteHitMass A x y = infiniteGreen A x y / infiniteGreen A y y :=
  infiniteHitMass_eq_green_div A x y hy
    (infiniteGreen_ne_top_of_subset_coordinateBox A R y y hA)

/-- Probability form of the Green quotient in any domain contained in a
coordinate box.  This is the assumption-free finite-domain hitting theorem
used by the annular estimates. -/
theorem simpleRandomWalkFrom_hitBeforeExit_eq_green_div_of_subset_coordinateBox
    (A : Finset Point) (R : ℕ) (x y : Point)
    (hA : A ⊆ coordinateBox R) (hy : y ∈ A) :
    simpleRandomWalkFrom x (walkHitBeforeExit A y) =
      infiniteGreen A x y / infiniteGreen A y y :=
  simpleRandomWalkFrom_hitBeforeExit_eq_green_div A x y hy
    (infiniteGreen_ne_top_of_subset_coordinateBox A R y y hA)

/-- Specialization to the closed lattice disc used in the annulus API. -/
theorem simpleRandomWalkFrom_hitBeforeExit_closedDisc_eq_green_div
    (R : ℕ) (x y : Point) (hy : y ∈ closedDisc R) :
    simpleRandomWalkFrom x (walkHitBeforeExit (closedDisc R) y) =
      infiniteGreen (closedDisc R) x y / infiniteGreen (closedDisc R) y y := by
  apply simpleRandomWalkFrom_hitBeforeExit_eq_green_div_of_subset_coordinateBox
    (closedDisc R) R x y
  · intro z hz
    exact (mem_closedDisc R z).mp hz |>.1
  · exact hy

end GreenProbability
end Erdos1165
