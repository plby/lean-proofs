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

import ErdosProblems.Erdos1165.Basic

/-!
# Increment and strong-Markov facts for Erdős Problem 1165

This file develops the probabilistic facts about the canonical product-space
realization of planar simple random walk that are needed repeatedly in a proof
of the Hao--Li--Okada--Zheng theorem.

Mathlib already proves that the coordinate maps under `Measure.infinitePi` are
independent and have the prescribed marginal distributions.  The finite-time
strong Markov statement below is not an invocation of an external theorem: it
is proved from those product-measure facts by decomposing according to the
events `{τ = n}`.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace Erdos1165

/-! ## Deterministic shifts and finite blocks -/

/-- Drop the first `n` increments. -/
def shiftSteps (n : ℕ) (ω : StepPath) : StepPath := fun j ↦ ω (n + j)

/-- The first `n` increments as a tuple indexed by `Fin n`. -/
def stepPrefix (n : ℕ) (ω : StepPath) : Fin n → Direction := fun j ↦ ω j

/-- The block of `k` increments beginning at index `n`. -/
def stepBlock (n k : ℕ) (ω : StepPath) : Fin k → Direction :=
  fun j ↦ ω (n + j)

/-- The product law of a block of `k` fair increments. -/
noncomputable def fairBlock (k : ℕ) : Measure (Fin k → Direction) :=
  Measure.infinitePi fun _ : Fin k ↦ fairStep

noncomputable instance (k : ℕ) : IsProbabilityMeasure (fairBlock k) := by
  unfold fairBlock
  infer_instance

lemma measurable_shiftSteps (n : ℕ) : Measurable (shiftSteps n) := by
  exact measurable_pi_lambda _ fun _ ↦ measurable_pi_apply _

lemma measurable_stepPrefix (n : ℕ) : Measurable (stepPrefix n) := by
  exact measurable_pi_lambda _ fun j ↦ measurable_pi_apply (j : ℕ)

lemma measurable_stepBlock (n k : ℕ) : Measurable (stepBlock n k) := by
  exact measurable_pi_lambda _ fun j ↦ measurable_pi_apply (n + j)

@[simp] lemma stepBlock_eq_stepPrefix_shiftSteps (n k : ℕ) (ω : StepPath) :
    stepBlock n k ω = stepPrefix k (shiftSteps n ω) := rfl

/-! ## The increments are IID -/

/-- The coordinate increments are mutually independent. -/
theorem fairSteps_iIndep :
    iIndepFun (fun n : ℕ ↦ fun ω : StepPath ↦ ω n) fairSteps := by
  unfold fairSteps
  exact iIndepFun_infinitePi (X := fun _ x ↦ x) fun _ ↦ measurable_id

/-- Every coordinate increment has law `fairStep`. -/
theorem fairSteps_map_eval (n : ℕ) :
    fairSteps.map (fun ω : StepPath ↦ ω n) = fairStep := by
  exact Measure.infinitePi_map_eval (fun _ : ℕ ↦ fairStep) n

/-- A deterministic tail of the increment sequence again has the IID product law. -/
theorem fairSteps_map_shiftSteps (n : ℕ) :
    fairSteps.map (shiftSteps n) = fairSteps := by
  unfold fairSteps shiftSteps
  exact Measure.map_infinitePi_infinitePi_of_inj
    (P := fun _ : ℕ ↦ fairStep) (f := fun j : ℕ ↦ n + j) fun _ _ ↦ Nat.add_left_cancel

/-- Every deterministic finite block has the corresponding finite product law. -/
theorem fairSteps_map_stepBlock (n k : ℕ) :
    fairSteps.map (stepBlock n k) = fairBlock k := by
  unfold fairSteps fairBlock stepBlock
  exact Measure.map_infinitePi_infinitePi_of_inj
    (P := fun _ : ℕ ↦ fairStep) (f := fun j : Fin k ↦ n + j) fun i j h ↦ by
      exact Fin.ext (Nat.add_left_cancel h)

/-! ## Independence of the past and a deterministic future block -/

private def prefixIndexSet (n : ℕ) : Finset ℕ := Finset.range n

private def blockIndexSet (n k : ℕ) : Finset ℕ :=
  (Finset.range k).image fun j ↦ n + j

private lemma prefixIndexSet_disjoint_blockIndexSet (n k : ℕ) :
    Disjoint (prefixIndexSet n) (blockIndexSet n k) := by
  rw [Finset.disjoint_left]
  intro i hi h'i
  rw [prefixIndexSet, Finset.mem_range] at hi
  rw [blockIndexSet, Finset.mem_image] at h'i
  obtain ⟨j, hj, rfl⟩ := h'i
  omega

/-- The first `n` increments are independent of the next `k` increments. -/
theorem indepFun_stepPrefix_stepBlock (n k : ℕ) :
    IndepFun (stepPrefix n) (stepBlock n k) fairSteps := by
  let S := prefixIndexSet n
  let T := blockIndexSet n k
  have h := fairSteps_iIndep.indepFun_finset S T
    (prefixIndexSet_disjoint_blockIndexSet n k) (fun _ ↦ measurable_pi_apply _)
  let toPrefix : (S → Direction) → (Fin n → Direction) :=
    fun u i ↦ u ⟨i, by simp [S, prefixIndexSet]⟩
  let toBlock : (T → Direction) → (Fin k → Direction) :=
    fun u i ↦ u ⟨n + i, by
      simp only [T, blockIndexSet, Finset.mem_image]
      exact ⟨i, by simp, rfl⟩⟩
  have hc := h.comp (measurable_of_countable toPrefix) (measurable_of_countable toBlock)
  have hp : stepPrefix n = fun x i ↦ x (i : ℕ) := rfl
  have hb : stepBlock n k = fun x i ↦ x (n + (i : ℕ)) := rfl
  rw [hp, hb]
  simpa [Function.comp_def, toPrefix, toBlock] using hc

/-! ## The increment filtration and finite stopping times -/

private def truncatePrefix {n m : ℕ} (h : n ≤ m) (u : Fin m → Direction) :
    Fin n → Direction := fun i ↦ u ⟨i, lt_of_lt_of_le i.isLt h⟩

/-- The information carried by increments with indices `< n`.  Thus the
position at time `n` is measurable at filtration time `n`. -/
def incrementFiltration : Filtration ℕ (inferInstance : MeasurableSpace StepPath) where
  seq n := MeasurableSpace.comap (stepPrefix n) inferInstance
  mono' := by
    intro n m hnm
    exact MeasurableSpace.comap_le_comap_of_eq_comp (truncatePrefix hnm)
      (measurable_of_countable _) (by ext ω i; rfl)
  le' n := (measurable_stepPrefix n).comap_le

@[simp] lemma incrementFiltration_apply (n : ℕ) :
    incrementFiltration n = MeasurableSpace.comap (stepPrefix n) inferInstance := rfl

/-- A finite stopping time is a natural-valued stopping time for the increment
filtration.  It cannot take the value `∞`; its coercion to `WithTop ℕ` is used
only to interoperate with Mathlib's standard stopping-time API. -/
def IsFiniteStoppingTime (τ : StepPath → ℕ) : Prop :=
  IsStoppingTime incrementFiltration fun ω ↦ (τ ω : WithTop ℕ)

theorem isFiniteStoppingTime_const (n : ℕ) :
    IsFiniteStoppingTime fun _ : StepPath ↦ n := by
  exact isStoppingTime_const incrementFiltration n

lemma IsFiniteStoppingTime.measurableSet_eq (hτ : IsFiniteStoppingTime τ) (n : ℕ) :
    MeasurableSet[incrementFiltration n] {ω | τ ω = n} := by
  change IsStoppingTime incrementFiltration (fun ω ↦ (τ ω : WithTop ℕ)) at hτ
  simpa using MeasureTheory.IsStoppingTime.measurableSet_eq hτ n

lemma IsFiniteStoppingTime.measurableSet_eq_global (hτ : IsFiniteStoppingTime τ) (n : ℕ) :
    MeasurableSet {ω | τ ω = n} :=
  incrementFiltration.le n _ (hτ.measurableSet_eq n)

/-! ## Strong Markov property at a finite stopping time -/

/-- At a fixed value of a finite stopping time, the next finite block has its
unconditional product law.  This is the atomic factorization from which the
finite-dimensional strong Markov theorem is assembled. -/
theorem strongMarkov_at_value (hτ : IsFiniteStoppingTime τ) (n k : ℕ)
    (v : Fin k → Direction) :
    fairSteps ({ω | τ ω = n} ∩ {ω | stepBlock n k ω = v}) =
      fairSteps {ω | τ ω = n} * fairBlock k {v} := by
  have hn := hτ.measurableSet_eq n
  rw [incrementFiltration_apply] at hn
  obtain ⟨s, hs, hs_eq⟩ := hn
  have hind := (indepFun_stepPrefix_stepBlock n k).measure_inter_preimage_eq_mul
    s {v} hs (measurableSet_singleton v)
  have hblock : fairSteps {ω | stepBlock n k ω = v} = fairBlock k {v} := by
    rw [← fairSteps_map_stepBlock n k, Measure.map_apply (measurable_stepBlock n k)
      (measurableSet_singleton v)]
    rfl
  rw [← hblock]
  simpa only [Set.preimage_ofPred_eq, Set.mem_singleton_iff] using hs_eq ▸ hind

/-- An event is observable at the finite stopping time `τ` when its part on
each atom `{τ = n}` is measurable using the first `n` increments.  For
natural-valued stopping times this is the concrete form of measurability with
respect to the stopped σ-algebra. -/
def IsMeasurableAtStopping (τ : StepPath → ℕ) (A : Set StepPath) : Prop :=
  ∀ n, MeasurableSet[incrementFiltration n] (A ∩ {ω | τ ω = n})

lemma IsMeasurableAtStopping.measurableSet (hA : IsMeasurableAtStopping τ A) :
    MeasurableSet A := by
  have h_union : (⋃ n, A ∩ {ω | τ ω = n}) = A := by
    ext ω
    simp
  rw [← h_union]
  exact MeasurableSet.iUnion fun n ↦ incrementFiltration.le n _ (hA n)

/-- Mathlib's stopped σ-algebra implies the concrete atomwise formulation
`IsMeasurableAtStopping`. -/
theorem isMeasurableAtStopping_of_measurableSet_stopping
    (hτ : IsFiniteStoppingTime τ)
    (hA : MeasurableSet[(show IsStoppingTime incrementFiltration
      (fun ω ↦ (τ ω : WithTop ℕ)) from hτ).measurableSpace] A) :
    IsMeasurableAtStopping τ A := by
  intro n
  let hτ' : IsStoppingTime incrementFiltration
      (fun ω ↦ (τ ω : WithTop ℕ)) := hτ
  have hEqFiltration : MeasurableSet[incrementFiltration n]
      {ω | (τ ω : WithTop ℕ) = n} := hτ'.measurableSet_eq n
  have hEqStopped : MeasurableSet[hτ'.measurableSpace]
      {ω | (τ ω : WithTop ℕ) = n} := by
    have := (hτ'.measurableSet_inter_eq_iff Set.univ n).2 (by
      simpa using hEqFiltration)
    simpa using this
  have hInt : MeasurableSet[hτ'.measurableSpace]
      (A ∩ {ω | (τ ω : WithTop ℕ) = n}) := hA.inter hEqStopped
  have := (hτ'.measurableSet_inter_eq_iff A n).1 hInt
  simpa using this

/-- A stopped-past event, restricted to `{τ = n}`, is independent of a
specified block of future increments. -/
theorem strongMarkov_stoppedEvent_at_value
    (hA : IsMeasurableAtStopping τ A) (n k : ℕ) (v : Fin k → Direction) :
    fairSteps ((A ∩ {ω | τ ω = n}) ∩ {ω | stepBlock n k ω = v}) =
      fairSteps (A ∩ {ω | τ ω = n}) * fairBlock k {v} := by
  have hn := hA n
  rw [incrementFiltration_apply] at hn
  obtain ⟨s, hs, hs_eq⟩ := hn
  have hind := (indepFun_stepPrefix_stepBlock n k).measure_inter_preimage_eq_mul
    s {v} hs (measurableSet_singleton v)
  have hblock : fairSteps {ω | stepBlock n k ω = v} = fairBlock k {v} := by
    rw [← fairSteps_map_stepBlock n k, Measure.map_apply (measurable_stepBlock n k)
      (measurableSet_singleton v)]
    rfl
  rw [← hblock]
  simpa only [Set.preimage_ofPred_eq, Set.mem_singleton_iff] using hs_eq ▸ hind

/-- The block of `k` increments immediately following a finite stopping time. -/
def postStoppingBlock (τ : StepPath → ℕ) (k : ℕ) (ω : StepPath) : Fin k → Direction :=
  fun j ↦ ω (τ ω + j)

private lemma postStoppingBlock_eq_on (τ : StepPath → ℕ) (k n : ℕ)
    {ω : StepPath} (hω : τ ω = n) :
    postStoppingBlock τ k ω = stepBlock n k ω := by
  ext j
  simp [postStoppingBlock, stepBlock, hω]

lemma measurable_postStoppingBlock (hτ : IsFiniteStoppingTime τ) (k : ℕ) :
    Measurable (postStoppingBlock τ k) := by
  intro s hs
  have hpre : postStoppingBlock τ k ⁻¹' s = ⋃ n,
      {ω | τ ω = n} ∩ stepBlock n k ⁻¹' s := by
    ext ω
    simp only [mem_preimage, mem_iUnion, mem_inter_iff, mem_ofPred_eq]
    constructor
    · intro hω
      refine ⟨τ ω, rfl, ?_⟩
      rw [← postStoppingBlock_eq_on τ k (τ ω) rfl]
      exact hω
    · rintro ⟨n, hn, hω⟩
      rw [postStoppingBlock_eq_on τ k n hn]
      exact hω
  rw [hpre]
  exact MeasurableSet.iUnion fun n ↦
    (hτ.measurableSet_eq_global n).inter ((measurable_stepBlock n k) hs)

/-- **Finite-dimensional strong Markov property.**  For every natural-valued
stopping time, the first `k` increments after the stopping time have exactly the
same law as `k` fresh fair increments. -/
theorem fairSteps_map_postStoppingBlock (hτ : IsFiniteStoppingTime τ) (k : ℕ) :
    fairSteps.map (postStoppingBlock τ k) = fairBlock k := by
  apply Measure.ext_of_singleton
  intro v
  rw [Measure.map_apply (measurable_postStoppingBlock hτ k) (measurableSet_singleton v)]
  let A : ℕ → Set StepPath := fun n ↦
    {ω | τ ω = n} ∩ {ω | stepBlock n k ω = v}
  have h_union : {ω | postStoppingBlock τ k ω = v} = ⋃ n, A n := by
    ext ω
    simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff, A]
    constructor
    · intro h
      refine ⟨τ ω, rfl, ?_⟩
      exact (postStoppingBlock_eq_on τ k (τ ω) rfl).symm.trans h
    · rintro ⟨n, hn, hv⟩
      exact (postStoppingBlock_eq_on τ k n hn).trans hv
  have hA_meas : ∀ n, MeasurableSet (A n) := fun n ↦
    (hτ.measurableSet_eq_global n).inter
      ((measurable_stepBlock n k) (measurableSet_singleton v))
  have hA_disjoint : Pairwise fun n m ↦ Disjoint (A n) (A m) := by
    intro n m hnm
    rw [Set.disjoint_left]
    intro ω hωn hωm
    exact hnm (hωn.1.symm.trans hωm.1)
  change fairSteps {ω | postStoppingBlock τ k ω = v} = fairBlock k {v}
  rw [h_union, measure_iUnion hA_disjoint hA_meas]
  simp_rw [A, strongMarkov_at_value hτ]
  rw [ENNReal.tsum_mul_right]
  have hτ_union : (⋃ n, {ω | τ ω = n}) = Set.univ := by
    ext ω
    simp
  have hτ_disjoint : Pairwise fun n m ↦
      Disjoint {ω | τ ω = n} {ω | τ ω = m} := by
    intro n m hnm
    rw [Set.disjoint_left]
    intro ω hωn hωm
    exact hnm (hωn.symm.trans hωm)
  have hτ_meas : ∀ n, MeasurableSet {ω | τ ω = n} := hτ.measurableSet_eq_global
  rw [← measure_iUnion hτ_disjoint hτ_meas, hτ_union, measure_univ, one_mul]

/-- **Strong Markov factorization.**  Every event observable at the stopping
time is independent of every singleton event for a finite block of increments
after the stopping time.  Since the block space is finite, singleton events
generate its full σ-algebra. -/
theorem strongMarkov_stoppedEvent (_hτ : IsFiniteStoppingTime τ)
    (hA : IsMeasurableAtStopping τ A) (k : ℕ) (v : Fin k → Direction) :
    fairSteps (A ∩ {ω | postStoppingBlock τ k ω = v}) =
      fairSteps A * fairBlock k {v} := by
  let B : ℕ → Set StepPath := fun n ↦
    (A ∩ {ω | τ ω = n}) ∩ {ω | stepBlock n k ω = v}
  have h_union : A ∩ {ω | postStoppingBlock τ k ω = v} = ⋃ n, B n := by
    ext ω
    simp only [mem_inter_iff, mem_ofPred_eq, mem_iUnion, B]
    constructor
    · rintro ⟨hωA, hωv⟩
      refine ⟨τ ω, ⟨hωA, rfl⟩, ?_⟩
      exact (postStoppingBlock_eq_on τ k (τ ω) rfl).symm.trans hωv
    · rintro ⟨n, ⟨hωA, hn⟩, hωv⟩
      exact ⟨hωA, (postStoppingBlock_eq_on τ k n hn).trans hωv⟩
  have hB_meas : ∀ n, MeasurableSet (B n) := fun n ↦
    (incrementFiltration.le n _ (hA n)).inter
      ((measurable_stepBlock n k) (measurableSet_singleton v))
  have hB_disjoint : Pairwise fun n m ↦ Disjoint (B n) (B m) := by
    intro n m hnm
    rw [Set.disjoint_left]
    intro ω hωn hωm
    exact hnm (hωn.1.2.symm.trans hωm.1.2)
  rw [h_union, measure_iUnion hB_disjoint hB_meas]
  simp_rw [B, strongMarkov_stoppedEvent_at_value hA]
  rw [ENNReal.tsum_mul_right]
  have hA_union : (⋃ n, A ∩ {ω | τ ω = n}) = A := by
    ext ω
    simp
  have hA_disjoint : Pairwise fun n m ↦
      Disjoint (A ∩ {ω | τ ω = n}) (A ∩ {ω | τ ω = m}) := by
    intro n m hnm
    rw [Set.disjoint_left]
    intro ω hωn hωm
    exact hnm (hωn.2.symm.trans hωm.2)
  have hA_meas : ∀ n, MeasurableSet (A ∩ {ω | τ ω = n}) := fun n ↦
    incrementFiltration.le n _ (hA n)
  rw [← measure_iUnion hA_disjoint hA_meas, hA_union]

/-- Measure-valued form of the finite-dimensional strong Markov property.
Restricting to an event observable at `τ`, then mapping the post-`τ` block,
gives its probability times the fresh product law. -/
theorem map_restrict_postStoppingBlock (hτ : IsFiniteStoppingTime τ)
    (hA : IsMeasurableAtStopping τ A) (k : ℕ) :
    (fairSteps.restrict A).map (postStoppingBlock τ k) =
      (fairSteps A) • fairBlock k := by
  apply Measure.ext_of_singleton
  intro v
  rw [Measure.map_apply (measurable_postStoppingBlock hτ k) (measurableSet_singleton v)]
  rw [Measure.restrict_apply ((measurable_postStoppingBlock hτ k)
    (measurableSet_singleton v))]
  rw [Measure.smul_apply, smul_eq_mul]
  have hpre : postStoppingBlock τ k ⁻¹' {v} =
      {ω | postStoppingBlock τ k ω = v} := by
    ext ω
    simp
  rw [hpre, Set.inter_comm]
  exact strongMarkov_stoppedEvent hτ hA k v

/-- Setwise form of strong Markov: every measurable event of a finite future
block factors from every event observable at the stopping time. -/
theorem strongMarkov_stoppedEvent_set (hτ : IsFiniteStoppingTime τ)
    (hA : IsMeasurableAtStopping τ A) (k : ℕ) (C : Set (Fin k → Direction)) :
    fairSteps (A ∩ postStoppingBlock τ k ⁻¹' C) =
      fairSteps A * fairBlock k C := by
  have hC : MeasurableSet C := (Set.to_countable C).measurableSet
  have h := congrArg (fun μ : Measure (Fin k → Direction) ↦ μ C)
    (map_restrict_postStoppingBlock hτ hA k)
  rw [Measure.map_apply (measurable_postStoppingBlock hτ k) hC] at h
  rw [Measure.restrict_apply ((measurable_postStoppingBlock hτ k)
    hC)] at h
  rw [Measure.smul_apply, smul_eq_mul] at h
  simpa only [Set.inter_comm] using h

/-! ## Relation to the position process -/

/-- Restarting the trajectory after deterministic time `n` subtracts the old
position and is the trajectory generated by the shifted increments. -/
theorem trajectory_add_sub_trajectory (ω : StepPath) (n k : ℕ) :
    trajectory ω (n + k) - trajectory ω n = trajectory (shiftSteps n ω) k := by
  simp only [trajectory, shiftSteps]
  rw [Finset.sum_range_add, add_sub_cancel_left]

/-- The finite vector of displacements after a stopping time has the law of a
fresh finite vector of displacements.  This pointwise identity is the bridge
from `fairSteps_map_postStoppingBlock` to random-walk restart arguments. -/
theorem trajectory_after_stopping (τ : StepPath → ℕ) (ω : StepPath) (k : ℕ) :
    trajectory ω (τ ω + k) - trajectory ω (τ ω) =
      trajectory (shiftSteps (τ ω) ω) k :=
  trajectory_add_sub_trajectory ω (τ ω) k

/-- The displacement encoded by a finite tuple of increments. -/
def markovBlockDisplacement {k : ℕ} (u : Fin k → Direction) : Point :=
  ∑ j, directionVector (u j)

lemma measurable_markovBlockDisplacement (k : ℕ) :
    Measurable (@markovBlockDisplacement k) := measurable_of_countable _

lemma trajectory_eq_markovBlockDisplacement_stepPrefix (ω : StepPath) (k : ℕ) :
    trajectory ω k = markovBlockDisplacement (stepPrefix k ω) := by
  simp only [trajectory, markovBlockDisplacement, stepPrefix]
  rw [← Fin.sum_univ_eq_sum_range]

/-- The displacement during the `k` increments immediately after `τ`. -/
def postStoppingDisplacement (τ : StepPath → ℕ) (k : ℕ) (ω : StepPath) : Point :=
  markovBlockDisplacement (postStoppingBlock τ k ω)

lemma postStoppingDisplacement_eq_trajectory_sub (τ : StepPath → ℕ)
    (k : ℕ) (ω : StepPath) :
    postStoppingDisplacement τ k ω =
      trajectory ω (τ ω + k) - trajectory ω (τ ω) := by
  rw [trajectory_after_stopping]
  exact (trajectory_eq_markovBlockDisplacement_stepPrefix (shiftSteps (τ ω) ω) k).symm

/-- A displacement over a fixed finite horizon after a stopping time has the
same law as the displacement of a fresh walk over that horizon. -/
theorem fairSteps_map_postStoppingDisplacement (hτ : IsFiniteStoppingTime τ) (k : ℕ) :
    fairSteps.map (postStoppingDisplacement τ k) =
      (fairBlock k).map markovBlockDisplacement := by
  have h := congrArg (fun μ : Measure (Fin k → Direction) ↦ μ.map markovBlockDisplacement)
    (fairSteps_map_postStoppingBlock hτ k)
  rw [Measure.map_map (measurable_markovBlockDisplacement k)
    (measurable_postStoppingBlock hτ k)] at h
  rw [show postStoppingDisplacement τ k =
    fun x ↦ markovBlockDisplacement (postStoppingBlock τ k x) from rfl]
  simpa only [Function.comp_def] using h

end Erdos1165
