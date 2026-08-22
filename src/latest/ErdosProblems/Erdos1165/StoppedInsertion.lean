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

import ErdosProblems.Erdos1165.Basic
import ErdosProblems.Erdos1165.Clock
import ErdosProblems.Erdos1165.Markov
import ErdosProblems.Erdos1165.LazyDecomposition
import ErdosProblems.Erdos1165.PathInsertion

/-!
# Stopped insertion and bounded HLOZ level clocks

`PathInsertion` proves the exact insertion law at a deterministic external
time.  This file supplies the stopping-time and measurability layer that can
legitimately be obtained from the current development.

* `truncatedLevelTime m k cutoff` is the first time at which `k` sites have
  local time at least `m`, capped at `cutoff`.
* It is a finite stopping time for the increment filtration.
* Finite external traces, external clocks, and deleted-excursion counts are
  measurable both at deterministic times and at finite stopping times.
* A finite block after a truncated random level time has its fresh product
  law.  Conditioning additionally on any finite truncation event gives an
  exact quotient identity.  The event `awayFromDominoes` makes explicit that
  the observed deleted excursions avoid a prescribed finite family of
  distinguished domino bases.

The last result is a stopped, disintegrated, finite-horizon conditional law.
It does **not** assert HLOZ (6.7): that formula concerns deleted excursions
*before* the level time and conditions on the favorite event itself.  Its proof
still requires a measurable insertion bijection on the fibers of the full
external trace.  A strong Markov restart after the level time cannot replace
that missing disintegration.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace Erdos1165.StoppedInsertion

open LazyDecomposition PathInsertion

local instance : MeasurableSpace (List Point) := ⊤
local instance : MeasurableSingletonClass (List Point) := ⟨fun _ ↦ trivial⟩

/-! ## Prefix statistics and their filtration measurability -/

/-- Extend a finite increment prefix arbitrarily after its last coordinate. -/
def extendPrefix {n : ℕ} (u : Fin n → Direction) : StepPath :=
  fun q ↦ if h : q < n then u ⟨q, h⟩ else 0

/-- The trajectory prefix reconstructed from exactly `n` increments. -/
def trajectoryPrefix {n : ℕ} (u : Fin n → Direction) : Fin (n + 1) → Point :=
  fun j ↦ trajectory (extendPrefix u) j

theorem trajectoryPrefix_stepPrefix (ω : StepPath) (n : ℕ) :
    trajectoryPrefix (stepPrefix n ω) = pathPrefix (trajectory ω) n := by
  funext j
  simp only [trajectoryPrefix, pathPrefix, trajectory]
  apply Finset.sum_congr rfl
  intro q hq
  have hqn : q < n :=
    (Finset.mem_range.mp hq).trans_le (Nat.le_of_lt_succ j.isLt)
  change directionVector (if h : q < n then ω q else 0) = directionVector (ω q)
  simp [hqn]

/-- The threshold count through time `n`, viewed as a function of precisely
the first `n` increments. -/
def thresholdCountPrefix (n m : ℕ) (u : Fin n → Direction) : ℕ :=
  let p := trajectoryPrefix u
  ((visitedPrefix p).filter fun x ↦ m ≤ localTimePrefix p x).card

theorem thresholdCountPrefix_stepPrefix (ω : StepPath) (n m : ℕ) :
    thresholdCountPrefix n m (stepPrefix n ω) = thresholdCount (trajectory ω) n m := by
  simp only [thresholdCountPrefix, thresholdCount, thresholdSites]
  rw [trajectoryPrefix_stepPrefix]
  rfl

/-- Reaching the level/count threshold by deterministic time `n` is observable
from the first `n` increments. -/
theorem measurableSet_thresholdCount_ge (n m k : ℕ) :
    MeasurableSet[incrementFiltration n]
      {ω : StepPath | k ≤ thresholdCount (trajectory ω) n m} := by
  rw [incrementFiltration_apply]
  let C : Set (Fin n → Direction) := {u | k ≤ thresholdCountPrefix n m u}
  have hC : MeasurableSet C := (Set.to_countable C).measurableSet
  have heq : {ω : StepPath | k ≤ thresholdCount (trajectory ω) n m} =
      stepPrefix n ⁻¹' C := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, C]
    rw [thresholdCountPrefix_stepPrefix]
  rw [heq]
  exact ⟨C, hC, rfl⟩

/-! ## The bounded random level clock -/

/-- The HLOZ level clock `T_m^k`, capped at a deterministic time.  On paths
which never reach the threshold, the value is the cutoff. -/
noncomputable def truncatedLevelTime (m k cutoff : ℕ) (ω : StepPath) : ℕ :=
  by
    classical
    exact if h : ReachesThreshold (trajectory ω) m k then min (Nat.find h) cutoff else cutoff

theorem truncatedLevelTime_le (m k cutoff : ℕ) (ω : StepPath) :
    truncatedLevelTime m k cutoff ω ≤ cutoff := by
  classical
  unfold truncatedLevelTime
  split_ifs
  · exact min_le_right _ _
  · exact le_rfl

private theorem find_threshold_le_iff (ω : StepPath) (m k n : ℕ)
    (h : ReachesThreshold (trajectory ω) m k) :
    Nat.find h ≤ n ↔ k ≤ thresholdCount (trajectory ω) n m := by
  constructor
  · intro hle
    exact (Nat.find_spec h).trans (thresholdCount_mono_time (trajectory ω) m hle)
  · exact Nat.find_min' h

theorem truncatedLevelTime_le_iff (m k cutoff n : ℕ) (ω : StepPath) :
    truncatedLevelTime m k cutoff ω ≤ n ↔
      cutoff ≤ n ∨ k ≤ thresholdCount (trajectory ω) n m := by
  classical
  by_cases hcut : cutoff ≤ n
  · constructor
    · intro _
      exact Or.inl hcut
    · intro _
      exact (truncatedLevelTime_le m k cutoff ω).trans hcut
  · have hncut : n < cutoff := Nat.lt_of_not_ge hcut
    unfold truncatedLevelTime
    split_ifs with hreach
    · rw [min_le_iff]
      simp only [hcut, or_false]
      rw [find_threshold_le_iff ω m k n hreach]
      simp only [false_or]
    · have hnot : ¬k ≤ thresholdCount (trajectory ω) n m := by
        intro hn
        exact hreach ⟨n, hn⟩
      simp [Nat.not_le.mpr hncut, hnot]

/-- The capped HLOZ level clock is an honest natural-valued stopping time. -/
theorem isFiniteStoppingTime_truncatedLevelTime (m k cutoff : ℕ) :
    IsFiniteStoppingTime (truncatedLevelTime m k cutoff) := by
  intro n
  have heq : {ω : StepPath |
      (fun ω ↦ (truncatedLevelTime m k cutoff ω : WithTop ℕ)) ω ≤ n} =
      if cutoff ≤ n then Set.univ
      else {ω : StepPath | k ≤ thresholdCount (trajectory ω) n m} := by
    ext ω
    simp only [Set.mem_ofPred_eq]
    norm_cast
    rw [truncatedLevelTime_le_iff]
    by_cases h : cutoff ≤ n <;> simp [h]
  have hrhs : MeasurableSet[incrementFiltration n]
      (if cutoff ≤ n then Set.univ
        else {ω : StepPath | k ≤ thresholdCount (trajectory ω) n m}) := by
    split_ifs
    · exact MeasurableSet.univ
    · exact measurableSet_thresholdCount_ge n m k
  exact heq.symm ▸ hrhs

/-! ## Measurability of deletion and the external clock -/

/-- The finite external trace through ordinary time `n`. -/
def externalTraceAt (o : Orientation) (ω : StepPath) (n : ℕ) : List Point :=
  finiteExternalPath o (pathPrefix (trajectory ω) n)

/-- The finite list of deleted middle points through ordinary time `n`. -/
def deletedTraceAt (o : Orientation) (ω : StepPath) (n : ℕ) : List Point :=
  finiteLazyPoints o (pathPrefix (trajectory ω) n)

/-- The external clock through ordinary time `n`. -/
def externalClockAt (o : Orientation) (ω : StepPath) (n : ℕ) : ℕ :=
  finiteExternalClock o (pathPrefix (trajectory ω) n)

/-- Number of deleted excursions through ordinary time `n`. -/
def deletedExcursionsAt (o : Orientation) (ω : StepPath) (n : ℕ) : ℕ :=
  finiteRemovedExcursions o (pathPrefix (trajectory ω) n)

private theorem measurable_prefixStatistic (n : ℕ) {β : Type*}
    [MeasurableSpace β] [MeasurableSingletonClass β] [Countable β]
    (F : (Fin n → Direction) → β) :
    Measurable fun ω : StepPath ↦ F (stepPrefix n ω) := by
  exact (measurable_of_countable F).comp (measurable_stepPrefix n)

theorem measurable_externalTraceAt (o : Orientation) (n : ℕ) :
    Measurable fun ω ↦ externalTraceAt o ω n := by
  let F : (Fin n → Direction) → List Point := fun u ↦
    finiteExternalPath o (trajectoryPrefix u)
  have hF := measurable_prefixStatistic n F
  convert hF using 1
  funext ω
  simp only [externalTraceAt, F]
  rw [trajectoryPrefix_stepPrefix]

theorem measurable_deletedTraceAt (o : Orientation) (n : ℕ) :
    Measurable fun ω ↦ deletedTraceAt o ω n := by
  let F : (Fin n → Direction) → List Point := fun u ↦
    finiteLazyPoints o (trajectoryPrefix u)
  have hF := measurable_prefixStatistic n F
  convert hF using 1
  funext ω
  simp only [deletedTraceAt, F]
  rw [trajectoryPrefix_stepPrefix]

theorem measurable_externalClockAt (o : Orientation) (n : ℕ) :
    Measurable fun ω ↦ externalClockAt o ω n := by
  let F : (Fin n → Direction) → ℕ := fun u ↦
    finiteExternalClock o (trajectoryPrefix u)
  have hF := measurable_prefixStatistic n F
  convert hF using 1
  funext ω
  simp only [externalClockAt, F]
  rw [trajectoryPrefix_stepPrefix]

theorem measurable_deletedExcursionsAt (o : Orientation) (n : ℕ) :
    Measurable fun ω ↦ deletedExcursionsAt o ω n := by
  let F : (Fin n → Direction) → ℕ := fun u ↦
    finiteRemovedExcursions o (trajectoryPrefix u)
  have hF := measurable_prefixStatistic n F
  convert hF using 1
  funext ω
  simp only [deletedExcursionsAt, F]
  rw [trajectoryPrefix_stepPrefix]

private theorem measurable_stopped_of_measurable {β : Type*}
    [MeasurableSpace β] [MeasurableSingletonClass β] [Countable β]
    {τ : StepPath → ℕ} (hτ : IsFiniteStoppingTime τ)
    (F : ℕ → StepPath → β) (hF : ∀ n, Measurable (F n)) :
    Measurable fun ω ↦ F (τ ω) ω := by
  intro C hC
  have heq : {ω | F (τ ω) ω ∈ C} = ⋃ n, {ω | τ ω = n} ∩ F n ⁻¹' C := by
    ext ω
    simp
  change MeasurableSet {ω | F (τ ω) ω ∈ C}
  rw [heq]
  exact MeasurableSet.iUnion fun n ↦
    (hτ.measurableSet_eq_global n).inter (hF n hC)

/-- External trace stopped at an arbitrary finite stopping time. -/
theorem measurable_stoppedExternalTrace (o : Orientation) {τ : StepPath → ℕ}
    (hτ : IsFiniteStoppingTime τ) :
    Measurable fun ω ↦ externalTraceAt o ω (τ ω) := by
  exact measurable_stopped_of_measurable hτ
    (fun n ω ↦ externalTraceAt o ω n) (measurable_externalTraceAt o)

/-- Deleted trace stopped at an arbitrary finite stopping time. -/
theorem measurable_stoppedDeletedTrace (o : Orientation) {τ : StepPath → ℕ}
    (hτ : IsFiniteStoppingTime τ) :
    Measurable fun ω ↦ deletedTraceAt o ω (τ ω) := by
  exact measurable_stopped_of_measurable hτ
    (fun n ω ↦ deletedTraceAt o ω n) (measurable_deletedTraceAt o)

/-- External clock stopped at an arbitrary finite stopping time. -/
theorem measurable_stoppedExternalClock (o : Orientation) {τ : StepPath → ℕ}
    (hτ : IsFiniteStoppingTime τ) :
    Measurable fun ω ↦ externalClockAt o ω (τ ω) := by
  exact measurable_stopped_of_measurable hτ
    (fun n ω ↦ externalClockAt o ω n) (measurable_externalClockAt o)

/-- Deleted-excursion count stopped at an arbitrary finite stopping time. -/
theorem measurable_stoppedDeletedExcursions (o : Orientation) {τ : StepPath → ℕ}
    (hτ : IsFiniteStoppingTime τ) :
    Measurable fun ω ↦ deletedExcursionsAt o ω (τ ω) := by
  exact measurable_stopped_of_measurable hτ
    (fun n ω ↦ deletedExcursionsAt o ω n) (measurable_deletedExcursionsAt o)

/-- The external clock and deletion count retain their exact pathwise identity
when evaluated at a random finite stopping time. -/
theorem stoppedExternalClock_add_deleted (o : Orientation) (τ : StepPath → ℕ)
    (ω : StepPath) :
    externalClockAt o ω (τ ω) + 2 * deletedExcursionsAt o ω (τ ω) = τ ω := by
  exact finiteExternalClock_eq o (pathPrefix (trajectory ω) (τ ω))

/-! ## Future block statistics after a random level time -/

/-- Pair `2q` directions into `q` two-increment blocks. -/
def pairDirections {q : ℕ} (u : Fin (2 * q) → Direction) : Fin q → Block :=
  fun j ↦ (u ⟨2 * j, by omega⟩, u ⟨2 * j + 1, by omega⟩)

lemma measurable_pairDirections (q : ℕ) : Measurable (@pairDirections q) :=
  measurable_of_countable _

/-- The first `q` two-increment blocks after a finite stopping time. -/
def postStoppingBlocks (τ : StepPath → ℕ) (q : ℕ) (ω : StepPath) : Fin q → Block :=
  pairDirections (postStoppingBlock τ (2 * q) ω)

lemma measurable_postStoppingBlocks {τ : StepPath → ℕ}
    (hτ : IsFiniteStoppingTime τ) (q : ℕ) :
    Measurable (postStoppingBlocks τ q) := by
  exact (measurable_pairDirections q).comp (measurable_postStoppingBlock hτ (2 * q))

/-- Delete removable blocks from a finite future block vector. -/
def futureExternalWord (o : Orientation) {q : ℕ} (u : Fin q → Block) : List Block :=
  deleteRemovableBlocks o (List.ofFn u)

/-- The number of deleted excursions in a finite future block vector. -/
def futureDeletedCount (o : Orientation) {q : ℕ} (u : Fin q → Block) : ℕ :=
  (List.ofFn u).count (removableBlock o)

/-- Base point immediately before future block `j`. -/
def futureBlockBase (x : Point) {q : ℕ} (u : Fin q → Block) (j : Fin q) : Point :=
  (blockPath x (List.ofFn u)).get ⟨2 * j, by simp⟩

/-- No deleted future excursion is based at a distinguished domino.  This is
the precise finite statistic needed when one works away from the favorite
dominoes in the HLOZ screening argument. -/
def awayFromDominoes (o : Orientation) (x : Point) (D : Finset Point)
    {q : ℕ} (u : Fin q → Block) : Prop :=
  ∀ j, u j = removableBlock o → futureBlockBase x u j ∉ D

theorem measurableSet_awayFromDominoes (o : Orientation) (x : Point)
    (D : Finset Point) (q : ℕ) :
    MeasurableSet {u : Fin q → Block | awayFromDominoes o x D u} :=
  (Set.to_countable _).measurableSet

/-- Strong Markov disintegration for paired future blocks. -/
theorem stoppedBlocks_factorization {τ : StepPath → ℕ} (hτ : IsFiniteStoppingTime τ)
    {A : Set StepPath} (hA : IsMeasurableAtStopping τ A) (q : ℕ)
    (C : Set (Fin q → Block)) :
    fairSteps (A ∩ postStoppingBlocks τ q ⁻¹' C) =
      fairSteps A * fairBlock (2 * q) (pairDirections ⁻¹' C) := by
  exact strongMarkov_stoppedEvent_set hτ hA (2 * q) (pairDirections ⁻¹' C)

/-- Conditional quotient form, after imposing a finite truncation event `B`.
The right side is a completely fresh finite-block computation. -/
theorem stoppedBlocks_truncated_conditional {τ : StepPath → ℕ}
    (hτ : IsFiniteStoppingTime τ) {A : Set StepPath}
    (hA : IsMeasurableAtStopping τ A) (q : ℕ)
    (B C : Set (Fin q → Block))
    (hApos : fairSteps A ≠ 0)
    (_hBpos : fairBlock (2 * q) (pairDirections ⁻¹' B) ≠ 0) :
    fairSteps (A ∩ postStoppingBlocks τ q ⁻¹' (B ∩ C)) /
        fairSteps (A ∩ postStoppingBlocks τ q ⁻¹' B) =
      fairBlock (2 * q) (pairDirections ⁻¹' (B ∩ C)) /
        fairBlock (2 * q) (pairDirections ⁻¹' B) := by
  rw [stoppedBlocks_factorization hτ hA q (B ∩ C),
    stoppedBlocks_factorization hτ hA q B]
  rw [ENNReal.mul_div_mul_left]
  · exact hApos
  · exact measure_ne_top fairSteps A

/-- The stopped conditional law specialized to the capped HLOZ level clock,
a cutoff on the number of deleted future excursions, and deletion away from
the distinguished domino bases `D`. -/
theorem truncatedLevel_awayFromDominoes_conditional
    (o : Orientation) (m k cutoff q cap : ℕ) {A : Set StepPath}
    (hA : IsMeasurableAtStopping (truncatedLevelTime m k cutoff) A)
    (hApos : fairSteps A ≠ 0)
    (htruncPos : fairBlock (2 * q)
      (pairDirections ⁻¹' {u : Fin q → Block | futureDeletedCount o u < cap}) ≠ 0)
    (x : Point) (D : Finset Point) :
    fairSteps (A ∩ postStoppingBlocks (truncatedLevelTime m k cutoff) q ⁻¹'
        ({u : Fin q → Block | futureDeletedCount o u < cap} ∩
          {u | awayFromDominoes o x D u})) /
      fairSteps (A ∩ postStoppingBlocks (truncatedLevelTime m k cutoff) q ⁻¹'
        {u : Fin q → Block | futureDeletedCount o u < cap}) =
    fairBlock (2 * q) (pairDirections ⁻¹'
        ({u : Fin q → Block | futureDeletedCount o u < cap} ∩
          {u | awayFromDominoes o x D u})) /
      fairBlock (2 * q) (pairDirections ⁻¹'
        {u : Fin q → Block | futureDeletedCount o u < cap}) := by
  exact stoppedBlocks_truncated_conditional
    (isFiniteStoppingTime_truncatedLevelTime m k cutoff) hA q _ _ hApos htruncPos

end Erdos1165.StoppedInsertion
