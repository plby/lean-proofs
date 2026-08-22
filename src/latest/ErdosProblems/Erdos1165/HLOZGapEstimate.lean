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

import ErdosProblems.Erdos1165.ExternalProposition44Closed
import ErdosProblems.Erdos1165.GreenHarnack
import ErdosProblems.Erdos1165.HLOZPathEvents
import ErdosProblems.Erdos1165.PrefixConditionalLaw
import ErdosProblems.Erdos1165.ScreeningInstantiation
import ErdosProblems.Erdos1165.TwoPointLogAvoidance

/-!
# The path-specific finite screen in HLOZ Lemma 4.10

This file supplies the measure-theoretic bridge between three pieces already
proved elsewhere in the development.

* `ScreeningInstantiation` and `ExternalProposition44` bound the number of
  sites which can be candidates after the external path has been exposed.
* `TwoPointLogAvoidance` gives a uniform probability of avoiding both the
  current candidate and the old favourite for a deterministic future block.
* `Markov` gives the exact finite-dimensional strong Markov factorization.

The important point is that the candidate location is random and observable
at the relevant stopping time.  The first theorem below partitions the
stopped-past event according to this random location, applies strong Markov on
each atom, and sums the atoms.  Consequently the iteration theorem needs no
independence or geometric-tail assumption: its only path input is the literal
stopping-time containment saying that another return forces the next future
block to lie in the complement of the two-point avoidance event.

The last section records the finite path-dependent enumeration used after the
Proposition 4.8 screen.  A random finite set of at most `J` sites is converted
to the fixed candidate type `Fin J`; this is the step needed in order to feed
the concrete path event `HLOZPathEvents.gapDeficitExceptionalEvent` to the
finite union engine in `Gap`.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace Erdos1165
namespace HLOZGapEstimate

open HLOZPathEvents

/-! ## Strong Markov with a stopped-past spatial parameter

The finite conditional laws proved in `PrefixConditionalLaw` are re-exported
here because they are the finite-fibre input used to establish the
observability hypotheses of the spatial strong-Markov lemma below.
-/

export PrefixConditionalLaw
  (EvenPrefixDominoTotals ShiftedPrefixDominoTotals
    evenPrefixTotals_conditional_factorization
    shiftedPrefixTotals_conditional_factorization)

export GreenHarnack
  (annulusOuterExit_ratio_bounds annulusInnerExit_ratio_bounds)

section SpatialStrongMarkov

variable {State : Type*} [Countable State]

/-- Strong Markov with a future block event depending on a countable-valued
stopped-past spatial parameter.

The hypothesis on `A ∩ {location = x}` is the exact disintegration seam:
it says that the candidate location has been determined by the stopped past.
No conditional probability is introduced. -/
theorem strongMarkov_stoppedEvent_spatial_le
    {A : Set StepPath} {location : StepPath → State}
    {τ : StepPath → ℕ} (hτ : IsFiniteStoppingTime τ)
    (k : ℕ) (future : State → Set (Fin k → Direction)) (q : ℝ≥0∞)
    (hobs : ∀ x, IsMeasurableAtStopping τ (A ∩ {w | location w = x}))
    (hfuture : ∀ x, fairBlock k (future x) ≤ q) :
    fairSteps {w | w ∈ A ∧ postStoppingBlock τ k w ∈ future (location w)} ≤
      fairSteps A * q := by
  let piece : State → Set StepPath := fun x ↦
    (A ∩ {w | location w = x}) ∩ postStoppingBlock τ k ⁻¹' future x
  have hunion :
      {w | w ∈ A ∧ postStoppingBlock τ k w ∈ future (location w)} =
        ⋃ x, piece x := by
    ext w
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, piece, Set.mem_inter_iff,
      Set.mem_preimage]
    constructor
    · rintro ⟨hwA, hw⟩
      exact ⟨location w, ⟨hwA, rfl⟩, hw⟩
    · rintro ⟨x, ⟨hwA, hloc⟩, hw⟩
      simpa [hloc] using ⟨hwA, hw⟩
  have hpiece (x : State) :
      fairSteps (piece x) =
        fairSteps (A ∩ {w | location w = x}) * fairBlock k (future x) := by
    exact strongMarkov_stoppedEvent_set hτ (hobs x) k (future x)
  have hmeas (x : State) : MeasurableSet (piece x) := by
    exact (hobs x).measurableSet.inter
      ((measurable_postStoppingBlock hτ k) (Set.to_countable _).measurableSet)
  have hpartMeas (x : State) :
      MeasurableSet (A ∩ {w | location w = x}) :=
    (hobs x).measurableSet
  have hpartDisjoint : Pairwise fun x y : State ↦
      Disjoint (A ∩ {w | location w = x}) (A ∩ {w | location w = y}) := by
    intro x y hxy
    rw [Set.disjoint_left]
    intro w hwx hwy
    exact hxy (hwx.2.symm.trans hwy.2)
  have hpartUnion : (⋃ x, A ∩ {w | location w = x}) = A := by
    ext w
    simp
  rw [hunion]
  calc
    fairSteps (⋃ x, piece x) ≤ ∑' x, fairSteps (piece x) :=
      measure_iUnion_le _
    _ = ∑' x,
        fairSteps (A ∩ {w | location w = x}) * fairBlock k (future x) := by
      congr 1
      funext x
      exact hpiece x
    _ ≤ ∑' x, fairSteps (A ∩ {w | location w = x}) * q := by
      apply ENNReal.tsum_le_tsum
      intro x
      gcongr
      exact hfuture x
    _ = (∑' x, fairSteps (A ∩ {w | location w = x})) * q := by
      rw [ENNReal.tsum_mul_right]
    _ = fairSteps A * q := by
      rw [← measure_iUnion hpartDisjoint hpartMeas, hpartUnion]

end SpatialStrongMarkov

/-! ## The checked geometric-return iteration

`TwoPointReturnCertificate` contains no probability estimate.  Its fields are
the pathwise/stopping-time facts needed to recognize each additional return as
a failure of a fresh two-point avoidance block.  The logarithmic probability
bound and every multiplication in the geometric iteration are proved below.
-/

/-- A pathwise certificate that `returns` successive candidate returns are
screened by fresh two-point avoidance blocks of length `horizon`.

`relativePoint r` is the old favourite translated by the candidate position
at the `r`-th restart.  It may be random, but each of its level sets must be
observable at the corresponding stopping time. -/
structure TwoPointReturnCertificate
    (event : Set WalkPath) (horizon returns : ℕ) where
  stage : ℕ → Set StepPath
  stop : ℕ → StepPath → ℕ
  relativePoint : ℕ → StepPath → Point
  event_subset : trajectory ⁻¹' event ⊆ stage returns
  stage_zero : stage 0 = Set.univ
  stop_isStopping : ∀ r < returns, IsFiniteStoppingTime (stop r)
  spatial_observable : ∀ r < returns, ∀ x,
    IsMeasurableAtStopping (stop r)
      (stage r ∩ {w | relativePoint r w = x})
  next_subset : ∀ r < returns,
    stage (r + 1) ⊆
      {w | w ∈ stage r ∧
        postStoppingBlock (stop r) horizon w ∈
          (TwoPointLogAvoidance.avoidingBlocks (relativePoint r w) horizon)ᶜ}

/-- The complement of a length-`n` two-point avoidance block has probability
at most `1 - 1/(100 log n)`. -/
theorem fairBlock_compl_avoidingBlocks_le
    (x : Point) {n : ℕ} (hn : 2 ≤ n) :
    fairBlock n (TwoPointLogAvoidance.avoidingBlocks x n)ᶜ ≤
      ENNReal.ofReal (1 - 1 / (100 * Real.log n)) := by
  have hlower := TwoPointLogAvoidance.fairSteps_avoidsPair_lower_log x hn
  have hblock : ENNReal.ofReal (1 / (100 * Real.log n)) ≤
      fairBlock n (TwoPointLogAvoidance.avoidingBlocks x n) := by
    have hreal := TwoPointLogAvoidance.fairBlock_avoidingBlocks_toReal x n
    apply (ENNReal.ofReal_le_iff_le_toReal (by finiteness)).2
    rw [hreal]
    exact TwoPointLogAvoidance.avoidanceProbability_lower_one_div_log x hn
  have hp0 : 0 ≤ 1 / (100 * Real.log n) := by
    have hn1 : 1 < n := lt_of_lt_of_le (by omega : 1 < 2) hn
    have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn1)
    positivity
  have hp1 : 1 / (100 * Real.log n) ≤ 1 := by
    have hmeasure : fairBlock n (TwoPointLogAvoidance.avoidingBlocks x n) ≤ 1 := by
      calc
        fairBlock n (TwoPointLogAvoidance.avoidingBlocks x n) ≤
            fairBlock n Set.univ := measure_mono (Set.subset_univ _)
        _ = 1 := measure_univ
    have hcoe : ENNReal.ofReal (1 / (100 * Real.log n)) ≤ 1 :=
      hblock.trans hmeasure
    exact (ENNReal.ofReal_le_one).mp hcoe
  rw [measure_compl (TwoPointLogAvoidance.measurableSet_avoidingBlocks x n)
    (measure_ne_top _ _), measure_univ]
  rw [← ENNReal.ofReal_one, ENNReal.ofReal_sub 1 hp0]
  exact tsub_le_tsub_left hblock _

/-- Strong Markov plus the checked two-point avoidance theorem gives the
complete geometric cost for a path-specific candidate. -/
theorem measure_le_geometricReturnCost_of_twoPointCertificate
    {event : Set WalkPath} {horizon returns : ℕ}
    (hevent : MeasurableSet event) (hn : 2 ≤ horizon)
    (cert : TwoPointReturnCertificate event horizon returns) :
    simpleRandomWalk event ≤
      Gap.geometricReturnCost
        (1 / (100 * Real.log horizon)) returns := by
  let q : ℝ≥0∞ := ENNReal.ofReal (1 - 1 / (100 * Real.log horizon))
  have hstage : ∀ r ≤ returns, fairSteps (cert.stage r) ≤ q ^ r := by
    intro r hr
    induction r with
    | zero =>
        rw [cert.stage_zero]
        simp
    | succ r ih =>
        have hrlt : r < returns := by omega
        have hstep := strongMarkov_stoppedEvent_spatial_le
          (cert.stop_isStopping r hrlt) horizon
          (fun x ↦ (TwoPointLogAvoidance.avoidingBlocks x horizon)ᶜ) q
          (cert.spatial_observable r hrlt)
          (fun x ↦ by
            exact fairBlock_compl_avoidingBlocks_le x hn)
        calc
          fairSteps (cert.stage (r + 1)) ≤
              fairSteps {w | w ∈ cert.stage r ∧
                postStoppingBlock (cert.stop r) horizon w ∈
                  (TwoPointLogAvoidance.avoidingBlocks
                    (cert.relativePoint r w) horizon)ᶜ} :=
            measure_mono (cert.next_subset r hrlt)
          _ ≤ fairSteps (cert.stage r) * q := hstep
          _ ≤ q ^ r * q := by
            gcongr
            exact ih (by omega)
          _ = q ^ (r + 1) := by rw [pow_succ]
  rw [simpleRandomWalk, Measure.map_apply measurable_trajectory hevent]
  calc
    fairSteps (trajectory ⁻¹' event) ≤ fairSteps (cert.stage returns) :=
      measure_mono cert.event_subset
    _ ≤ q ^ returns := hstage returns le_rfl
    _ = Gap.geometricReturnCost
        (1 / (100 * Real.log horizon)) returns := by
      have hp1 : 1 / (100 * Real.log horizon) ≤ 1 := by
        have hlower := TwoPointLogAvoidance.fairSteps_avoidsPair_lower_log
          (0 : Point) hn
        have hmeasure :
            fairSteps (TwoPointLogAvoidance.avoidsPair (0 : Point) horizon) ≤ 1 := by
          calc
            fairSteps (TwoPointLogAvoidance.avoidsPair (0 : Point) horizon) ≤
                fairSteps Set.univ := measure_mono (Set.subset_univ _)
            _ = 1 := measure_univ
        exact ENNReal.ofReal_le_one.mp (hlower.trans hmeasure)
      exact (ENNReal.ofReal_pow (sub_nonneg.mpr hp1) returns).symm

/-! ## A checked stopped return ladder

The certificate above is convenient for the finite union engine, but its
stopping-time fields should not be repeated at every application.  The next
construction supplies the basic clock from a stopped candidate location. -/

/-- The first strict visit to `target` after `σ` and before `deadline`, or the
deadline when there is no such visit. -/
noncomputable def nextVisitBefore (σ : StepPath → ℕ)
    (target : StepPath → Point) (deadline : ℕ) (w : StepPath) : ℕ := by
  classical
  exact if h : ∃ j, j < deadline ∧ σ w < j ∧ trajectory w j = target w then
    Nat.find h
  else deadline

theorem nextVisitBefore_le_deadline (σ : StepPath → ℕ)
    (target : StepPath → Point) (deadline : ℕ) (w : StepPath) :
    nextVisitBefore σ target deadline w ≤ deadline := by
  classical
  unfold nextVisitBefore
  split_ifs with h
  · exact (Nat.find_spec h).1.le
  · exact le_rfl

theorem nextVisitBefore_le_iff {σ : StepPath → ℕ}
    {target : StepPath → Point} {deadline n : ℕ} (hn : n < deadline)
    (w : StepPath) :
    nextVisitBefore σ target deadline w ≤ n ↔
      ∃ j ≤ n, σ w < j ∧ trajectory w j = target w := by
  classical
  constructor
  · intro hle
    unfold nextVisitBefore at hle
    split at hle
    next h =>
      refine ⟨Nat.find h, hle, ?_, ?_⟩
      · exact (Nat.find_spec h).2.1
      · exact (Nat.find_spec h).2.2
    next h => omega
  · rintro ⟨j, hjn, hσj, hj⟩
    have hex : ∃ q, q < deadline ∧ σ w < q ∧ trajectory w q = target w :=
      ⟨j, hjn.trans_lt hn, hσj, hj⟩
    unfold nextVisitBefore
    rw [dif_pos hex]
    exact (Nat.find_min' hex (m := j) ⟨hjn.trans_lt hn, hσj, hj⟩).trans hjn

theorem nextVisitBefore_lt_deadline_iff {σ : StepPath → ℕ}
    {target : StepPath → Point} {deadline : ℕ} (w : StepPath) :
    nextVisitBefore σ target deadline w < deadline ↔
      ∃ j, j < deadline ∧ σ w < j ∧ trajectory w j = target w := by
  classical
  unfold nextVisitBefore
  split_ifs with h
  · exact ⟨fun _ ↦ h, fun _ ↦ (Nat.find_spec h).1⟩
  · constructor
    · intro hlt
      omega
    · intro hex
      exact (h hex).elim

/-- The random target is observable before a deterministic time once it was
observable at an earlier stopping time. -/
theorem measurableSet_targetFiber_inter_stop_lt
    {σ : StepPath → ℕ} {target : StepPath → Point}
    (htarget : ∀ x, IsMeasurableAtStopping σ {w | target w = x})
    (x : Point) (n : ℕ) :
    MeasurableSet[incrementFiltration n]
      ({w | target w = x} ∩ {w | σ w < n}) := by
  have heq :
      {w | target w = x} ∩ {w | σ w < n} =
        ⋃ k : Fin n, ({w | target w = x} ∩ {w | σ w = k}) := by
    ext w
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨hx, hlt⟩
      exact ⟨⟨σ w, hlt⟩, hx, rfl⟩
    · rintro ⟨k, hx, hk⟩
      exact ⟨hx, hk ▸ k.isLt⟩
  rw [heq]
  exact MeasurableSet.iUnion fun k ↦
    incrementFiltration.mono (Nat.le_of_lt k.isLt) _ (htarget x k)

lemma measurable_trajectory_at_incrementFiltration (n : ℕ) :
    Measurable[incrementFiltration n] (fun w : StepPath ↦ trajectory w n) := by
  rw [incrementFiltration_apply]
  have h : Measurable[MeasurableSpace.comap (stepPrefix n) inferInstance]
      (fun w : StepPath ↦ markovBlockDisplacement (stepPrefix n w)) :=
    (measurable_markovBlockDisplacement n).comp (comap_measurable (stepPrefix n))
  simpa only [← trajectory_eq_markovBlockDisplacement_stepPrefix] using h

theorem measurableSet_visitRandomTarget_after
    {σ : StepPath → ℕ} {target : StepPath → Point}
    (htarget : ∀ x, IsMeasurableAtStopping σ {w | target w = x})
    (n : ℕ) :
    MeasurableSet[incrementFiltration n]
      {w | σ w < n ∧ trajectory w n = target w} := by
  have heq : {w | σ w < n ∧ trajectory w n = target w} =
      ⋃ x : Point,
        ({w | target w = x} ∩ {w | σ w < n}) ∩
          {w | trajectory w n = x} := by
    ext w
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · rintro ⟨hσn, htraj⟩
      exact ⟨target w, ⟨rfl, hσn⟩, htraj⟩
    · rintro ⟨x, ⟨htarget, hσn⟩, htraj⟩
      exact ⟨hσn, htraj.trans htarget.symm⟩
  rw [heq]
  exact MeasurableSet.iUnion fun x ↦
    (measurableSet_targetFiber_inter_stop_lt htarget x n).inter
      (measurableSet_eq_fun
        (measurable_trajectory_at_incrementFiltration n) measurable_const)

/-- A first strict visit to a stopped-past random point, capped by a
deterministic deadline, is a finite stopping time. -/
theorem isFiniteStoppingTime_nextVisitBefore
    {σ : StepPath → ℕ} {target : StepPath → Point} {deadline : ℕ}
    (htarget : ∀ x, IsMeasurableAtStopping σ {w | target w = x}) :
    IsFiniteStoppingTime (nextVisitBefore σ target deadline) := by
  intro n
  change MeasurableSet[incrementFiltration n]
    {w | (nextVisitBefore σ target deadline w : WithTop ℕ) ≤ n}
  by_cases hn : deadline ≤ n
  · have heq : {w | (nextVisitBefore σ target deadline w : WithTop ℕ) ≤ n} =
        Set.univ := by
      ext w
      simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      norm_cast
      exact (nextVisitBefore_le_deadline σ target deadline w).trans hn
    rw [heq]
    exact MeasurableSet.univ
  · have hnlt : n < deadline := Nat.lt_of_not_ge hn
    have heq : {w | (nextVisitBefore σ target deadline w : WithTop ℕ) ≤ n} =
        ⋃ j : Fin (n + 1),
          {w | σ w < (j : ℕ) ∧ trajectory w j = target w} := by
      ext w
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
      norm_cast
      rw [nextVisitBefore_le_iff hnlt]
      constructor
      · rintro ⟨j, hjn, hj⟩
        exact ⟨⟨j, Nat.lt_succ_of_le hjn⟩, hj⟩
      · rintro ⟨j, hj⟩
        exact ⟨j, Nat.le_of_lt_succ j.isLt, hj⟩
    rw [heq]
    exact MeasurableSet.iUnion fun j ↦
      incrementFiltration.mono (Nat.le_of_lt_succ j.isLt) _
        (measurableSet_visitRandomTarget_after htarget j)

theorem self_le_nextVisitBefore
    {σ : StepPath → ℕ} {target : StepPath → Point} {deadline : ℕ}
    (hσle : ∀ w, σ w ≤ deadline) (w : StepPath) :
    σ w ≤ nextVisitBefore σ target deadline w := by
  classical
  unfold nextVisitBefore
  split_ifs with h
  · exact (Nat.find_spec h).2.1.le
  · exact hσle w

/-- A stopped-past event remains stopped-past observable at any later finite
stopping time. -/
theorem IsMeasurableAtStopping.mono_time
    {σ τ : StepPath → ℕ} {A : Set StepPath}
    (hA : IsMeasurableAtStopping σ A)
    (hτ : IsFiniteStoppingTime τ) (hστ : ∀ w, σ w ≤ τ w) :
    IsMeasurableAtStopping τ A := by
  intro n
  have heq : A ∩ {w | τ w = n} =
      ⋃ k : Fin (n + 1), (A ∩ {w | σ w = k}) ∩ {w | τ w = n} := by
    ext w
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨hAw, hτw⟩
      have hσn : σ w ≤ n := hτw ▸ hστ w
      exact ⟨⟨σ w, Nat.lt_succ_of_le hσn⟩, ⟨hAw, rfl⟩, hτw⟩
    · rintro ⟨k, ⟨hAw, _⟩, hτw⟩
      exact ⟨hAw, hτw⟩
  rw [heq]
  exact MeasurableSet.iUnion fun k ↦
    (incrementFiltration.mono (Nat.le_of_lt_succ k.isLt) _ (hA k)).inter
      (hτ.measurableSet_eq n)

/-- Successive strict visits to one stopped-past random target, all capped at
the same deterministic deadline. -/
noncomputable def returnLadder (σ : StepPath → ℕ)
    (target : StepPath → Point) (deadline : ℕ) : ℕ → StepPath → ℕ
  | 0 => σ
  | r + 1 => nextVisitBefore (returnLadder σ target deadline r) target deadline

@[simp] theorem returnLadder_zero (σ : StepPath → ℕ)
    (target : StepPath → Point) (deadline : ℕ) :
    returnLadder σ target deadline 0 = σ := rfl

theorem returnLadder_succ (σ : StepPath → ℕ)
    (target : StepPath → Point) (deadline r : ℕ) :
    returnLadder σ target deadline (r + 1) =
      nextVisitBefore (returnLadder σ target deadline r) target deadline := rfl

theorem returnLadder_le_deadline
    {σ : StepPath → ℕ} {target : StepPath → Point} {deadline : ℕ}
    (hσle : ∀ w, σ w ≤ deadline) (r : ℕ) (w : StepPath) :
    returnLadder σ target deadline r w ≤ deadline := by
  cases r with
  | zero => exact hσle w
  | succ r => exact nextVisitBefore_le_deadline _ _ _ _

theorem returnLadder_mono_step
    {σ : StepPath → ℕ} {target : StepPath → Point} {deadline r : ℕ}
    (hσle : ∀ w, σ w ≤ deadline) (w : StepPath) :
    returnLadder σ target deadline r w ≤
      returnLadder σ target deadline (r + 1) w := by
  rw [returnLadder_succ]
  exact self_le_nextVisitBefore
    (fun v ↦ returnLadder_le_deadline hσle r v) w

theorem returnLadder_base_le
    {σ : StepPath → ℕ} {target : StepPath → Point} {deadline : ℕ}
    (hσle : ∀ w, σ w ≤ deadline) (r : ℕ) (w : StepPath) :
    σ w ≤ returnLadder σ target deadline r w := by
  induction r with
  | zero => exact le_rfl
  | succ r ih => exact ih.trans (returnLadder_mono_step hσle w)

theorem returnLadder_isFiniteStoppingTime
    {σ : StepPath → ℕ} {target : StepPath → Point} {deadline : ℕ}
    (hσ : IsFiniteStoppingTime σ) (hσle : ∀ w, σ w ≤ deadline)
    (htarget : ∀ x, IsMeasurableAtStopping σ {w | target w = x}) :
    ∀ r, IsFiniteStoppingTime (returnLadder σ target deadline r) := by
  intro r
  induction r with
  | zero => exact hσ
  | succ r ih =>
      apply isFiniteStoppingTime_nextVisitBefore
      intro x
      exact IsMeasurableAtStopping.mono_time (htarget x) ih
        (returnLadder_base_le hσle r)

theorem returnLadder_target_observable
    {σ : StepPath → ℕ} {target : StepPath → Point} {deadline : ℕ}
    (hσ : IsFiniteStoppingTime σ) (hσle : ∀ w, σ w ≤ deadline)
    (htarget : ∀ x, IsMeasurableAtStopping σ {w | target w = x})
    (r : ℕ) (x : Point) :
    IsMeasurableAtStopping (returnLadder σ target deadline r)
      {w | target w = x} :=
  IsMeasurableAtStopping.mono_time (htarget x)
    (returnLadder_isFiniteStoppingTime hσ hσle htarget r)
    (returnLadder_base_le hσle r)

/-- The stage saying that `r` strict returns have occurred.  Stage zero is
all paths, as required by `TwoPointReturnCertificate`. -/
def returnLadderStage (σ : StepPath → ℕ) (target : StepPath → Point)
    (deadline : ℕ) : ℕ → Set StepPath
  | 0 => Set.univ
  | r + 1 => {w | returnLadder σ target deadline (r + 1) w < deadline}

@[simp] theorem returnLadderStage_zero (σ : StepPath → ℕ)
    (target : StepPath → Point) (deadline : ℕ) :
    returnLadderStage σ target deadline 0 = Set.univ := rfl

theorem returnLadderStage_observable
    {σ : StepPath → ℕ} {target : StepPath → Point} {deadline r : ℕ}
    (hσ : IsFiniteStoppingTime σ) (hσle : ∀ w, σ w ≤ deadline)
    (htarget : ∀ x, IsMeasurableAtStopping σ {w | target w = x}) :
    IsMeasurableAtStopping (returnLadder σ target deadline r)
      (returnLadderStage σ target deadline r) := by
  intro n
  cases r with
  | zero =>
      simpa using
        (returnLadder_isFiniteStoppingTime hσ hσle htarget 0).measurableSet_eq n
  | succ r =>
      by_cases hn : n < deadline
      · have heq :
          returnLadderStage σ target deadline (r + 1) ∩
              {w | returnLadder σ target deadline (r + 1) w = n} =
            {w | returnLadder σ target deadline (r + 1) w = n} := by
          ext w
          simp only [returnLadderStage, Set.mem_inter_iff, Set.mem_ofPred_eq]
          constructor
          · exact fun h ↦ h.2
          · intro hstop
            exact ⟨hstop ▸ hn, hstop⟩
        rw [heq]
        exact (returnLadder_isFiniteStoppingTime hσ hσle htarget
          (r + 1)).measurableSet_eq n
      · have heq :
          returnLadderStage σ target deadline (r + 1) ∩
              {w | returnLadder σ target deadline (r + 1) w = n} = ∅ := by
          ext w
          simp only [returnLadderStage, Set.mem_inter_iff, Set.mem_ofPred_eq,
            Set.mem_empty_iff_false, iff_false, not_and]
          intro _ hnstop
          omega
        rw [heq]
        exact (incrementFiltration n).measurableSet_empty

theorem returnLadderStage_targetFiber_observable
    {σ : StepPath → ℕ} {target : StepPath → Point} {deadline r : ℕ}
    (hσ : IsFiniteStoppingTime σ) (hσle : ∀ w, σ w ≤ deadline)
    (htarget : ∀ x, IsMeasurableAtStopping σ {w | target w = x})
    (x : Point) :
    IsMeasurableAtStopping (returnLadder σ target deadline r)
      (returnLadderStage σ target deadline r ∩
        {_w : StepPath | (0 : Point) = x}) := by
  by_cases hx : (0 : Point) = x
  · simpa [hx] using returnLadderStage_observable hσ hσle htarget
  · have heq :
        returnLadderStage σ target deadline r ∩
          {_w : StepPath | (0 : Point) = x} = ∅ := by
      ext w
      simp [hx]
    rw [heq]
    intro n
    change MeasurableSet[incrementFiltration n]
      ((∅ : Set StepPath) ∩ {w | returnLadder σ target deadline r w = n})
    rw [Set.empty_inter]
    exact (incrementFiltration n).measurableSet_empty

/-! ## Enumerating a random finite candidate set by fixed slots -/

section CandidateEnumeration

variable {Site Band : Type*}

/-- The `i`-th element of a finite set, or `none` when `i` is outside the
set.  The particular `Fintype.equivFin` order is immaterial; only the two
membership lemmas below are used. -/
noncomputable def finsetSlot (S : Finset Site) (i : ℕ) : Option Site :=
  if hi : i < S.card then
    some ((S.equivFin.symm ⟨i, hi⟩ : S) : Site)
  else none

theorem finsetSlot_eq_some_mem {S : Finset Site} {i : ℕ} {x : Site}
    (h : finsetSlot S i = some x) : x ∈ S := by
  classical
  unfold finsetSlot at h
  split at h
  · have heq : ((S.equivFin.symm ⟨i, by assumption⟩ : S) : Site) = x :=
      Option.some.inj h
    rw [← heq]
    exact (S.equivFin.symm ⟨i, by assumption⟩ : S).property
  · simp at h

/-- Every member occurs in a slot strictly below the cardinality. -/
theorem exists_finsetSlot_eq_some {S : Finset Site} {x : Site} (hx : x ∈ S) :
    ∃ i < S.card, finsetSlot S i = some x := by
  classical
  let y : S := ⟨x, hx⟩
  let i : Fin S.card := S.equivFin y
  refine ⟨i, i.isLt, ?_⟩
  simp only [finsetSlot, dif_pos i.isLt, Option.some.injEq]
  change ((S.equivFin.symm i : S) : Site) = x
  have hi : S.equivFin.symm i = y := by
    exact S.equivFin.symm_apply_apply y
  exact congrArg Subtype.val hi

/-- A path has a candidate overflow if one of the finitely many bands has
more candidates than its allotted slot budget. -/
def candidateOverflow (bands : Finset Band)
    (sites : WalkPath → Band → Finset Site) (budget : Band → ℕ) :
    Set WalkPath :=
  {s | ∃ band ∈ bands, budget band < (sites s band).card}

/-- The event that the candidate occupying slot `i` realizes the indicated
path property. -/
def slotSuccessEvent (sites : WalkPath → Band → Finset Site)
    (realizes : WalkPath → Band → Site → Prop) (band : Band) (i : ℕ) :
    Set WalkPath :=
  {s | ∃ x, finsetSlot (sites s band) i = some x ∧ realizes s band x}

/-- The deterministic content of the deficit-band decomposition: off the
candidate overflow, every path in the target gap event has a realizing site
in one of the displayed candidate sets. -/
def PathGapWitness (gapEvent : Set WalkPath) (bands : Finset Band)
    (sites : WalkPath → Band → Finset Site) (budget : Band → ℕ)
    (realizes : WalkPath → Band → Site → Prop) : Prop :=
  ∀ s, s ∈ gapEvent → s ∉ candidateOverflow bands sites budget →
    ∃ band ∈ bands, ∃ x ∈ sites s band, realizes s band x

/-- The path-dependent enumeration becomes a `GapEventCovered` statement
with the fixed candidate type `ℕ` and candidate set `range (budget band)`.
This is the stopping-time enumeration step in Lemma 4.10. -/
theorem gapEvent_diff_overflow_covered_by_slots
    (gapEvent : Set WalkPath) (bands : Finset Band)
    (sites : WalkPath → Band → Finset Site) (budget : Band → ℕ)
    (realizes : WalkPath → Band → Site → Prop)
    (hwitness : PathGapWitness gapEvent bands sites budget realizes) :
    Gap.GapEventCovered
      (gapEvent \ candidateOverflow bands sites budget) bands
      (fun band ↦ Finset.range (budget band))
      (slotSuccessEvent sites realizes) := by
  intro s hs
  obtain ⟨band, hband, x, hx, hrealizes⟩ := hwitness s hs.1 hs.2
  have hcard : (sites s band).card ≤ budget band := by
    by_contra hnot
    apply hs.2
    exact ⟨band, hband, Nat.lt_of_not_ge hnot⟩
  obtain ⟨i, hi, hslot⟩ := exists_finsetSlot_eq_some hx
  rw [Gap.mem_someGapCandidateSucceeds]
  exact ⟨band, hband, i, Finset.mem_range.mpr (hi.trans_le hcard), x,
    hslot, hrealizes⟩

theorem range_candidateCountBound (bands : Finset Band) (budget : Band → ℕ) :
    Gap.CandidateCountBound bands
      (fun band ↦ Finset.range (budget band)) budget := by
  intro band hband
  simp

/-- The path-specific strong-Markov certificate discharges the entire
per-slot geometric-return premise of the finite `Gap` engine. -/
theorem perCandidateGeometricReturnBound_of_twoPointCertificates
    (bands : Finset Band) (sites : WalkPath → Band → Finset Site)
    (budget horizon returns : Band → ℕ)
    (realizes : WalkPath → Band → Site → Prop)
    (hmeas : ∀ band i, MeasurableSet (slotSuccessEvent sites realizes band i))
    (hhorizon : ∀ band ∈ bands, 2 ≤ horizon band)
    (hcertificate : ∀ band ∈ bands, ∀ i ∈ Finset.range (budget band),
      TwoPointReturnCertificate
        (slotSuccessEvent sites realizes band i) (horizon band) (returns band)) :
    Gap.PerCandidateGeometricReturnBound simpleRandomWalk bands
      (fun band ↦ Finset.range (budget band))
      (slotSuccessEvent sites realizes)
      (fun band ↦ 1 / (100 * Real.log (horizon band))) returns := by
  intro band hband i hi
  exact measure_le_geometricReturnCost_of_twoPointCertificate
    (hmeas band i) (hhorizon band hband)
    (hcertificate band hband i hi)

/-- Full path-specific finite-screen estimate.  Candidate enumeration and
geometric iteration have both been discharged; the displayed overflow is the
event estimated by Proposition 4.8. -/
theorem measure_gapDeficitExceptionalEvent_le_overflow_add_geometric
    (t : DominoTiling) (m : ℕ) (bands : Finset Band)
    (sites : WalkPath → Band → Finset Site)
    (budget horizon returns : Band → ℕ)
    (realizes : WalkPath → Band → Site → Prop)
    (hwitness : PathGapWitness (gapDeficitExceptionalEvent t m)
      bands sites budget realizes)
    (hmeas : ∀ band i, MeasurableSet (slotSuccessEvent sites realizes band i))
    (hhorizon : ∀ band ∈ bands, 2 ≤ horizon band)
    (hcertificate : ∀ band ∈ bands, ∀ i ∈ Finset.range (budget band),
      TwoPointReturnCertificate
        (slotSuccessEvent sites realizes band i) (horizon band) (returns band)) :
    simpleRandomWalk (gapDeficitExceptionalEvent t m) ≤
      simpleRandomWalk (candidateOverflow bands sites budget) +
        ∑ band ∈ bands, (budget band : ℝ≥0∞) *
          Gap.geometricReturnCost
            (1 / (100 * Real.log (horizon band))) (returns band) := by
  let overflow := candidateOverflow bands sites budget
  let screened := gapDeficitExceptionalEvent t m \ overflow
  have hsplit : gapDeficitExceptionalEvent t m ⊆ overflow ∪ screened := by
    intro s hs
    by_cases ho : s ∈ overflow
    · exact Or.inl ho
    · exact Or.inr ⟨hs, ho⟩
  calc
    simpleRandomWalk (gapDeficitExceptionalEvent t m) ≤
        simpleRandomWalk (overflow ∪ screened) := measure_mono hsplit
    _ ≤ simpleRandomWalk overflow + simpleRandomWalk screened :=
      measure_union_le _ _
    _ ≤ simpleRandomWalk overflow +
        ∑ band ∈ bands, (budget band : ℝ≥0∞) *
          Gap.geometricReturnCost
            (1 / (100 * Real.log (horizon band))) (returns band) := by
      gcongr
      exact Gap.measure_gapEvent_le_geometric_sum simpleRandomWalk screened bands
        (fun band ↦ Finset.range (budget band))
        (slotSuccessEvent sites realizes) budget
        (fun band ↦ 1 / (100 * Real.log (horizon band))) returns
        (by
          dsimp only [screened, overflow]
          exact gapEvent_diff_overflow_covered_by_slots
            (gapDeficitExceptionalEvent t m) bands sites budget realizes hwitness)
        (range_candidateCountBound bands budget)
        (perCandidateGeometricReturnBound_of_twoPointCertificates bands sites
          budget horizon returns realizes hmeas hhorizon hcertificate)

end CandidateEnumeration

/-! ## The concrete external-thick candidate screen -/

open LazyDecomposition

/-- The path-dependent candidate set at the exact Proposition 4.4 cutoff and
thickness level. -/
noncomputable def externalCandidateSites44 (o : Orientation) (m : ℕ)
    (distinguished : WalkPath → Finset Point) (s : WalkPath) : Finset Point :=
  ScreeningInstantiation.externalThickCandidates o
    (ExternalProposition44.hlozCutoff44 m)
    (ExternalProposition44.hlozThickLevel44 m) distinguished s

def externalCandidateOverflow44 (o : Orientation) (m : ℕ)
    (distinguished : WalkPath → Finset Point) : Set WalkPath :=
  {s | ExternalProposition44.hlozSiteBudget44 m <
    (externalCandidateSites44 o m distinguished s).card}

/-- Off the displayed overflow, the concrete random candidate set fits in
the Proposition 4.4 slot budget. -/
theorem externalCandidateSites44_card_le_of_not_overflow
    {o : Orientation} {m : ℕ} {distinguished : WalkPath → Finset Point}
    {s : WalkPath} (hs : s ∉ externalCandidateOverflow44 o m distinguished) :
    (externalCandidateSites44 o m distinguished s).card ≤
      ExternalProposition44.hlozSiteBudget44 m := by
  exact Nat.le_of_not_gt hs

/-- Candidate overflow is contained in the oriented external thick-count
overflow, independently of the distinguished set. -/
theorem externalCandidateOverflow44_subset_orientedThickCount
    (o : Orientation) (m : ℕ) (distinguished : WalkPath → Finset Point) :
    externalCandidateOverflow44 o m distinguished ⊆
      {s | ExternalProposition44.hlozSiteBudget44 m <
        ExternalThickCount.orientedExternalThickCount o s
          (ExternalProposition44.hlozCutoff44 m)
          (ExternalProposition44.hlozThickLevel44 m)} := by
  intro s hs
  exact hs.trans_le
    (ScreeningInstantiation.externalThickCandidates_card_le o
      (ExternalProposition44.hlozCutoff44 m)
      (ExternalProposition44.hlozThickLevel44 m) distinguished s)

/-- Exact path-to-external-chain disintegration still needed to apply the
IID external-chain Proposition 4.4 estimate to the canonical stopped path.
This is a transport statement, not the desired gap estimate. -/
def ExternalCountTransport44 (o : Orientation) (m : ℕ) : Prop :=
  simpleRandomWalk {s |
      ExternalProposition44.hlozSiteBudget44 m <
        ExternalThickCount.orientedExternalThickCount o s
          (ExternalProposition44.hlozCutoff44 m)
          (ExternalProposition44.hlozThickLevel44 m)} ≤
    ExternalWalk.externalBlocks o {η |
      ExternalProposition44.hlozSiteBudget44 m <
        ExternalProposition44.externalThickCount o η
          (ExternalProposition44.hlozCutoff44 m)
          (ExternalProposition44.hlozThickLevel44 m)}

/-- Proposition 4.4 supplies the candidate-count probability once the exact
external-chain transport has been established.  No candidate-count bound is
left as a hypothesis. -/
theorem eventually_externalCandidateOverflow44_lt_failureRate
    (o : Orientation) (distinguished : ℕ → WalkPath → Finset Point)
    (htransport : ∀ᶠ m : ℕ in atTop, ExternalCountTransport44 o m) :
    ∀ᶠ m : ℕ in atTop,
      simpleRandomWalk (externalCandidateOverflow44 o m (distinguished m)) <
        ExternalProposition44.hlozFailureRate44 m := by
  filter_upwards [htransport,
      ExternalProposition44Closed.eventually_hloz_externalThickCount_failure44 o]
      with m htransportM hcount
  exact (measure_mono
    (externalCandidateOverflow44_subset_orientedThickCount o m
      (distinguished m))).trans_lt (htransportM.trans_lt hcount)

section OrientedCandidateScreen

variable {Band : Type*}

/-- Proposition 4.4 candidates for a family of deficit bands.  The parity
orientation is part of the band data, exactly as in the two-deletion argument
of HLOZ. -/
noncomputable def orientedCandidateSites44 (orientation : Band → Orientation)
    (m : ℕ) (distinguished : Orientation → WalkPath → Finset Point)
    (s : WalkPath) (band : Band) : Finset Point :=
  externalCandidateSites44 (orientation band) m
    (distinguished (orientation band)) s

def orientedCandidateOverflow44 (bands : Finset Band)
    (orientation : Band → Orientation) (m : ℕ)
    (distinguished : Orientation → WalkPath → Finset Point) : Set WalkPath :=
  candidateOverflow bands (orientedCandidateSites44 orientation m distinguished)
    (fun _ ↦ ExternalProposition44.hlozSiteBudget44 m)

/-- Any band overflow lies in one of the two external-chain overflow events.
Thus the number of bands does not enter the Proposition 4.4 cost. -/
theorem orientedCandidateOverflow44_subset_two_orientations
    (bands : Finset Band) (orientation : Band → Orientation) (m : ℕ)
    (distinguished : Orientation → WalkPath → Finset Point) :
    orientedCandidateOverflow44 bands orientation m distinguished ⊆
      externalCandidateOverflow44 .even m (distinguished .even) ∪
        externalCandidateOverflow44 .shifted m (distinguished .shifted) := by
  intro s hs
  obtain ⟨band, hband, hcard⟩ := hs
  cases h : orientation band with
  | even =>
      apply Or.inl
      simpa [orientedCandidateSites44, externalCandidateOverflow44, h] using hcard
  | shifted =>
      apply Or.inr
      simpa [orientedCandidateSites44, externalCandidateOverflow44, h] using hcard

/-- The checked Proposition 4.4 count for all path-dependent candidate bands.
Only the two path-to-external-chain transports and the sharp one-point tails
remain; finite enumeration and the union over orientations are internal. -/
theorem eventually_orientedCandidateOverflow44_lt_two_failureRates
    (bands : ℕ → Finset Band) (orientation : Band → Orientation)
    (distinguished : ℕ → Orientation → WalkPath → Finset Point)
    (htransportEven : ∀ᶠ m : ℕ in atTop, ExternalCountTransport44 .even m)
    (htransportShifted : ∀ᶠ m : ℕ in atTop,
      ExternalCountTransport44 .shifted m) :
    ∀ᶠ m : ℕ in atTop,
      simpleRandomWalk
          (orientedCandidateOverflow44 (bands m) orientation m (distinguished m)) <
        ExternalProposition44.hlozFailureRate44 m +
          ExternalProposition44.hlozFailureRate44 m := by
  have heven := eventually_externalCandidateOverflow44_lt_failureRate .even
    (fun m ↦ distinguished m .even) htransportEven
  have hshifted := eventually_externalCandidateOverflow44_lt_failureRate .shifted
    (fun m ↦ distinguished m .shifted) htransportShifted
  filter_upwards [heven, hshifted] with m hevenM hshiftedM
  calc
    simpleRandomWalk
        (orientedCandidateOverflow44 (bands m) orientation m (distinguished m)) ≤
      simpleRandomWalk
          (externalCandidateOverflow44 .even m (distinguished m .even) ∪
            externalCandidateOverflow44 .shifted m
              (distinguished m .shifted)) :=
        measure_mono (orientedCandidateOverflow44_subset_two_orientations
          (bands m) orientation m (distinguished m))
    _ ≤ simpleRandomWalk
          (externalCandidateOverflow44 .even m (distinguished m .even)) +
        simpleRandomWalk
          (externalCandidateOverflow44 .shifted m (distinguished m .shifted)) :=
      measure_union_le _ _
    _ < ExternalProposition44.hlozFailureRate44 m +
        ExternalProposition44.hlozFailureRate44 m :=
      ENNReal.add_lt_add hevenM hshiftedM

end OrientedCandidateScreen

end HLOZGapEstimate
end Erdos1165
