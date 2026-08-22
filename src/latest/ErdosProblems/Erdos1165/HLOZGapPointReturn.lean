/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
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

import ErdosProblems.Erdos1165.HLOZGapStoppedCandidate
import ErdosProblems.Erdos1165.PointBeforeReturn
import ErdosProblems.Erdos1165.StrongMarkovFullTail

/-!
# Sharp point-before-return iteration for HLOZ Lemma 4.10

The finite-horizon two-point avoidance estimate gives only an escape chance
of order the inverse logarithm of the global level-time cutoff.  HLOZ Lemma
4.10 needs the sharper inverse logarithm of the distance between the new
candidate and the preceding favorite.

`PointBeforeReturn` proves the exact identity

`P_0(H_x < H_0^+) = 1 / (2 a(x))`

and its explicit logarithmic lower bound.  `StrongMarkovFullTail` makes that
infinite future event available after a random finite stopping time.  This
file supplies the remaining countable spatial disintegration and geometric
iteration.  Its certificate contains only pathwise facts: every additional
candidate return occurs on a fresh tail which did not first hit the old
favorite.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace Erdos1165.HLOZGapPointReturn

open HLOZGapEstimate HLOZGapReturn HLOZGapStoppedCandidate
open PointBeforeReturn

noncomputable section

/-! ## Full-tail spatial strong Markov -/

/-- Strong Markov for a measurable full-tail event depending on a countable
stopped-past spatial parameter. -/
theorem strongMarkov_fullTail_spatial_le
    {State : Type*} [Countable State]
    {A : Set StepPath} {location : StepPath → State}
    {tau : StepPath → ℕ} (htau : IsFiniteStoppingTime tau)
    (future : State → Set StepPath) (q : ℝ≥0∞)
    (hobs : ∀ x, IsMeasurableAtStopping tau
      (A ∩ {w | location w = x}))
    (hmeas : ∀ x, MeasurableSet (future x))
    (hfuture : ∀ x, (A ∩ {w | location w = x}).Nonempty →
      fairSteps (future x) ≤ q) :
    fairSteps {w | w ∈ A ∧
        postStoppingSteps tau w ∈ future (location w)} ≤
      fairSteps A * q := by
  rw [strongMarkov_fullTail_countable_partition htau location hobs future hmeas]
  calc
    ∑' x, fairSteps (A ∩ {w | location w = x}) * fairSteps (future x) ≤
        ∑' x, fairSteps (A ∩ {w | location w = x}) * q := by
      apply ENNReal.tsum_le_tsum
      intro x
      by_cases hx : (A ∩ {w | location w = x}).Nonempty
      · gcongr
        exact hfuture x hx
      · have hempty : A ∩ {w | location w = x} = ∅ := Set.not_nonempty_iff_eq_empty.mp hx
        rw [hempty]
        simp
    _ = (∑' x, fairSteps (A ∩ {w | location w = x})) * q := by
      rw [ENNReal.tsum_mul_right]
    _ = fairSteps A * q := by
      have hpartDisjoint : Pairwise fun x y : State ↦
          Disjoint (A ∩ {w | location w = x})
            (A ∩ {w | location w = y}) := by
        intro x y hxy
        rw [Set.disjoint_left]
        intro w hwx hwy
        exact hxy (hwx.2.symm.trans hwy.2)
      have hpartMeas (x : State) :
          MeasurableSet (A ∩ {w | location w = x}) :=
        (hobs x).measurableSet
      have hpartUnion : (⋃ x, A ∩ {w | location w = x}) = A := by
        ext w
        simp
      rw [← measure_iUnion hpartDisjoint hpartMeas, hpartUnion]

/-! ## Stopped-past spatial observables -/

/-- Stopped-past observability is closed under intersections. -/
theorem isMeasurableAtStopping_inter
    {tau : StepPath → ℕ} {A B : Set StepPath}
    (hA : IsMeasurableAtStopping tau A)
    (hB : IsMeasurableAtStopping tau B) :
    IsMeasurableAtStopping tau (A ∩ B) := by
  intro n
  have heq : (A ∩ B) ∩ {w | tau w = n} =
      (A ∩ {w | tau w = n}) ∩ (B ∩ {w | tau w = n}) := by
    ext w
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
    tauto
  rw [heq]
  exact (hA n).inter (hB n)

/-- Stopped-past observability is closed under complements. -/
theorem isMeasurableAtStopping_compl
    {tau : StepPath → ℕ} {A : Set StepPath}
    (htau : IsFiniteStoppingTime tau)
    (hA : IsMeasurableAtStopping tau A) :
    IsMeasurableAtStopping tau Aᶜ := by
  intro n
  have heq : Aᶜ ∩ {w | tau w = n} =
      {w | tau w = n} \ (A ∩ {w | tau w = n}) := by
    ext w
    simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_ofPred_eq,
      Set.mem_sdiff]
    tauto
  rw [heq]
  exact (htau.measurableSet_eq n).diff (hA n)

/-- A binary function of two countable stopped-past observables is again a
stopped-past observable, in the atomwise fiber form needed by spatial strong
Markov. -/
theorem isMeasurableAtStopping_binary_fiber
    {X Y Z : Type*} [Countable X] [Countable Y]
    {tau : StepPath → ℕ} {left : StepPath → X} {right : StepPath → Y}
    (hleft : ∀ x, IsMeasurableAtStopping tau {w | left w = x})
    (hright : ∀ y, IsMeasurableAtStopping tau {w | right w = y})
    (op : X → Y → Z) (z : Z) :
    IsMeasurableAtStopping tau {w | op (left w) (right w) = z} := by
  intro n
  have heq :
      {w | op (left w) (right w) = z} ∩ {w | tau w = n} =
        ⋃ x : X, ⋃ y : Y, ⋃ (_hxy : op x y = z),
          ({w | left w = x} ∩ {w | tau w = n}) ∩
            ({w | right w = y} ∩ {w | tau w = n}) := by
    ext w
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨hop, htau⟩
      exact ⟨left w, right w, hop, ⟨rfl, htau⟩, rfl, htau⟩
    · rintro ⟨x, y, hxy, ⟨hl, htau⟩, hr, _⟩
      exact ⟨hl ▸ hr ▸ hxy, htau⟩
  rw [heq]
  exact MeasurableSet.iUnion fun x ↦ MeasurableSet.iUnion fun y ↦
    MeasurableSet.iUnion fun _hxy ↦ (hleft x n).inter (hright y n)

/-- There is no visit to `old` strictly after the stopped past and through
the terminal clock.  This includes the terminal endpoint. -/
def noOldVisitThrough (past terminal : StepPath → ℕ)
    (old : StepPath → Point) : Set StepPath :=
  {w | ∀ q, past w < q → q ≤ terminal w → trajectory w q ≠ old w}

/-- Avoiding a stopped-past random site through a later finite stopping time
is observable at the later clock. -/
theorem noOldVisitThrough_observable
    {past terminal : StepPath → ℕ} {old : StepPath → Point}
    (hterminal : IsFiniteStoppingTime terminal)
    (hpast_le : ∀ w, past w ≤ terminal w)
    (hold : ∀ x, IsMeasurableAtStopping past {w | old w = x}) :
    IsMeasurableAtStopping terminal (noOldVisitThrough past terminal old) := by
  intro n
  have heq : noOldVisitThrough past terminal old ∩ {w | terminal w = n} =
      ⋃ p : Fin (n + 1), ⋃ x : Point,
        (({w | old w = x} ∩ {w | past w = (p : ℕ)}) ∩
          (⋂ q : Fin (n + 1), ⋂ (_hpq : (p : ℕ) < (q : ℕ)),
            {w | trajectory w (q : ℕ) ≠ x})) ∩
          {w | terminal w = n} := by
    ext w
    simp only [noOldVisitThrough, Set.mem_inter_iff, Set.mem_ofPred_eq,
      Set.mem_iUnion, Set.mem_iInter]
    constructor
    · rintro ⟨havoid, hterm⟩
      have hpastn : past w ≤ n := hterm ▸ hpast_le w
      refine ⟨⟨past w, Nat.lt_succ_of_le hpastn⟩, old w,
        ⟨⟨rfl, rfl⟩, ?_⟩, hterm⟩
      intro q hpq
      exact havoid (q : ℕ) hpq (by
        simpa only [hterm] using Nat.le_of_lt_succ q.isLt)
    · rintro ⟨p, x, ⟨⟨holdx, hpast⟩, havoid⟩, hterm⟩
      refine ⟨?_, hterm⟩
      intro q hpq hq
      have hqn : q ≤ n := hterm ▸ hq
      have hqmem : q < n + 1 := Nat.lt_succ_of_le hqn
      have hpq' : (p : ℕ) < q := by simpa only [hpast] using hpq
      have := havoid ⟨q, hqmem⟩ hpq'
      simpa only [holdx] using this
  rw [heq]
  apply MeasurableSet.iUnion
  intro p
  apply MeasurableSet.iUnion
  intro x
  have holdPast : MeasurableSet[incrementFiltration n]
      ({w | old w = x} ∩ {w | past w = (p : ℕ)}) :=
    incrementFiltration.mono (Nat.le_of_lt_succ p.isLt) _ (hold x p)
  have havoid : MeasurableSet[incrementFiltration n]
      (⋂ q : Fin (n + 1), ⋂ (_hpq : (p : ℕ) < (q : ℕ)),
        {w | trajectory w (q : ℕ) ≠ x}) := by
    apply MeasurableSet.iInter
    intro q
    apply MeasurableSet.iInter
    intro _hpq
    exact incrementFiltration.mono (Nat.le_of_lt_succ q.isLt) _
      ((measurableSet_eq_fun
        (measurable_trajectory_at_incrementFiltration (q : ℕ))
        measurable_const).compl)
  exact (holdPast.inter havoid).inter (hterminal.measurableSet_eq n)

/-! ## A canonical screened return ladder -/

/-- The return-ladder stage additionally remembers that the stopped target
is distinct from the old favorite and that the latter has not been visited
since the earlier stopped past. -/
def screenedReturnLadderStage
    (past start : StepPath → ℕ) (target : StepPath → Point)
    (deadline : ℕ) (old : StepPath → Point) : ℕ → Set StepPath
  | r =>
      (returnLadderStage start target deadline r ∩
        {w | old w ≠ target w}) ∩
          noOldVisitThrough past (returnLadder start target deadline r) old

/-- The screened stages are decreasing. -/
theorem screenedReturnLadderStage_succ_subset
    {past start : StepPath → ℕ} {target : StepPath → Point}
    {deadline r : ℕ} {old : StepPath → Point}
    (hstart_le : ∀ w, start w ≤ deadline) :
    screenedReturnLadderStage past start target deadline old (r + 1) ⊆
      screenedReturnLadderStage past start target deadline old r := by
  intro w hw
  rcases hw with ⟨⟨hreturn, hdistinct⟩, havoid⟩
  refine ⟨⟨returnLadderStage_succ_subset hstart_le hreturn, hdistinct⟩, ?_⟩
  intro q hpast hq
  exact havoid q hpast (hq.trans (returnLadder_mono_step hstart_le w))

/-- Every screened stage is observable at its return-ladder clock. -/
theorem screenedReturnLadderStage_observable
    {past start : StepPath → ℕ} {target old : StepPath → Point}
    {deadline : ℕ}
    (hstart : IsFiniteStoppingTime start)
    (hstart_le : ∀ w, start w ≤ deadline)
    (htarget : ∀ x, IsMeasurableAtStopping start {w | target w = x})
    (hpast_le : ∀ w, past w ≤ start w)
    (hold : ∀ x, IsMeasurableAtStopping past {w | old w = x}) :
    ∀ r, IsMeasurableAtStopping (returnLadder start target deadline r)
      (screenedReturnLadderStage past start target deadline old r) := by
  intro r
  have hstop : IsFiniteStoppingTime (returnLadder start target deadline r) :=
    returnLadder_isFiniteStoppingTime hstart hstart_le htarget r
  have hstage := returnLadderStage_observable hstart hstart_le htarget
    (r := r)
  have holdAtStart (x : Point) :
      IsMeasurableAtStopping start {w | old w = x} :=
    IsMeasurableAtStopping.mono_time (hold x) hstart hpast_le
  have holdAtReturn (x : Point) :
      IsMeasurableAtStopping (returnLadder start target deadline r)
          {w | old w = x} :=
    IsMeasurableAtStopping.mono_time (holdAtStart x) hstop
      (returnLadder_base_le hstart_le r)
  have htargetAtReturn (x : Point) :
      IsMeasurableAtStopping (returnLadder start target deadline r)
          {w | target w = x} :=
    returnLadder_target_observable hstart hstart_le htarget r x
  have heqObservable : IsMeasurableAtStopping
      (returnLadder start target deadline r) {w | old w = target w} := by
    simpa only [sub_eq_zero] using
      isMeasurableAtStopping_binary_fiber holdAtReturn htargetAtReturn
        (fun a b : Point ↦ a - b) 0
  have hdistinct : IsMeasurableAtStopping
      (returnLadder start target deadline r) {w | old w ≠ target w} := by
    have hset : {w | old w ≠ target w} = ({w | old w = target w})ᶜ := by
      ext w
      simp
    rw [hset]
    exact isMeasurableAtStopping_compl hstop heqObservable
  have hpastReturn : ∀ w, past w ≤
      returnLadder start target deadline r w := fun w ↦
    (hpast_le w).trans (returnLadder_base_le hstart_le r w)
  exact isMeasurableAtStopping_inter
    (isMeasurableAtStopping_inter hstage hdistinct)
    (noOldVisitThrough_observable hstop hpastReturn hold)

/-- The displacement from the stopped target to a stopped-past old site is
observable at every return-ladder clock. -/
theorem returnLadder_relativePoint_fiber_observable
    {past start : StepPath → ℕ} {target old : StepPath → Point}
    {deadline r : ℕ}
    (hstart : IsFiniteStoppingTime start)
    (hstart_le : ∀ w, start w ≤ deadline)
    (htarget : ∀ x, IsMeasurableAtStopping start {w | target w = x})
    (hpast_le : ∀ w, past w ≤ start w)
    (hold : ∀ x, IsMeasurableAtStopping past {w | old w = x})
    (x : Point) :
    IsMeasurableAtStopping (returnLadder start target deadline r)
      {w | old w - target w = x} := by
  have hstop : IsFiniteStoppingTime (returnLadder start target deadline r) :=
    returnLadder_isFiniteStoppingTime hstart hstart_le htarget r
  have holdAtStart (a : Point) :
      IsMeasurableAtStopping start {w | old w = a} :=
    IsMeasurableAtStopping.mono_time (hold a) hstart hpast_le
  have holdAtReturn (a : Point) :
      IsMeasurableAtStopping (returnLadder start target deadline r)
        {w | old w = a} :=
    IsMeasurableAtStopping.mono_time (holdAtStart a) hstop
      (returnLadder_base_le hstart_le r)
  have htargetAtReturn (a : Point) :
      IsMeasurableAtStopping (returnLadder start target deadline r)
        {w | target w = a} :=
    returnLadder_target_observable hstart hstart_le htarget r a
  exact isMeasurableAtStopping_binary_fiber holdAtReturn htargetAtReturn
    (fun a b : Point ↦ a - b) x

/-- On a screened additional return, the fresh tail cannot hit the old site
before its first positive return to the candidate. -/
theorem screenedReturnLadderStage_succ_subset_pointBeforeReturn_compl
    {past start : StepPath → ℕ} {target old : StepPath → Point}
    {deadline r : ℕ}
    (hstart_le : ∀ w, start w ≤ deadline)
    (hpast_le : ∀ w, past w ≤ start w)
    (hbase : ∀ w, trajectory w (start w) = target w) :
    screenedReturnLadderStage past start target deadline old (r + 1) ⊆
      {w | w ∈ screenedReturnLadderStage past start target deadline old r ∧
        postStoppingSteps (returnLadder start target deadline r) w ∈
          (pointBeforePositiveReturn (old w - target w))ᶜ} := by
  intro w hw
  have hwPrev := screenedReturnLadderStage_succ_subset hstart_le hw
  refine ⟨hwPrev, ?_⟩
  intro hhit
  rw [pointBeforePositiveReturn] at hhit
  rcases Set.mem_iUnion.mp hhit with ⟨n, hn⟩
  have hwReturnNext :
      w ∈ returnLadderStage start target deadline (r + 1) := hw.1.1
  have hwReturnPrev :
      w ∈ returnLadderStage start target deadline r :=
    returnLadderStage_succ_subset hstart_le hwReturnNext
  have hprevTarget : trajectory w (returnLadder start target deadline r w) =
      target w := returnLadder_eq_target_of_stage hbase r hwReturnPrev
  have hnextLt : returnLadder start target deadline (r + 1) w < deadline :=
    hwReturnNext
  have hex : ∃ j, j < deadline ∧
      returnLadder start target deadline r w < j ∧
        trajectory w j = target w := by
    rw [returnLadder_succ] at hnextLt
    exact (nextVisitBefore_lt_deadline_iff w).mp hnextLt
  have hnextSpec :
      returnLadder start target deadline r w <
          returnLadder start target deadline (r + 1) w ∧
        trajectory w (returnLadder start target deadline (r + 1) w) =
          target w := by
    rw [returnLadder_succ]
    unfold nextVisitBefore
    rw [dif_pos hex]
    exact ⟨(Nat.find_spec hex).2.1, (Nat.find_spec hex).2.2⟩
  let d := returnLadder start target deadline (r + 1) w -
    returnLadder start target deadline r w
  have hdpos : 0 < d := Nat.sub_pos_of_lt hnextSpec.1
  have hadd : returnLadder start target deadline r w + d =
      returnLadder start target deadline (r + 1) w := by
    dsimp only [d]
    exact Nat.add_sub_of_le hnextSpec.1.le
  have hzero : trajectory
      (postStoppingSteps (returnLadder start target deadline r) w) d = 0 := by
    change trajectory
      (shiftSteps (returnLadder start target deadline r w) w) d = 0
    rw [← trajectory_add_sub_trajectory, hadd, hnextSpec.2,
      hprevTarget, sub_self]
  have hnd : n < d := by
    have hnotDlt : ¬d < n := by
      intro hdn
      exact (hn.2.2 d hdpos hdn).1 hzero
    have hnNeD : n ≠ d := by
      intro hndeq
      have hrelativeZero : old w - target w = 0 := by
        rw [← hn.2.1, hndeq, hzero]
      exact hw.1.2 (sub_eq_zero.mp hrelativeZero)
    omega
  have hglobalOld : trajectory w
      (returnLadder start target deadline r w + n) = old w := by
    have htail := hn.2.1
    change trajectory
      (shiftSteps (returnLadder start target deadline r w) w) n =
        old w - target w at htail
    rw [← trajectory_add_sub_trajectory, hprevTarget] at htail
    exact sub_left_injective htail
  have hpastCurrent : past w ≤ returnLadder start target deadline r w :=
    (hpast_le w).trans (returnLadder_base_le hstart_le r w)
  have hnpos : 0 < n := hn.1
  have hpastGlobal : past w <
      returnLadder start target deadline r w + n := by omega
  have hglobalNext : returnLadder start target deadline r w + n ≤
      returnLadder start target deadline (r + 1) w := by
    rw [← hadd]
    omega
  exact hw.2 _ hpastGlobal hglobalNext hglobalOld

/-! ## Canonical stopped candidates with an old favorite -/

/-- The stopped-candidate local-time witness augmented by the old favorite
which must be avoided.  All clocks and candidate visits are still generated
canonically from the local-time gain. -/
structure StoppedCandidatePointReturnWitness
    (event : Set WalkPath) (deadline returns : ℕ) where
  candidateWitness :
    StoppedCandidateLocalTimeWitness event deadline returns
  oldFavorite : StepPath → Point
  oldFavorite_observable : ∀ x,
    IsMeasurableAtStopping candidateWitness.past {w | oldFavorite w = x}
  event_distinct : ∀ w, trajectory w ∈ event →
    oldFavorite w ≠ candidateWitness.candidate w
  event_no_old_visit : ∀ w, trajectory w ∈ event → ∀ q,
    candidateWitness.past w < q → q < deadline →
      trajectory w q ≠ oldFavorite w

/-- The canonical first visit to the candidate after the stopped past. -/
noncomputable def StoppedCandidatePointReturnWitness.start
    {event : Set WalkPath} {deadline returns : ℕ}
    (h : StoppedCandidatePointReturnWitness event deadline returns) :
    StepPath → ℕ :=
  nextVisitBefore h.candidateWitness.past h.candidateWitness.candidate deadline

/-- The candidate position observed at the canonical first-visit clock. -/
def StoppedCandidatePointReturnWitness.target
    {event : Set WalkPath} {deadline returns : ℕ}
    (h : StoppedCandidatePointReturnWitness event deadline returns) :
    StepPath → Point := stoppedLocation h.start

theorem StoppedCandidatePointReturnWitness.start_isStopping
    {event : Set WalkPath} {deadline returns : ℕ}
    (h : StoppedCandidatePointReturnWitness event deadline returns) :
    IsFiniteStoppingTime h.start :=
  isFiniteStoppingTime_nextVisitBefore h.candidateWitness.candidate_observable

theorem StoppedCandidatePointReturnWitness.past_le_start
    {event : Set WalkPath} {deadline returns : ℕ}
    (h : StoppedCandidatePointReturnWitness event deadline returns) :
    ∀ w, h.candidateWitness.past w ≤ h.start w :=
  self_le_nextVisitBefore (fun w ↦ (h.candidateWitness.past_lt_deadline w).le)

theorem StoppedCandidatePointReturnWitness.start_le_deadline
    {event : Set WalkPath} {deadline returns : ℕ}
    (h : StoppedCandidatePointReturnWitness event deadline returns) :
    ∀ w, h.start w ≤ deadline :=
  nextVisitBefore_le_deadline _ _ _

theorem StoppedCandidatePointReturnWitness.target_observable
    {event : Set WalkPath} {deadline returns : ℕ}
    (h : StoppedCandidatePointReturnWitness event deadline returns) (x : Point) :
    IsMeasurableAtStopping h.start {w | h.target w = x} :=
  stoppedLocation_fiber_observable h.start_isStopping x

theorem StoppedCandidatePointReturnWitness.start_at_target
    {event : Set WalkPath} {deadline returns : ℕ}
    (h : StoppedCandidatePointReturnWitness event deadline returns) (w : StepPath) :
    trajectory w (h.start w) = h.target w := rfl

/-- On the slot event, the canonical first-visit clock really is at the
enumerated candidate. -/
theorem StoppedCandidatePointReturnWitness.target_eq_candidate
    {event : Set WalkPath} {deadline returns : ℕ}
    (h : StoppedCandidatePointReturnWitness event deadline returns)
    {w : StepPath} (hw : trajectory w ∈ event) :
    h.target w = h.candidateWitness.candidate w := by
  obtain ⟨times, _hmono, hafter, hbefore, hvisit⟩ :=
    h.candidateWitness.toReturnWitness.event_visits hw
  let first : Fin (returns + 1) := ⟨0, Nat.zero_lt_succ returns⟩
  have hstartLt : h.start w < deadline := by
    apply (nextVisitBefore_lt_deadline_iff w).2
    exact ⟨times first, hbefore first, hafter first, hvisit first⟩
  exact trajectory_nextVisitBefore_eq_target_of_lt hstartLt

/-- The slot event lies in every required screened return stage. -/
theorem StoppedCandidatePointReturnWitness.event_mem_screenedStage
    {event : Set WalkPath} {deadline returns : ℕ}
    (h : StoppedCandidatePointReturnWitness event deadline returns)
    {w : StepPath} (hw : trajectory w ∈ event) :
    w ∈ screenedReturnLadderStage
      h.candidateWitness.past h.start h.target deadline h.oldFavorite returns := by
  have hschedule := h.candidateWitness.toReturnWitness.event_visits hw
  obtain ⟨times, hmono, hafter, hbefore, hvisit⟩ := hschedule
  have hreturn : w ∈ returnLadderStage h.start h.target deadline returns :=
    returnLadderStage_of_strictVisitSchedule
      ⟨times, hmono, hafter, hbefore, hvisit⟩
  have hclockLt : returnLadder h.start h.target deadline returns w < deadline := by
    have hle := returnLadder_le_visitTime times hmono hafter hbefore hvisit
      ⟨returns, Nat.lt_succ_self returns⟩
    exact hle.trans_lt (hbefore ⟨returns, Nat.lt_succ_self returns⟩)
  refine ⟨⟨hreturn, ?_⟩, ?_⟩
  · intro heq
    apply h.event_distinct w hw
    exact heq.trans (h.target_eq_candidate hw)
  · intro q hpast hq
    exact h.event_no_old_visit w hw q hpast (hq.trans_lt hclockLt)

/-! ## The exact one-return cost -/

/-- The complement of `H_x < H_0^+` costs at most `1-p` whenever `p` is a
lower bound for the exact point-before-return probability. -/
theorem fairSteps_compl_pointBeforePositiveReturn_le
    (x : Point) {p : ℝ} (hp0 : 0 ≤ p)
    (hlower : p ≤ pointBeforeReturnProbability x) :
    fairSteps (pointBeforePositiveReturn x)ᶜ ≤ ENNReal.ofReal (1 - p) := by
  have hprob : ENNReal.ofReal p ≤ fairSteps (pointBeforePositiveReturn x) := by
    apply (ENNReal.ofReal_le_iff_le_toReal (by finiteness)).2
    change p ≤ (fairSteps (pointBeforePositiveReturn x)).toReal at hlower
    exact hlower
  rw [measure_compl (measurableSet_pointBeforePositiveReturn x)
    (measure_ne_top _ _), measure_univ]
  rw [← ENNReal.ofReal_one, ENNReal.ofReal_sub 1 hp0]
  exact tsub_le_tsub_left hprob _

/-- A pathwise certificate for repeated candidate returns screened by the
sharp event that the old favorite is hit before the next candidate return.
The translated old-favorite displacement may be random, but is observable at
the corresponding restart clock. -/
structure PointBeforeReturnCertificate
    (event : Set WalkPath) (returns : ℕ) where
  stage : ℕ → Set StepPath
  stop : ℕ → StepPath → ℕ
  relativePoint : ℕ → StepPath → Point
  event_subset : trajectory ⁻¹' event ⊆ stage returns
  stop_isStopping : ∀ r < returns, IsFiniteStoppingTime (stop r)
  spatial_observable : ∀ r < returns, ∀ x,
    IsMeasurableAtStopping (stop r)
      (stage r ∩ {w | relativePoint r w = x})
  next_subset : ∀ r < returns,
    stage (r + 1) ⊆
      {w | w ∈ stage r ∧
        postStoppingSteps (stop r) w ∈
          (pointBeforePositiveReturn (relativePoint r w))ᶜ}

/-- Full-tail strong Markov turns the exact one-step lower bound into the
complete geometric return cost. -/
theorem measure_le_geometricReturnCost_of_pointBeforeReturnCertificate
    {event : Set WalkPath} {returns : ℕ} {escapeChance : ℝ}
    (hevent : MeasurableSet event)
    (hzero : 0 ≤ escapeChance) (hone : escapeChance ≤ 1)
    (cert : PointBeforeReturnCertificate event returns)
    (hlower : ∀ r < returns, ∀ w,
      w ∈ cert.stage r →
        escapeChance ≤ pointBeforeReturnProbability (cert.relativePoint r w)) :
    simpleRandomWalk event ≤
      Gap.geometricReturnCost escapeChance returns := by
  let q : ℝ≥0∞ := ENNReal.ofReal (1 - escapeChance)
  have hstage : ∀ r ≤ returns, fairSteps (cert.stage r) ≤ q ^ r := by
    intro r hr
    induction r with
    | zero =>
        simpa using
          (measure_mono (μ := fairSteps) (subset_univ (cert.stage 0)))
    | succ r ih =>
        have hrlt : r < returns := by omega
        have hstep := strongMarkov_fullTail_spatial_le
          (cert.stop_isStopping r hrlt)
          (fun x ↦ (pointBeforePositiveReturn x)ᶜ) q
          (cert.spatial_observable r hrlt)
          (fun x ↦ (measurableSet_pointBeforePositiveReturn x).compl)
          (fun x hx ↦ by
            obtain ⟨w, hwstage, hwx⟩ := hx
            apply fairSteps_compl_pointBeforePositiveReturn_le x hzero
            rw [← hwx]
            exact hlower r hrlt w hwstage)
        calc
          fairSteps (cert.stage (r + 1)) ≤
              fairSteps {w | w ∈ cert.stage r ∧
                postStoppingSteps (cert.stop r) w ∈
                  (pointBeforePositiveReturn
                    (cert.relativePoint r w))ᶜ} :=
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
    _ = Gap.geometricReturnCost escapeChance returns := by
      exact (ENNReal.ofReal_pow (sub_nonneg.mpr hone) returns).symm

/-! ## Instantiation by the canonical stopped candidate -/

/-- The literal stopped-candidate/old-favorite data instantiate the complete
full-tail point-before-return certificate. -/
noncomputable def StoppedCandidatePointReturnWitness.toPointBeforeReturnCertificate
    {event : Set WalkPath} {deadline returns : ℕ}
    (h : StoppedCandidatePointReturnWitness event deadline returns) :
    PointBeforeReturnCertificate event returns where
  stage := screenedReturnLadderStage
    h.candidateWitness.past h.start h.target deadline h.oldFavorite
  stop := returnLadder h.start h.target deadline
  relativePoint := fun _ w ↦ h.oldFavorite w - h.target w
  event_subset := fun _ hw ↦ h.event_mem_screenedStage hw
  stop_isStopping := fun r _hr ↦
    returnLadder_isFiniteStoppingTime h.start_isStopping h.start_le_deadline
      h.target_observable r
  spatial_observable := fun r _hr x ↦
    isMeasurableAtStopping_inter
      (screenedReturnLadderStage_observable h.start_isStopping
        h.start_le_deadline h.target_observable h.past_le_start
        h.oldFavorite_observable r)
      (returnLadder_relativePoint_fiber_observable h.start_isStopping
        h.start_le_deadline h.target_observable h.past_le_start
        h.oldFavorite_observable x)
  next_subset := fun _r _hr ↦
    screenedReturnLadderStage_succ_subset_pointBeforeReturn_compl
      h.start_le_deadline h.past_le_start h.start_at_target

/-- Sharp geometric return cost for a canonical stopped candidate.  The only
remaining analytic input is a lower bound for `P_0(H_x < H_0^+)` on the
nonzero random displacements admitted by the screened stages. -/
theorem measure_le_geometricReturnCost_of_stoppedCandidatePointReturn
    {event : Set WalkPath} {deadline returns : ℕ} {escapeChance : ℝ}
    (hevent : MeasurableSet event)
    (hzero : 0 ≤ escapeChance) (hone : escapeChance ≤ 1)
    (h : StoppedCandidatePointReturnWitness event deadline returns)
    (hlower : ∀ w, h.oldFavorite w ≠ h.target w →
      escapeChance ≤ pointBeforeReturnProbability
        (h.oldFavorite w - h.target w)) :
    simpleRandomWalk event ≤ Gap.geometricReturnCost escapeChance returns := by
  apply measure_le_geometricReturnCost_of_pointBeforeReturnCertificate
    hevent hzero hone h.toPointBeforeReturnCertificate
  intro r _hr w hw
  exact hlower w hw.1.2

section FiniteScreen

variable {Band Site : Type*}

/-- One old-favorite/candidate witness per finite slot discharges the sharp
per-candidate geometric-return premise. -/
theorem perCandidateGeometricReturnBound_of_stoppedCandidatePointReturns
    (bands : Finset Band) (sites : WalkPath → Band → Finset Site)
    (budget deadline returns : Band → ℕ) (escapeChance : Band → ℝ)
    (realizes : WalkPath → Band → Site → Prop)
    (hmeas : ∀ band i,
      MeasurableSet (slotSuccessEvent sites realizes band i))
    (hzero : ∀ band ∈ bands, 0 ≤ escapeChance band)
    (hone : ∀ band ∈ bands, escapeChance band ≤ 1)
    (hwitness : ∀ band ∈ bands, ∀ i ∈ Finset.range (budget band),
      StoppedCandidatePointReturnWitness
        (slotSuccessEvent sites realizes band i)
        (deadline band) (returns band))
    (hlower : ∀ (band : Band) (hband : band ∈ bands) (i : ℕ)
      (hi : i ∈ Finset.range (budget band)) (w : StepPath),
      let h := hwitness band hband i hi
      h.oldFavorite w ≠ h.target w →
        escapeChance band ≤ pointBeforeReturnProbability
          (h.oldFavorite w - h.target w)) :
    Gap.PerCandidateGeometricReturnBound simpleRandomWalk bands
      (fun band ↦ Finset.range (budget band))
      (slotSuccessEvent sites realizes) escapeChance returns := by
  intro band hband i hi
  exact measure_le_geometricReturnCost_of_stoppedCandidatePointReturn
    (hmeas band i) (hzero band hband) (hone band hband)
    (hwitness band hband i hi) (hlower band hband i hi)

/-- Full finite-screen estimate with the sharp point-before-return cost. -/
theorem measure_gapDeficitExceptionalEvent_le_overflow_add_pointReturns
    (t : DominoTiling) (m : ℕ) (bands : Finset Band)
    (sites : WalkPath → Band → Finset Site)
    (budget deadline returns : Band → ℕ) (escapeChance : Band → ℝ)
    (realizes : WalkPath → Band → Site → Prop)
    (hpath : PathGapWitness (HLOZPathEvents.gapDeficitExceptionalEvent t m)
      bands sites budget realizes)
    (hmeas : ∀ band i,
      MeasurableSet (slotSuccessEvent sites realizes band i))
    (hzero : ∀ band ∈ bands, 0 ≤ escapeChance band)
    (hone : ∀ band ∈ bands, escapeChance band ≤ 1)
    (hwitness : ∀ band ∈ bands, ∀ i ∈ Finset.range (budget band),
      StoppedCandidatePointReturnWitness
        (slotSuccessEvent sites realizes band i)
        (deadline band) (returns band))
    (hlower : ∀ (band : Band) (hband : band ∈ bands) (i : ℕ)
      (hi : i ∈ Finset.range (budget band)) (w : StepPath),
      let h := hwitness band hband i hi
      h.oldFavorite w ≠ h.target w →
        escapeChance band ≤ pointBeforeReturnProbability
          (h.oldFavorite w - h.target w)) :
    simpleRandomWalk (HLOZPathEvents.gapDeficitExceptionalEvent t m) ≤
      simpleRandomWalk (candidateOverflow bands sites budget) +
        ∑ band ∈ bands, (budget band : ℝ≥0∞) *
          Gap.geometricReturnCost (escapeChance band) (returns band) := by
  let overflow := candidateOverflow bands sites budget
  let screened := HLOZPathEvents.gapDeficitExceptionalEvent t m \ overflow
  have hsplit : HLOZPathEvents.gapDeficitExceptionalEvent t m ⊆
      overflow ∪ screened := by
    intro s hs
    by_cases ho : s ∈ overflow
    · exact Or.inl ho
    · exact Or.inr ⟨hs, ho⟩
  calc
    simpleRandomWalk (HLOZPathEvents.gapDeficitExceptionalEvent t m) ≤
        simpleRandomWalk (overflow ∪ screened) := measure_mono hsplit
    _ ≤ simpleRandomWalk overflow + simpleRandomWalk screened :=
      measure_union_le _ _
    _ ≤ simpleRandomWalk overflow +
        ∑ band ∈ bands, (budget band : ℝ≥0∞) *
          Gap.geometricReturnCost (escapeChance band) (returns band) := by
      gcongr
      exact Gap.measure_gapEvent_le_geometric_sum simpleRandomWalk screened bands
        (fun band ↦ Finset.range (budget band))
        (slotSuccessEvent sites realizes) budget escapeChance returns
        (by
          dsimp only [screened, overflow]
          exact gapEvent_diff_overflow_covered_by_slots
            (HLOZPathEvents.gapDeficitExceptionalEvent t m)
            bands sites budget realizes hpath)
        (range_candidateCountBound bands budget)
        (perCandidateGeometricReturnBound_of_stoppedCandidatePointReturns
          bands sites budget deadline returns escapeChance realizes hmeas
          hzero hone hwitness hlower)

end FiniteScreen

end

end Erdos1165.HLOZGapPointReturn
