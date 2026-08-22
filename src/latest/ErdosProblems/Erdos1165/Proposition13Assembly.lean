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

import ErdosProblems.Erdos1165.AppendixDecoupling
import ErdosProblems.Erdos1165.AppendixA8OnePoint
import ErdosProblems.Erdos1165.AppendixFirstMoment
import ErdosProblems.Erdos1165.AppendixLocalTime
import ErdosProblems.Erdos1165.AppendixLocalTimeTransfer
import ErdosProblems.Erdos1165.AppendixPair
import ErdosProblems.Erdos1165.AppendixSmallBallAssembly
import ErdosProblems.Erdos1165.BlockAmplification
import ErdosProblems.Erdos1165.ConsecutiveBlocks
import ErdosProblems.Erdos1165.DiffusiveExitTail
import ErdosProblems.Erdos1165.ExitTail
import ErdosProblems.Erdos1165.LevelTail
import ErdosProblems.Erdos1165.ProfileA11Assembly
import ErdosProblems.Erdos1165.Proposition13Measurability
import ErdosProblems.Erdos1165.SecondMoment
import ErdosProblems.Erdos1165.ThickPoint

/-!
# Assembly of HLOZ Proposition 1.3

This file isolates the exact remaining inputs needed to turn the checked
finite Appendix-A calculations into the lower-deviation estimate for the
maximum local time of planar simple random walk.

For each deterministic block, `successful` is the excursion-profile event
and `thick` is its terminal-local-time refinement.  The three genuinely
walk-specific analytic inputs left explicit in `ScaleCertificate` are:

* `onePointProfile`: the uniform one-point profile lower bound (the output of
  the annular Harnack comparison and constrained-profile estimate);
* `terminalThick`: the event-level terminal Harnack/disintegration lower
  comparison; the Bernoulli--geometric concentration and loss algebra are
  checked in `AppendixLocalTimeTransfer` and this file;
* `pairMoment`: the summed two-point bound (the output of the separation-level
  decomposition and the two-point Harnack estimate).

Everything after those estimates is proved here.  The first two inputs give a
first-moment lower bound, `SecondMoment.indicatorCount_union_lower` gives a
one-block success probability, `ExitTail` controls a delayed disc exit, and
`BlockAmplification` turns independent deterministic blocks into the exact
double-exponential bound of HLOZ Proposition 1.3.  No lower-deviation estimate
is a field of the certificate.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal ProbabilityTheory

namespace Erdos1165.Proposition13Assembly

noncomputable section

open ConsecutiveBlocks

/-! ## One-block first and second moment assembly -/

/-- The event that at least one candidate point is thick-successful in a
given block. -/
def oneBlockSuccess (scale : ℕ) (thick : Point → Set StepPath) : Set StepPath :=
  ⋃ x ∈ ThickPoint.candidateBox scale, thick x

lemma measurableSet_oneBlockSuccess {scale : ℕ} {thick : Point → Set StepPath}
    (hmeas : ∀ x ∈ ThickPoint.candidateBox scale, MeasurableSet (thick x)) :
    MeasurableSet (oneBlockSuccess scale thick) := by
  exact (ThickPoint.candidateBox scale).measurableSet_biUnion hmeas

/-- The exact first-moment consequence of the one-point profile estimate and
the terminal-local-time loss estimate.  This is HLOZ (A.4) and (A.7), before
the second-moment argument. -/
theorem thick_firstMoment_lower
    (mu : Measure StepPath) [IsFiniteMeasure mu]
    (scale : ℕ) (successful thick : Point → Set StepPath)
    {onePoint epsilon : ℝ}
    (hepsilon1 : epsilon ≤ 1)
    (hmeasSuccessful : ∀ x ∈ ThickPoint.candidateBox scale,
      MeasurableSet (successful x))
    (hmeasThick : ∀ x ∈ ThickPoint.candidateBox scale,
      MeasurableSet (thick x))
    (hsub : ∀ x ∈ ThickPoint.candidateBox scale, thick x ⊆ successful x)
    (onePointProfile : ∀ x ∈ ThickPoint.candidateBox scale,
      onePoint ≤ mu.real (successful x))
    (terminalLoss : ∀ x ∈ ThickPoint.candidateBox scale,
      mu.real (successful x \ thick x) ≤
        epsilon * mu.real (successful x)) :
    ((ThickPoint.candidateBox scale).card : ℝ) *
        ((1 - epsilon) * onePoint) ≤
      ∑ x ∈ ThickPoint.candidateBox scale, mu.real (thick x) := by
  apply AppendixFirstMoment.card_mul_le_sum_of_uniform_lower
  intro x hx
  have hfactor : 0 ≤ 1 - epsilon := sub_nonneg.mpr hepsilon1
  calc
    (1 - epsilon) * onePoint ≤
        (1 - epsilon) * mu.real (successful x) :=
      mul_le_mul_of_nonneg_left (onePointProfile x hx) hfactor
    _ ≤ mu.real (thick x) :=
      AppendixFirstMoment.one_sub_mul_success_le_thick mu
        (hmeasSuccessful x hx) (hmeasThick x hx) (hsub x hx)
        (terminalLoss x hx)

/-- Event-level algebra turning a terminal conditional-success lower bound
into the successful-but-not-thick loss used by the first-moment argument. -/
theorem terminalLoss_of_thick_lower
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    {successful thick : Set Omega} {epsilon : ℝ}
    (hmeasSuccessful : MeasurableSet successful)
    (hmeasThick : MeasurableSet thick)
    (hsub : thick ⊆ successful)
    (hthick : (1 - epsilon) * mu.real successful ≤ mu.real thick) :
    mu.real (successful \ thick) ≤ epsilon * mu.real successful := by
  have hsplit := AppendixFirstMoment.measureReal_success_eq_thick_add_loss
    mu hmeasSuccessful hmeasThick hsub
  linarith

/-- Paley--Zygmund applied after the exact first-moment and summed pair
estimates.  Thus the only probabilistic inputs are precisely the one-point,
terminal-loss, and pair estimates displayed in the statement. -/
theorem oneBlockSuccess_probability_lower
    (mu : Measure StepPath) [IsFiniteMeasure mu]
    (scale : ℕ) (successful thick : Point → Set StepPath)
    {onePoint epsilon pairUpper : ℝ}
    (hepsilon1 : epsilon ≤ 1)
    (honePoint : 0 ≤ onePoint) (hpairUpper : 0 < pairUpper)
    (hmeasSuccessful : ∀ x ∈ ThickPoint.candidateBox scale,
      MeasurableSet (successful x))
    (hmeasThick : ∀ x ∈ ThickPoint.candidateBox scale,
      MeasurableSet (thick x))
    (hsub : ∀ x ∈ ThickPoint.candidateBox scale, thick x ⊆ successful x)
    (onePointProfile : ∀ x ∈ ThickPoint.candidateBox scale,
      onePoint ≤ mu.real (successful x))
    (terminalLoss : ∀ x ∈ ThickPoint.candidateBox scale,
      mu.real (successful x \ thick x) ≤
        epsilon * mu.real (successful x))
    (pairMoment :
      (∑ x ∈ ThickPoint.candidateBox scale,
        ∑ y ∈ ThickPoint.candidateBox scale,
          mu.real (thick x ∩ thick y)) ≤ pairUpper) :
    ((((ThickPoint.candidateBox scale).card : ℝ) *
          ((1 - epsilon) * onePoint)) ^ 2) / pairUpper ≤
      mu.real (oneBlockSuccess scale thick) := by
  let firstLower : ℝ := ((ThickPoint.candidateBox scale).card : ℝ) *
    ((1 - epsilon) * onePoint)
  have hfirstLower : 0 ≤ firstLower := by
    dsimp [firstLower]
    positivity
  have hfirst : firstLower ≤
      ∑ x ∈ ThickPoint.candidateBox scale, mu.real (thick x) := by
    exact thick_firstMoment_lower mu scale successful thick hepsilon1
      hmeasSuccessful hmeasThick hsub onePointProfile terminalLoss
  simpa [oneBlockSuccess, firstLower] using
    SecondMoment.indicatorCount_union_lower (mu := mu)
      (ThickPoint.candidateBox scale) thick hmeasThick hfirstLower hpairUpper
      hfirst pairMoment

/-! ## The finite certificate at a deterministic target time -/

/-- A shifted block has not left its prescribed closed disc by the chosen
block horizon.  The definition is deliberately the literal pullback of the
event controlled by `ExitTail.measureReal_staysInClosedDiscThrough_le_exp_div`.
-/
def lateExitEvent (start : ℕ) (center : Point) (radius horizon : ℕ) :
    Set StepPath :=
  shiftSteps start ⁻¹'
    ExitTail.staysInClosedDiscThrough center radius horizon

lemma measurableSet_lateExitEvent (start : ℕ) (center : Point)
    (radius horizon : ℕ) :
    MeasurableSet (lateExitEvent start center radius horizon) := by
  exact (measurable_shiftSteps start)
    (ExitTail.measurableSet_staysInClosedDiscThrough center radius horizon)

/-- The explicit exit exponent furnished by the checked diffusive exit-tail
argument. -/
def exitExponent (radius horizon : ℕ) : ℝ :=
  (3 / 16 : ℝ) *
    (horizon / DiffusiveExitTail.diffusiveBlockLength radius : ℕ)

theorem measureReal_lateExitEvent_le (start : ℕ) (center : Point)
    (radius horizon : ℕ) :
    fairSteps.real (lateExitEvent start center radius horizon) ≤
      Real.exp (-exitExponent radius horizon) := by
  have hmeasure :
      fairSteps (lateExitEvent start center radius horizon) =
        fairSteps (ExitTail.staysInClosedDiscThrough center radius horizon) := by
    rw [lateExitEvent, ← Measure.map_apply (measurable_shiftSteps start)
      (ExitTail.measurableSet_staysInClosedDiscThrough center radius horizon),
      fairSteps_map_shiftSteps]
  rw [Measure.real, hmeasure]
  simpa [Measure.real, exitExponent] using
    DiffusiveExitTail.measureReal_staysInClosedDiscThrough_diffusive_le_exp_div
      center radius horizon

/-! ### The literal stopped Appendix-A events -/

/-- The walk segment formed by increments beginning at deterministic time
`start`, translated back to the origin. -/
def shiftedWalk (start : ℕ) (omega : StepPath) : WalkPath :=
  trajectory (shiftSteps start omega)

lemma measurable_shiftedWalk (start : ℕ) : Measurable (shiftedWalk start) := by
  exact measurable_trajectory.comp (measurable_shiftSteps start)

/-- The range-based local time used by the Appendix construction is exactly
the finite-prefix local time used in the statement of Proposition 1.3. -/
lemma localTimeThrough_eq_localTime (s : WalkPath) (n : ℕ) (x : Point) :
    ThickPoint.localTimeThrough s n x = localTime s n x := by
  unfold ThickPoint.localTimeThrough localTime localTimePrefix pathPrefix
  apply Finset.card_bij
    (fun k hk ↦ (⟨k, by
      simpa using (Finset.mem_filter.mp hk).1⟩ : Fin (n + 1)))
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (Finset.mem_filter.mp hk).2
  · intro a _ha b _hb hab
    exact Fin.ext_iff.mp hab
  · intro j hj
    refine ⟨j, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_range, Fin.is_lt, true_and]
      exact (Finset.mem_filter.mp hj).2
    · rfl

/-- Translating a block interval into the global time axis injects every
visit in the shifted block into a visit of the original walk. -/
lemma localTimeThrough_shifted_le_global
    (omega : StepPath) (start horizon n : ℕ) (x : Point)
    (hbound : start + horizon ≤ n) :
    ThickPoint.localTimeThrough (shiftedWalk start omega) horizon x ≤
      localTime (trajectory omega) n (trajectory omega start + x) := by
  rw [← localTimeThrough_eq_localTime]
  unfold ThickPoint.localTimeThrough
  apply Finset.card_le_card_of_injective
    (f := fun k ↦ ⟨start + k.1, by
      rw [Finset.mem_filter]
      have hk := Finset.mem_filter.mp k.2
      have hklt : k.1 < horizon + 1 := Finset.mem_range.mp hk.1
      refine ⟨by rw [Finset.mem_range]; omega, ?_⟩
      have hshift := trajectory_add_sub_trajectory omega start k.1
      have hkpos := hk.2
      change trajectory (shiftSteps start omega) k.1 = x at hkpos
      rw [hkpos] at hshift
      apply_fun (fun z : Point ↦ trajectory omega start + z) at hshift
      simpa [add_sub_cancel_left] using hshift⟩)
  intro a b hab
  apply Subtype.ext
  exact Nat.add_left_cancel (congrArg Subtype.val hab)

/-- A thick-successful point inside a block forces the global maximum local
time to exceed the same threshold, provided the block lies before the target
time. -/
theorem lowerDeviation_not_of_shifted_thickPoint
    (omega : StepPath) (start scale horizon n : ℕ)
    (profileDelta thickDelta delta : ℝ) (x : Point)
    (hbound : start + horizon ≤ n)
    (hthick : ThickPoint.ThickSuccessfulPoint
      (shiftedWalk start omega) scale horizon profileDelta thickDelta x)
    (hthresholdPos : 0 < ThickPoint.thickThreshold scale thickDelta)
    (hthreshold : lowerDeviationThreshold delta n ≤
      ThickPoint.thickThreshold scale thickDelta) :
    omega ∈ (trajectory ⁻¹' lowerDeviationSet delta n)ᶜ := by
  have hlocalBlock : ThickPoint.thickThreshold scale thickDelta ≤
      (ThickPoint.localTimeThrough (shiftedWalk start omega) horizon x : ℝ) :=
    hthick.2
  have hlocalNat := localTimeThrough_shifted_le_global
    omega start horizon n x hbound
  have hlocal : ThickPoint.thickThreshold scale thickDelta ≤
      (localTime (trajectory omega) n (trajectory omega start + x) : ℝ) :=
    hlocalBlock.trans (by exact_mod_cast hlocalNat)
  have hlocalPos : 0 <
      localTime (trajectory omega) n (trajectory omega start + x) := by
    exact_mod_cast lt_of_lt_of_le hthresholdPos hlocal
  have hvisited : trajectory omega start + x ∈
      visitedSites (trajectory omega) n :=
    (mem_visitedSites_iff_localTime_pos _ _ _).2 hlocalPos
  have hmax : localTime (trajectory omega) n (trajectory omega start + x) ≤
      maxLocalTime (trajectory omega) n :=
    localTime_le_maxLocalTime _ _ hvisited
  rw [mem_compl_iff]
  change ¬(maxLocalTime (trajectory omega) n : ℝ) <
    lowerDeviationThreshold delta n
  exact not_lt_of_ge (hthreshold.trans (hlocal.trans (by exact_mod_cast hmax)))

/-- The literal finite-word success event: the induced walk hits the outer
boundary and has a thick-successful candidate by the end of the block. -/
def boundedThickWordSuccess (blockLength scale : ℕ)
    (profileDelta thickDelta : ℝ) : Set (Fin blockLength → Direction) :=
  {u | ∃ horizon ≤ blockLength, ∃ x,
    ThickPoint.IsOuterExitTime
        (trajectory (ExitTail.extendStepPrefix u)) scale horizon ∧
      ThickPoint.ThickSuccessfulPoint
        (trajectory (ExitTail.extendStepPrefix u)) scale horizon
          profileDelta thickDelta x}

/-- The bounded finite-word event has the desired deterministic implication
to the global lower-deviation complement. -/
theorem boundedThickWordSuccess_to_global
    (omega : StepPath) (blockLength blockIndex scale n : ℕ)
    (profileDelta thickDelta delta : ℝ)
    (hblockEnd : blockIndex * blockLength + blockLength ≤ n)
    (hthresholdPos : 0 < ThickPoint.thickThreshold scale thickDelta)
    (hthreshold : lowerDeviationThreshold delta n ≤
      ThickPoint.thickThreshold scale thickDelta)
    (hword : consecutiveStepBlock blockLength blockIndex omega ∈
      boundedThickWordSuccess blockLength scale profileDelta thickDelta) :
    omega ∈ (trajectory ⁻¹' lowerDeviationSet delta n)ᶜ := by
  rcases hword with ⟨horizon, hhorizon, x, _hexit, hthick⟩
  let start := blockIndex * blockLength
  have hpref : ∀ k ≤ horizon,
      trajectory (ExitTail.extendStepPrefix
          (consecutiveStepBlock blockLength blockIndex omega)) k =
        shiftedWalk start omega k := by
    intro k hk
    have hkL : k ≤ blockLength := hk.trans hhorizon
    simpa [start, consecutiveStepBlock, shiftedWalk,
      stepBlock_eq_stepPrefix_shiftSteps] using
      (ExitTail.trajectory_extendStepPrefix (shiftSteps start omega) hkL)
  have hthickShift : ThickPoint.ThickSuccessfulPoint
      (shiftedWalk start omega) scale horizon profileDelta thickDelta x :=
    (Proposition13Measurability.thickSuccessfulPoint_congr_prefix hpref
      profileDelta thickDelta x).mp hthick
  apply lowerDeviation_not_of_shifted_thickPoint omega start scale horizon n
    profileDelta thickDelta delta x
  · dsimp [start]
    omega
  · exact hthickShift
  · exact hthresholdPos
  · exact hthreshold

/-! ### Deterministic outer-boundary crossing -/

/-- The integer radius used by the geometric exit-tail estimate.  It is the
ceiling of the real HLOZ outer radius, so the real disc is contained in this
finite integer disc. -/
noncomputable def outerExitRadius (scale : ℕ) : ℕ :=
  ⌈ThickPoint.outerScale scale⌉₊

lemma outerDisc_subset_closedDisc (scale : ℕ) :
    ThickPoint.disc (0, 0) (ThickPoint.outerScale scale) ⊆
      (Annulus.closedDisc (outerExitRadius scale) : Set Point) := by
  intro y hy
  change y ∈ Annulus.closedDisc (outerExitRadius scale)
  rw [Annulus.mem_closedDisc_iff_radiusSqInt_le]
  have hK0 : 0 ≤ ThickPoint.outerScale scale := by
    unfold ThickPoint.outerScale
    positivity
  have hdist0 : 0 ≤ ThickPoint.squaredDistance (0, 0) y := by
    unfold ThickPoint.squaredDistance
    positivity
  have hsqrtSq := Real.sq_sqrt hdist0
  have hdist : ThickPoint.squaredDistance (0, 0) y ≤
      ThickPoint.outerScale scale ^ 2 := by
    change ThickPoint.latticeDistance (0, 0) y ≤
      ThickPoint.outerScale scale at hy
    unfold ThickPoint.latticeDistance at hy
    nlinarith [Real.sqrt_nonneg (ThickPoint.squaredDistance (0, 0) y)]
  have hKR : ThickPoint.outerScale scale ≤ (outerExitRadius scale : ℝ) := by
    exact Nat.le_ceil _
  have hreal : (Annulus.radiusSqInt y : ℝ) ≤
      (outerExitRadius scale : ℝ) ^ 2 := by
    have heq : (Annulus.radiusSqInt y : ℝ) =
        ThickPoint.squaredDistance (0, 0) y := by
      simp [Annulus.radiusSqInt, ThickPoint.squaredDistance]
    rw [heq]
    nlinarith
  exact_mod_cast hreal

lemma adjacent_trajectory_succ (omega : StepPath) (k : ℕ) :
    ThickPoint.Adjacent (trajectory omega k) (trajectory omega (k + 1)) := by
  rw [trajectory_succ]
  unfold ThickPoint.Adjacent
  generalize hd : omega k = d
  fin_cases d <;> simp [directionVector]

/-- A nearest-neighbor path which starts in a set and leaves it by time `L`
must visit its inner vertex boundary by time `L`. -/
lemma exists_innerBoundary_before_of_exit
    (s : WalkPath) (A : Set Point)
    (hstep : ∀ k, ThickPoint.Adjacent (s k) (s (k + 1)))
    (hzero : s 0 ∈ A) {L : ℕ} (hexit : ∃ t ≤ L, s t ∉ A) :
    ∃ k ≤ L, s k ∈ ThickPoint.innerBoundary A := by
  classical
  let P : ℕ → Prop := fun t ↦ t ≤ L ∧ s t ∉ A
  let t := Nat.find hexit
  have htP : P t := Nat.find_spec hexit
  have ht0 : 0 < t := by
    by_contra h
    have : t = 0 := Nat.eq_zero_of_not_pos h
    exact htP.2 (this ▸ hzero)
  let k := t - 1
  have hkt : k < t := by omega
  have hkA : s k ∈ A := by
    by_contra hk
    have hkP : P k := ⟨hkt.le.trans htP.1, hk⟩
    exact (Nat.not_le_of_gt hkt) (Nat.find_min' hexit hkP)
  have hsucc : k + 1 = t := by omega
  refine ⟨k, hkt.le.trans htP.1, hkA, s t, htP.2, ?_⟩
  simpa [hsucc] using hstep k

lemma zero_mem_outerDisc (scale : ℕ) :
    (0, 0) ∈ ThickPoint.disc (0, 0) (ThickPoint.outerScale scale) := by
  change ThickPoint.latticeDistance (0, 0) (0, 0) ≤ ThickPoint.outerScale scale
  have hK0 : 0 ≤ ThickPoint.outerScale scale := by
    unfold ThickPoint.outerScale
    positivity
  simpa [ThickPoint.latticeDistance, ThickPoint.squaredDistance] using hK0

/-- Leaving the ceiling-radius closed disc by time `blockLength` forces the
literal first HLOZ outer-boundary time to occur within that block. -/
lemma outerExitTime_le_of_not_late
    (omega : StepPath) (start scale blockLength horizon : ℕ)
    (hexit : ThickPoint.IsOuterExitTime
      (shiftedWalk start omega) scale horizon)
    (hnotLate : omega ∉ lateExitEvent start (0, 0)
      (outerExitRadius scale) blockLength) :
    horizon ≤ blockLength := by
  have houtsideClosed : ∃ t ≤ blockLength,
      trajectory (shiftSteps start omega) t ∉
        Annulus.closedDisc (outerExitRadius scale) := by
    simp only [lateExitEvent, mem_preimage, ExitTail.staysInClosedDiscThrough,
      mem_ofPred_eq, not_forall] at hnotLate
    obtain ⟨t, htL, htout⟩ := hnotLate
    refine ⟨t, htL, ?_⟩
    change (0 : Point) + trajectory (shiftSteps start omega) t ∉
      Annulus.closedDisc (outerExitRadius scale) at htout
    simpa only [zero_add] using htout
  have houtsideOuter : ∃ t ≤ blockLength,
      shiftedWalk start omega t ∉
        ThickPoint.disc (0, 0) (ThickPoint.outerScale scale) := by
    obtain ⟨t, htL, htout⟩ := houtsideClosed
    exact ⟨t, htL, fun hin ↦ htout (outerDisc_subset_closedDisc scale hin)⟩
  have hboundary : ∃ k ≤ blockLength,
      shiftedWalk start omega k ∈
        ThickPoint.discBoundary (0, 0) (ThickPoint.outerScale scale) := by
    apply exists_innerBoundary_before_of_exit
      (shiftedWalk start omega)
      (ThickPoint.disc (0, 0) (ThickPoint.outerScale scale))
    · intro k
      exact adjacent_trajectory_succ (shiftSteps start omega) k
    · simpa [shiftedWalk] using zero_mem_outerDisc scale
    · exact houtsideOuter
  obtain ⟨k, hkL, hkBoundary⟩ := hboundary
  have hnot : ¬k < horizon := fun hkh ↦ hexit.2 k hkh hkBoundary
  exact (Nat.le_of_not_gt hnot).trans hkL

/-! The next lemmas discharge finite-prefix measurability for the literal
stopped events. -/

def extendWalkPrefix {horizon : ℕ} (u : Fin (horizon + 1) → Point) : WalkPath :=
  fun k ↦ if hk : k ≤ horizon then u ⟨k, Nat.lt_succ_of_le hk⟩ else (0, 0)

lemma extendWalkPrefix_eq {horizon : ℕ} (u : Fin (horizon + 1) → Point)
    {k : ℕ} (hk : k ≤ horizon) :
    extendWalkPrefix u k = u ⟨k, Nat.lt_succ_of_le hk⟩ := by
  simp [extendWalkPrefix, hk]

lemma measurableSet_of_pathPrefix_dependent (horizon : ℕ) (P : WalkPath → Prop)
    (hP : ∀ s t : WalkPath, (∀ k ≤ horizon, s k = t k) → (P s ↔ P t)) :
    MeasurableSet {s | P s} := by
  let A : Set (Fin (horizon + 1) → Point) := {u | P (extendWalkPrefix u)}
  have hset : {s : WalkPath | P s} =
      (fun s : WalkPath ↦ pathPrefix s horizon) ⁻¹' A := by
    ext s
    change P s ↔ P (extendWalkPrefix (pathPrefix s horizon))
    apply hP
    intro k hk
    simp [extendWalkPrefix, hk, pathPrefix]
  rw [hset]
  exact (measurable_pathPrefix horizon) (Set.to_countable A).measurableSet

lemma ThickPoint.hitTimesThrough_congr_prefix
    {s t : WalkPath} {horizon : ℕ}
    (hst : ∀ k ≤ horizon, s k = t k)
    (A : Set Point) [DecidablePred (· ∈ A)] (start : ℕ) :
    ThickPoint.hitTimesThrough s A start horizon =
      ThickPoint.hitTimesThrough t A start horizon := by
  apply Finset.filter_congr
  intro k hk
  have hkh : k ≤ horizon := (Finset.mem_Icc.mp hk).2
  rw [hst k hkh]

lemma ThickPoint.firstHitThrough_congr_prefix
    {s t : WalkPath} {horizon : ℕ}
    (hst : ∀ k ≤ horizon, s k = t k)
    (A : Set Point) [DecidablePred (· ∈ A)] (start : ℕ) :
    ThickPoint.firstHitThrough s A start horizon =
      ThickPoint.firstHitThrough t A start horizon := by
  unfold ThickPoint.firstHitThrough
  rw [ThickPoint.hitTimesThrough_congr_prefix hst A start]

lemma ThickPoint.completedExcursionCount_congr_prefix
    {s t : WalkPath} {horizon : ℕ}
    (hst : ∀ k ≤ horizon, s k = t k)
    (outer inner : Set Point)
    [DecidablePred (· ∈ outer)] [DecidablePred (· ∈ inner)] :
    ThickPoint.completedExcursionCount s outer inner horizon =
      ThickPoint.completedExcursionCount t outer inner horizon := by
  have hstep :
      ThickPoint.excursionStep s outer inner horizon =
        ThickPoint.excursionStep t outer inner horizon := by
    funext start
    unfold ThickPoint.excursionStep
    rw [ThickPoint.firstHitThrough_congr_prefix hst outer start,
      ThickPoint.firstHitThrough_congr_prefix hst inner]
  have hstart (j : ℕ) :
      ThickPoint.excursionStart s outer inner horizon j =
        ThickPoint.excursionStart t outer inner horizon j := by
    unfold ThickPoint.excursionStart
    rw [hstep, ThickPoint.firstHitThrough_congr_prefix hst outer]
  have hfinish (j : ℕ) :
      ThickPoint.excursionFinish s outer inner horizon j =
        ThickPoint.excursionFinish t outer inner horizon j := by
    unfold ThickPoint.excursionFinish
    rw [hstart j, ThickPoint.firstHitThrough_congr_prefix hst inner]
  unfold ThickPoint.completedExcursionCount
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro j _hj
  rw [hfinish j]

lemma ThickPoint.excursionProfile_congr_prefix
    {s t : WalkPath} {n horizon : ℕ}
    (hst : ∀ k ≤ horizon, s k = t k) (x : Point) :
    ThickPoint.excursionProfile s n horizon x =
    ThickPoint.excursionProfile t n horizon x := by
  classical
  funext k
  unfold ThickPoint.excursionProfile
  split_ifs
  · rfl
  · exact ThickPoint.completedExcursionCount_congr_prefix hst _ _

lemma ThickPoint.localTimeThrough_congr_prefix
    {s t : WalkPath} {horizon : ℕ}
    (hst : ∀ k ≤ horizon, s k = t k) (x : Point) :
    ThickPoint.localTimeThrough s horizon x =
      ThickPoint.localTimeThrough t horizon x := by
  unfold ThickPoint.localTimeThrough
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro k hk
  rw [hst k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))]

lemma ThickPoint.successfulPoint_congr_prefix
    {s t : WalkPath} {n horizon : ℕ}
    (hst : ∀ k ≤ horizon, s k = t k) (delta : ℝ) (x : Point) :
    ThickPoint.SuccessfulPoint s n horizon delta x ↔
      ThickPoint.SuccessfulPoint t n horizon delta x := by
  unfold ThickPoint.SuccessfulPoint
  rw [ThickPoint.excursionProfile_congr_prefix hst x]

lemma ThickPoint.thickSuccessfulPoint_congr_prefix
    {s t : WalkPath} {n horizon : ℕ}
    (hst : ∀ k ≤ horizon, s k = t k) (delta delta' : ℝ) (x : Point) :
    ThickPoint.ThickSuccessfulPoint s n horizon delta delta' x ↔
      ThickPoint.ThickSuccessfulPoint t n horizon delta delta' x := by
  unfold ThickPoint.ThickSuccessfulPoint
  rw [ThickPoint.successfulPoint_congr_prefix hst delta x,
    ThickPoint.localTimeThrough_congr_prefix hst x]

lemma ThickPoint.isOuterExitTime_congr_prefix
    {s t : WalkPath} {n horizon : ℕ}
    (hst : ∀ k ≤ horizon, s k = t k) :
    ThickPoint.IsOuterExitTime s n horizon ↔
      ThickPoint.IsOuterExitTime t n horizon := by
  unfold ThickPoint.IsOuterExitTime
  constructor
  · rintro ⟨hexit, hbefore⟩
    refine ⟨?_, ?_⟩
    · simpa [hst horizon le_rfl] using hexit
    · intro k hk
      simpa [hst k hk.le] using hbefore k hk
  · rintro ⟨hexit, hbefore⟩
    refine ⟨?_, ?_⟩
    · simpa [hst horizon le_rfl] using hexit
    · intro k hk
      simpa [hst k hk.le] using hbefore k hk

/-- A candidate point has the prescribed excursion profile at the first
outer-boundary hit of a shifted block. -/
def stoppedSuccessfulPointEvent (start scale : ℕ) (profileDelta : ℝ)
    (x : Point) : Set StepPath :=
  {omega | ∃ horizon : ℕ,
    ThickPoint.IsOuterExitTime (shiftedWalk start omega) scale horizon ∧
      ThickPoint.SuccessfulPoint (shiftedWalk start omega) scale horizon
        profileDelta x}

/-- The same stopped profile event refined by the required terminal local
time.  These are exactly the indicators denoted `Y'(q,x)` in HLOZ. -/
def stoppedThickPointEvent (start scale : ℕ)
    (profileDelta thickDelta : ℝ) (x : Point) : Set StepPath :=
  {omega | ∃ horizon : ℕ,
    ThickPoint.IsOuterExitTime (shiftedWalk start omega) scale horizon ∧
      ThickPoint.ThickSuccessfulPoint (shiftedWalk start omega) scale horizon
        profileDelta thickDelta x}

lemma measurableSet_stoppedSuccessfulPointEvent
    (start scale : ℕ) (profileDelta : ℝ) (x : Point) :
    MeasurableSet (stoppedSuccessfulPointEvent start scale profileDelta x) := by
  have hfixed (horizon : ℕ) : MeasurableSet
      {omega : StepPath |
        ThickPoint.IsOuterExitTime (shiftedWalk start omega) scale horizon ∧
          ThickPoint.SuccessfulPoint (shiftedWalk start omega) scale horizon
            profileDelta x} := by
    change MeasurableSet ((shiftedWalk start) ⁻¹'
      {s : WalkPath |
        ThickPoint.IsOuterExitTime s scale horizon ∧
          ThickPoint.SuccessfulPoint s scale horizon profileDelta x})
    apply (measurable_shiftedWalk start)
    exact measurableSet_of_pathPrefix_dependent horizon _ fun s t hst ↦ by
      rw [ThickPoint.isOuterExitTime_congr_prefix hst,
        ThickPoint.successfulPoint_congr_prefix hst profileDelta x]
  have hunion : stoppedSuccessfulPointEvent start scale profileDelta x =
      ⋃ horizon : ℕ,
        {omega : StepPath |
          ThickPoint.IsOuterExitTime (shiftedWalk start omega) scale horizon ∧
            ThickPoint.SuccessfulPoint (shiftedWalk start omega) scale horizon
              profileDelta x} := by
    ext omega
    simp [stoppedSuccessfulPointEvent]
  rw [hunion]
  exact MeasurableSet.iUnion hfixed

lemma measurableSet_stoppedThickPointEvent
    (start scale : ℕ) (profileDelta thickDelta : ℝ) (x : Point) :
    MeasurableSet
      (stoppedThickPointEvent start scale profileDelta thickDelta x) := by
  have hfixed (horizon : ℕ) : MeasurableSet
      {omega : StepPath |
        ThickPoint.IsOuterExitTime (shiftedWalk start omega) scale horizon ∧
          ThickPoint.ThickSuccessfulPoint (shiftedWalk start omega) scale horizon
            profileDelta thickDelta x} := by
    change MeasurableSet ((shiftedWalk start) ⁻¹'
      {s : WalkPath |
        ThickPoint.IsOuterExitTime s scale horizon ∧
          ThickPoint.ThickSuccessfulPoint s scale horizon
            profileDelta thickDelta x})
    apply (measurable_shiftedWalk start)
    exact measurableSet_of_pathPrefix_dependent horizon _ fun s t hst ↦ by
      rw [ThickPoint.isOuterExitTime_congr_prefix hst,
        ThickPoint.thickSuccessfulPoint_congr_prefix hst profileDelta thickDelta x]
  have hunion : stoppedThickPointEvent start scale profileDelta thickDelta x =
      ⋃ horizon : ℕ,
        {omega : StepPath |
          ThickPoint.IsOuterExitTime (shiftedWalk start omega) scale horizon ∧
            ThickPoint.ThickSuccessfulPoint (shiftedWalk start omega) scale horizon
              profileDelta thickDelta x} := by
    ext omega
    simp [stoppedThickPointEvent]
  rw [hunion]
  exact MeasurableSet.iUnion hfixed

lemma stoppedThickPointEvent_subset_stoppedSuccessfulPointEvent
    (start scale : ℕ) (profileDelta thickDelta : ℝ) (x : Point) :
    stoppedThickPointEvent start scale profileDelta thickDelta x ⊆
      stoppedSuccessfulPointEvent start scale profileDelta x := by
  rintro omega ⟨horizon, hexit, hthick⟩
  exact ⟨horizon, hexit, hthick.1⟩

/-- The stopped unbounded event, after removing the late-exit event, is
exactly carried by the literal bounded finite-word event. -/
theorem stoppedBlockSuccess_notLate_subset_boundedWord
    (blockIndex blockLength scale : ℕ) (profileDelta thickDelta : ℝ) :
    oneBlockSuccess scale
        (stoppedThickPointEvent (blockIndex * blockLength)
          scale profileDelta thickDelta) ∩
        (lateExitEvent (blockIndex * blockLength) (0, 0)
          (outerExitRadius scale) blockLength)ᶜ ⊆
      consecutiveStepBlock blockLength blockIndex ⁻¹'
        boundedThickWordSuccess blockLength scale profileDelta thickDelta := by
  intro omega homega
  have hnotLate : omega ∉ lateExitEvent (blockIndex * blockLength) (0, 0)
      (outerExitRadius scale) blockLength := homega.2
  have hsuccess := homega.1
  rw [oneBlockSuccess] at hsuccess
  simp only [mem_iUnion] at hsuccess
  obtain ⟨x, _hxCandidate, hxStopped⟩ := hsuccess
  change ∃ horizon : ℕ,
    ThickPoint.IsOuterExitTime
        (shiftedWalk (blockIndex * blockLength) omega) scale horizon ∧
      ThickPoint.ThickSuccessfulPoint
        (shiftedWalk (blockIndex * blockLength) omega) scale horizon
          profileDelta thickDelta x at hxStopped
  obtain ⟨horizon, hexit, hthick⟩ := hxStopped
  have hhorizon : horizon ≤ blockLength :=
    outerExitTime_le_of_not_late omega (blockIndex * blockLength) scale
      blockLength horizon hexit hnotLate
  have hpref : ∀ k ≤ horizon,
      trajectory (ExitTail.extendStepPrefix
          (consecutiveStepBlock blockLength blockIndex omega)) k =
        shiftedWalk (blockIndex * blockLength) omega k := by
    intro k hk
    have hkL : k ≤ blockLength := hk.trans hhorizon
    simpa [consecutiveStepBlock, shiftedWalk,
      stepBlock_eq_stepPrefix_shiftSteps] using
      (ExitTail.trajectory_extendStepPrefix
        (shiftSteps (blockIndex * blockLength) omega) hkL)
  refine ⟨horizon, hhorizon, x, ?_, ?_⟩
  · exact (Proposition13Measurability.isOuterExitTime_congr_prefix hpref).mpr hexit
  · exact (Proposition13Measurability.thickSuccessfulPoint_congr_prefix hpref
      profileDelta thickDelta x).mpr hthick

/-! ### Discharging the constrained-profile part of the one-point estimate -/

/-- **Checked one-point profile bound up to the genuine annular input.**

The finite Gaussian path reindexing, Taylor error, random-variance comparison,
prefix completion, and strip-survival loss are all contained in the explicit
positive quantity `quantitativeA8OnePoint`.  The sole remaining hypothesis is
the annular Harnack/disintegration comparison from the ideal constrained
profile law to the actual stopped random-walk event. -/
theorem stoppedSuccessful_probability_lower_of_quantitativeA8_and_harnack
    (blockStart : ℕ) {start steps n R : ℕ} (hstart : 2 ≤ start)
    (hbound : start + steps ≤ n)
    (hscale : (2560 : ℝ) * (n : ℝ) ^ 2 ≤ (R : ℝ) ^ 2)
    {profileDelta : ℝ} (hprofileDelta : profileDelta ≤ 1)
    (hcenter : ∀ l ∈ Finset.Icc start (start + steps),
      R ≤ AppendixFirstMoment.profileCenter l)
    (hwidth : ∀ l ∈ Finset.Icc start (start + steps),
      (R : ℝ) ≤ (l : ℝ) ^ (1 + profileDelta))
    (x : Point)
    (hannularHarnack :
      AppendixFirstMoment.constrainedProfileWeight (start + steps) profileDelta ≤
        fairSteps.real
          (stoppedSuccessfulPointEvent blockStart (start + steps)
            profileDelta x)) :
    AppendixA8OnePoint.quantitativeA8OnePoint
        (steps := steps) (n := n) (R := R) hstart ≤
      fairSteps.real
        (stoppedSuccessfulPointEvent blockStart (start + steps)
          profileDelta x) := by
  exact (AppendixA8OnePoint.quantitativeA8OnePoint_le_constrainedProfileWeight
    hstart hbound hscale hprofileDelta hcenter hwidth).trans hannularHarnack

/-- Data at one deterministic target time `n`.  It contains no estimate on
`lowerDeviationSet`.  Its analytic fields are the three finite Appendix-A
estimates; the remaining fields record the deterministic block transfer,
independence, and explicit numerical inequalities needed by amplification.
-/
structure ScaleCertificate (delta : ℝ) (n : ℕ) where
  /-- Appendix scale `q`. -/
  scale : ℕ
  /-- Number of deterministic independent blocks. -/
  blockCount : ℕ
  /-- Common deterministic length of the consecutive increment blocks. -/
  blockLength : ℕ
  blockLength_pos : 0 < blockLength
  /-- Width parameter in the successful excursion-profile window. -/
  profileDelta : ℝ
  /-- Exponent in the terminal thick-point threshold. -/
  thickDelta : ℝ
  /-- Uniform one-point profile lower bound. -/
  onePoint : ℝ
  /-- Relative loss in the terminal-local-time refinement. -/
  epsilon : ℝ
  /-- Uniform summed pair-moment upper bound. -/
  pairUpper : ℝ
  /-- Rate reserved for one deterministic block. -/
  blockRate : ℝ
  epsilon_le_one : epsilon ≤ 1
  onePoint_nonneg : 0 ≤ onePoint
  pairUpper_pos : 0 < pairUpper
  /-- Every consecutive block lies before the deterministic target time. -/
  blocksFit : blockCount * blockLength ≤ n
  thickThreshold_pos : 0 < ThickPoint.thickThreshold scale thickDelta
  globalThreshold_le : lowerDeviationThreshold delta n ≤
    ThickPoint.thickThreshold scale thickDelta
  /-- Missing one-point Harnack/profile estimate. -/
  onePointProfile : ∀ (i : Fin blockCount) x,
    x ∈ ThickPoint.candidateBox scale →
    onePoint ≤ fairSteps.real
      (stoppedSuccessfulPointEvent ((i : ℕ) * blockLength)
        scale profileDelta x)
  /-- Remaining event-level terminal Harnack/disintegration comparison.  The
  stopped-history proof and iid local-time concentration are supplied by the
  terminal-excursion modules; the loss estimate used below is then derived by
  `terminalLoss_of_thick_lower`. -/
  terminalThick : ∀ (i : Fin blockCount) x,
    x ∈ ThickPoint.candidateBox scale →
    (1 - epsilon) * fairSteps.real
        (stoppedSuccessfulPointEvent ((i : ℕ) * blockLength)
          scale profileDelta x) ≤
      fairSteps.real
        (stoppedThickPointEvent ((i : ℕ) * blockLength)
          scale profileDelta thickDelta x)
  /-- Missing summed two-point Harnack/profile estimate. -/
  pairMoment : ∀ i : Fin blockCount,
    (∑ x ∈ ThickPoint.candidateBox scale,
      ∑ y ∈ ThickPoint.candidateBox scale,
        fairSteps.real
          (stoppedThickPointEvent ((i : ℕ) * blockLength)
              scale profileDelta thickDelta x ∩
            stoppedThickPointEvent ((i : ℕ) * blockLength)
              scale profileDelta thickDelta y)) ≤
      pairUpper
  /-- One-block first/second-moment failure plus the explicit exit tail fits
  below the reserved exponential rate. -/
  oneBlockNumerical :
    1 -
          ((((ThickPoint.candidateBox scale).card : ℝ) *
              ((1 - epsilon) * onePoint)) ^ 2) / pairUpper +
        Real.exp (-exitExponent (outerExitRadius scale) blockLength) ≤
      Real.exp (-blockRate)
  /-- There are enough blocks for the desired double exponential. -/
  enoughBlocks :
    Real.exp (Real.log n ^ (3 / 5 : ℝ)) ≤
      (blockCount : ℝ) * blockRate

/-- The pullback of the finite-word success event on the `i`-th consecutive
block. -/
def ScaleCertificate.timedSuccess {delta : ℝ} {n : ℕ}
    (cert : ScaleCertificate delta n) (i : Fin cert.blockCount) : Set StepPath :=
  consecutiveStepBlock cert.blockLength (i : ℕ) ⁻¹'
    boundedThickWordSuccess cert.blockLength cert.scale
      cert.profileDelta cert.thickDelta

lemma ScaleCertificate.independent_timed {delta : ℝ} {n : ℕ}
    (cert : ScaleCertificate delta n) :
    ProbabilityTheory.iIndepSet cert.timedSuccess fairSteps := by
  exact iIndepSet_consecutiveBlockEvents_of_countable cert.blockLength_pos
    (fun _ ↦ boundedThickWordSuccess cert.blockLength cert.scale
      cert.profileDelta cert.thickDelta)

lemma ScaleCertificate.timedSuccess_to_global {delta : ℝ} {n : ℕ}
    (cert : ScaleCertificate delta n) (i : Fin cert.blockCount) :
    cert.timedSuccess i ⊆ (trajectory ⁻¹' lowerDeviationSet delta n)ᶜ := by
  intro omega hsuccess
  apply boundedThickWordSuccess_to_global omega cert.blockLength (i : ℕ)
    cert.scale n cert.profileDelta cert.thickDelta delta
  · calc
      (i : ℕ) * cert.blockLength + cert.blockLength =
          ((i : ℕ) + 1) * cert.blockLength := by ring
      _ ≤ cert.blockCount * cert.blockLength := by
        exact Nat.mul_le_mul_right cert.blockLength (Nat.lt_iff_add_one_le.mp i.isLt)
      _ ≤ n := cert.blocksFit
  · exact cert.thickThreshold_pos
  · exact cert.globalThreshold_le
  · exact hsuccess

/-- The existence of certificates for every large deterministic time. -/
def HasAppendixCertificates : Prop :=
  ∀ delta : ℝ, 0 < delta → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    Nonempty (ScaleCertificate delta n)

/-! ## From a finite certificate to Proposition 1.3 -/

private lemma deterministicFailure_subset_of_late
    {exitSuccess timedSuccess late : Set StepPath}
    (htransfer : exitSuccess ∩ lateᶜ ⊆ timedSuccess) :
    timedSuccessᶜ ⊆ exitSuccessᶜ ∪ late := by
  intro omega htimed
  by_cases hexit : omega ∈ exitSuccess
  · by_cases hlate : omega ∈ late
    · exact Or.inr hlate
    · exact False.elim (htimed (htransfer ⟨hexit, hlate⟩))
  · exact Or.inl hexit

/-- A finite certificate gives the real-valued double-exponential estimate at
its target time. -/
theorem ScaleCertificate.measureReal_lowerDeviation_le
    {delta : ℝ} {n : ℕ} (cert : ScaleCertificate delta n) :
    fairSteps.real (trajectory ⁻¹' lowerDeviationSet delta n) ≤
      Real.exp (-Real.exp (Real.log n ^ (3 / 5 : ℝ))) := by
  let firstLower : ℝ :=
    ((ThickPoint.candidateBox cert.scale).card : ℝ) *
      ((1 - cert.epsilon) * cert.onePoint)
  let successProbability : ℝ := firstLower ^ 2 / cert.pairUpper
  have hsuccess (i : Fin cert.blockCount) :
      successProbability ≤
        fairSteps.real
          (oneBlockSuccess cert.scale
            (stoppedThickPointEvent ((i : ℕ) * cert.blockLength) cert.scale
              cert.profileDelta cert.thickDelta)) := by
    simpa [successProbability, firstLower] using
      oneBlockSuccess_probability_lower fairSteps cert.scale
        (stoppedSuccessfulPointEvent ((i : ℕ) * cert.blockLength) cert.scale
          cert.profileDelta)
        (stoppedThickPointEvent ((i : ℕ) * cert.blockLength) cert.scale
          cert.profileDelta cert.thickDelta)
        cert.epsilon_le_one cert.onePoint_nonneg
        cert.pairUpper_pos
        (fun x _ ↦ measurableSet_stoppedSuccessfulPointEvent
          ((i : ℕ) * cert.blockLength) cert.scale cert.profileDelta x)
        (fun x _ ↦ measurableSet_stoppedThickPointEvent
          ((i : ℕ) * cert.blockLength) cert.scale cert.profileDelta cert.thickDelta x)
        (fun x _ ↦ stoppedThickPointEvent_subset_stoppedSuccessfulPointEvent
          ((i : ℕ) * cert.blockLength) cert.scale cert.profileDelta cert.thickDelta x)
        (cert.onePointProfile i)
        (fun x hx ↦ terminalLoss_of_thick_lower fairSteps
          (measurableSet_stoppedSuccessfulPointEvent
            ((i : ℕ) * cert.blockLength) cert.scale cert.profileDelta x)
          (measurableSet_stoppedThickPointEvent
            ((i : ℕ) * cert.blockLength) cert.scale cert.profileDelta
              cert.thickDelta x)
          (stoppedThickPointEvent_subset_stoppedSuccessfulPointEvent
            ((i : ℕ) * cert.blockLength) cert.scale cert.profileDelta
              cert.thickDelta x)
          (cert.terminalThick i x hx))
        (cert.pairMoment i)
  have hmeas (i : Fin cert.blockCount) :
      MeasurableSet
        (oneBlockSuccess cert.scale
          (stoppedThickPointEvent ((i : ℕ) * cert.blockLength) cert.scale
            cert.profileDelta cert.thickDelta)) :=
    measurableSet_oneBlockSuccess fun x _ ↦
      measurableSet_stoppedThickPointEvent ((i : ℕ) * cert.blockLength) cert.scale
        cert.profileDelta cert.thickDelta x
  have hlate (i : Fin cert.blockCount) :
      fairSteps.real
          (lateExitEvent ((i : ℕ) * cert.blockLength) (0, 0)
            (outerExitRadius cert.scale) cert.blockLength) ≤
        Real.exp (-exitExponent (outerExitRadius cert.scale) cert.blockLength) :=
    measureReal_lateExitEvent_le ((i : ℕ) * cert.blockLength) (0, 0)
      (outerExitRadius cert.scale) cert.blockLength
  have hfail (i : Fin cert.blockCount) :
      fairSteps.real (cert.timedSuccess i)ᶜ ≤ Real.exp (-cert.blockRate) := by
    let stopped := oneBlockSuccess cert.scale
      (stoppedThickPointEvent ((i : ℕ) * cert.blockLength) cert.scale
        cert.profileDelta cert.thickDelta)
    let late := lateExitEvent ((i : ℕ) * cert.blockLength) (0, 0)
      (outerExitRadius cert.scale) cert.blockLength
    have hsubset : (cert.timedSuccess i)ᶜ ⊆ stoppedᶜ ∪ late :=
      deterministicFailure_subset_of_late
        (stoppedBlockSuccess_notLate_subset_boundedWord (i : ℕ)
          cert.blockLength cert.scale cert.profileDelta cert.thickDelta)
    have hstopped : fairSteps.real stoppedᶜ ≤ 1 - successProbability :=
      BlockAmplification.measureReal_compl_le_one_sub_of_le fairSteps stopped
        (hmeas i) (hsuccess i)
    calc
      fairSteps.real (cert.timedSuccess i)ᶜ ≤
          fairSteps.real (stoppedᶜ ∪ late) := measureReal_mono hsubset
      _ ≤ fairSteps.real stoppedᶜ + fairSteps.real late :=
        measureReal_union_le _ _
      _ ≤ (1 - successProbability) +
          Real.exp (-exitExponent (outerExitRadius cert.scale) cert.blockLength) :=
        add_le_add hstopped (hlate i)
      _ ≤ Real.exp (-cert.blockRate) := by
        simpa [successProbability, firstLower] using cert.oneBlockNumerical
  have hglobal := BlockAmplification.measureReal_globalFailure_le_doubleExp
    fairSteps cert.timedSuccess
      ((trajectory ⁻¹' lowerDeviationSet delta n)ᶜ)
      cert.independent_timed Finset.univ
      (fun i _ ↦ cert.timedSuccess_to_global i)
      (fun i _ ↦ hfail i) (by simpa using cert.enoughBlocks)
  simpa using hglobal

lemma measurableSet_lowerDeviationSet (delta : ℝ) (n : ℕ) :
    MeasurableSet (lowerDeviationSet delta n) := by
  exact measurableSet_lt
    ((measurable_of_countable (fun u : Fin (n + 1) → Point ↦
      (maxLocalTimePrefix u : ℝ))).comp (measurable_pathPrefix n))
    measurable_const

/-- **Full Proposition 1.3 assembly.**  Certificates containing the explicit
one-point profile estimate, terminal-local-time loss, summed pair estimate,
and deterministic block construction imply HLOZ's lower-deviation estimate
for the canonical planar simple random walk. -/
theorem hasPlanarMaximumLowerDeviation_of_appendixCertificates
    (hcert : HasAppendixCertificates) :
    HasPlanarMaximumLowerDeviation simpleRandomWalk := by
  intro delta hdelta
  obtain ⟨N, hN⟩ := hcert delta hdelta
  refine ⟨2, by norm_num, N, ?_⟩
  intro n hn
  let cert : ScaleCertificate delta n := Classical.choice (hN n hn)
  have hreal := cert.measureReal_lowerDeviation_le
  have hmeas := measurableSet_lowerDeviationSet delta n
  have hmap :
      simpleRandomWalk (lowerDeviationSet delta n) =
        fairSteps (trajectory ⁻¹' lowerDeviationSet delta n) := by
    rw [simpleRandomWalk,
      Measure.map_apply_of_aemeasurable measurable_trajectory.aemeasurable hmeas]
  rw [hmap]
  let b : ℝ := Real.exp (-Real.exp (Real.log n ^ (3 / 5 : ℝ)))
  have hb : 0 < b := Real.exp_pos _
  have hstrict :
      fairSteps.real (trajectory ⁻¹' lowerDeviationSet delta n) < 2 * b :=
    lt_of_le_of_lt (by simpa [b] using hreal) (by linarith)
  apply (ENNReal.toReal_lt_toReal (measure_ne_top _ _)
    ENNReal.ofReal_ne_top).mp
  simpa [Measure.real, b, ENNReal.toReal_ofReal hb.le] using hstrict

end

end Erdos1165.Proposition13Assembly
