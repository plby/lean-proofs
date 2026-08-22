/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
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

import ErdosProblems.Erdos1165.AnnularOffspringKernel
import ErdosProblems.Erdos1165.StrongMarkovFullTail
import ErdosProblems.Erdos1165.TerminalGlobalExitSplice
import ErdosProblems.Erdos1165.RealDiscFinite
import ErdosProblems.Erdos1165.LiteralRealAnnulus
import ErdosProblems.Erdos1165.TerminalBoundaryScan

/-!
# Exact renewal identity for the literal annular kernels

This file proves the renewal equation required by the endpoint-retaining
offspring algebra.  Its probabilistic input is the full-tail strong Markov
theorem.  The geometric input is stated as an ordering of literal first-hit
clocks: a separating boundary is hit no later than the boundary lying beyond
it.  The remaining hypotheses say that finite types enumerate the literal
inner and middle boundaries exactly.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators

namespace Erdos1165.AnnularOffspringRenewal

noncomputable section

open TerminalExcursionBridge TerminalSequentialVisitLaw
open MarkedBoundaryVisitKernel AnnularOffspringKernel
open AnnularBoundaryExcursionKernel
open BoundaryVisitRegeneration BoundaryVisitLaw
open PlanarPotential
open ThickPoint TerminalClockSplice TerminalBoundaryScan

/-- A literal boundary `barrier` separates `start` from `target` when its
first-hit clock is pathwise no later than the target first-hit clock. -/
def FirstHitSeparates (barrier target : Set Point) (start : Point) : Prop :=
  ∀ omega,
    boundaryExitTime barrier start omega ≤ boundaryExitTime target start omega

private lemma trajectoryFrom_add_shiftSteps_eq
    (start : Point) (omega : StepPath) (t q : ℕ) :
    trajectoryFrom (start + trajectory omega t) (shiftSteps t omega) q =
      trajectoryFrom start omega (t + q) := by
  unfold trajectoryFrom
  rw [← trajectory_add_sub_trajectory omega t q]
  abel

private lemma trajectoryFrom_shiftSteps_eq'
    (start : Point) (omega : StepPath) (t q : ℕ) :
    trajectoryFrom (trajectoryFrom start omega t) (shiftSteps t omega) q =
      trajectoryFrom start omega (t + q) := by
  unfold trajectoryFrom
  rw [← trajectory_add_sub_trajectory omega t q]
  abel

private lemma shiftSteps_add (omega : StepPath) (a b : ℕ) :
    shiftSteps b (shiftSteps a omega) = shiftSteps (a + b) omega := by
  funext q
  simp only [shiftSteps]
  congr 1
  omega

private lemma absoluteBoundaryFirstAt_shift
    {boundary : Set Point} {start point : Point} {omega : StepPath}
    {t N : ℕ} (hfirst : AbsoluteBoundaryFirstAt boundary start omega N)
    (htN : t ≤ N) (hpoint : trajectoryFrom start omega t = point) :
    AbsoluteBoundaryFirstAt boundary point (shiftSteps t omega) (N - t) := by
  change start + trajectory omega t = point at hpoint
  constructor
  · rw [← hpoint, trajectoryFrom_add_shiftSteps_eq,
      Nat.add_sub_of_le htN]
    exact hfirst.1
  · intro q hq
    rw [← hpoint, trajectoryFrom_add_shiftSteps_eq]
    exact hfirst.2 (t + q) (by omega)

private lemma absoluteBoundaryFirstAt_concat
    {boundary : Set Point} {start point : Point} {omega : StepPath}
    {t M : ℕ} (hbefore : ∀ q < t,
      trajectoryFrom start omega q ∉ boundary)
    (hpoint : trajectoryFrom start omega t = point)
    (htail : AbsoluteBoundaryFirstAt boundary point
      (shiftSteps t omega) M) :
    AbsoluteBoundaryFirstAt boundary start omega (t + M) := by
  change start + trajectory omega t = point at hpoint
  constructor
  · rw [← trajectoryFrom_add_shiftSteps_eq, hpoint]
    exact htail.1
  · intro q hq
    by_cases hqt : q < t
    · exact hbefore q hqt
    · have htq : t ≤ q := Nat.le_of_not_gt hqt
      have hdiff : q - t < M := by omega
      rw [← Nat.add_sub_of_le htq, ← trajectoryFrom_add_shiftSteps_eq, hpoint]
      exact htail.2 (q - t) hdiff

private lemma point_add_zero_pair (x : Point) : x + (0, 0) = x := by
  change (x.1 + 0, x.2 + 0) = x
  simp

private lemma boundaryExitMarkedSteps_compose
    {barrier target : Set Point} {start endpoint : Point}
    (hsep : FirstHitSeparates barrier target start) :
    boundaryExitMarkedSteps target {endpoint} start =
      {omega |
        boundaryExitTime barrier start omega < ⊤ ∧
          postWithTopStoppingSteps (boundaryExitTime barrier start) omega ∈
            boundaryExitMarkedSteps target {endpoint}
              (start + stoppedPosition (boundaryExitTime barrier start) omega)} := by
  ext omega
  constructor
  · intro homega
    obtain ⟨N, hfirst, hendpoint⟩ :=
      (mem_boundaryExitMarkedSteps_iff_exists_first
        target {endpoint} start omega).mp homega
    have htargetTime : boundaryExitTime target start omega = N :=
      boundaryExitTime_eq_of_absoluteBoundaryFirstAt hfirst
    have hbarrierFinite : boundaryExitTime barrier start omega < ⊤ := by
      exact lt_of_le_of_lt ((hsep omega).trans_eq htargetTime)
        (WithTop.coe_lt_top N)
    have hbarrierNe : boundaryExitTime barrier start omega ≠ ⊤ :=
      WithTop.lt_top_iff_ne_top.mp hbarrierFinite
    lift boundaryExitTime barrier start omega to ℕ using hbarrierNe with t ht
    have htEq : boundaryExitTime barrier start omega = t := ht.symm
    have htN : t ≤ N := by
      have hs := hsep omega
      rw [htargetTime, htEq] at hs
      exact WithTop.coe_le_coe.mp hs
    have hpost : postWithTopStoppingSteps (boundaryExitTime barrier start) omega =
        shiftSteps t omega := postWithTopStoppingSteps_eq_shiftSteps_of_eq htEq
    have hposition : stoppedPosition (boundaryExitTime barrier start) omega =
        trajectory omega t := stoppedPosition_eq_of_eq htEq
    refine ⟨by rw [htEq]; exact WithTop.coe_lt_top t,
      (mem_boundaryExitMarkedSteps_iff_exists_first
        target {endpoint}
          (start + stoppedPosition (boundaryExitTime barrier start) omega)
          (postWithTopStoppingSteps (boundaryExitTime barrier start) omega)).mpr
        ⟨N - t, ?_, ?_⟩⟩
    · rw [hpost, hposition]
      constructor
      · rw [trajectoryFrom_add_shiftSteps_eq, Nat.add_sub_of_le htN]
        exact hfirst.1
      · intro q hq
        rw [trajectoryFrom_add_shiftSteps_eq]
        exact hfirst.2 (t + q) (by omega)
    · rw [hpost, hposition, trajectoryFrom_add_shiftSteps_eq,
        Nat.add_sub_of_le htN]
      exact hendpoint
  · rintro ⟨hbarrierFinite, hfuture⟩
    have hbarrierNe : boundaryExitTime barrier start omega ≠ ⊤ :=
      WithTop.lt_top_iff_ne_top.mp hbarrierFinite
    lift boundaryExitTime barrier start omega to ℕ using hbarrierNe with t ht
    have htEq : boundaryExitTime barrier start omega = t := ht.symm
    have hpost : postWithTopStoppingSteps (boundaryExitTime barrier start) omega =
        shiftSteps t omega := postWithTopStoppingSteps_eq_shiftSteps_of_eq htEq
    have hposition : stoppedPosition (boundaryExitTime barrier start) omega =
        trajectory omega t := stoppedPosition_eq_of_eq htEq
    obtain ⟨M, htailFirst, htailEndpoint⟩ :=
      (mem_boundaryExitMarkedSteps_iff_exists_first
        target {endpoint}
          (start + stoppedPosition (boundaryExitTime barrier start) omega)
          (postWithTopStoppingSteps (boundaryExitTime barrier start) omega)).mp
        hfuture
    refine (mem_boundaryExitMarkedSteps_iff_exists_first
      target {endpoint} start omega).mpr ⟨t + M, ?_, ?_⟩
    · constructor
      · rw [← trajectoryFrom_add_shiftSteps_eq, ← hpost, ← hposition]
        exact htailFirst.1
      · intro q hq
        by_cases hqt : q < t
        · intro hqTarget
          have htargetLe : boundaryExitTime target start omega ≤ q :=
            (firstHitSetAfter_le_iff zeroClock
              (relativeBoundary target start) omega q).mpr
              ⟨q, le_rfl, by simp [zeroClock], by
                change start + trajectory omega q ∈ target
                simpa only [trajectoryFrom] using hqTarget⟩
          have hbarrierLe : (t : WithTop ℕ) ≤ boundaryExitTime target start omega := by
            rw [← htEq]
            exact hsep omega
          exact (not_le_of_gt hqt)
            (WithTop.coe_le_coe.mp (hbarrierLe.trans htargetLe))
        · have htq : t ≤ q := Nat.le_of_not_gt hqt
          have hdiff : q - t < M := by omega
          have hqEq : t + (q - t) = q := Nat.add_sub_of_le htq
          rw [← hqEq, ← trajectoryFrom_add_shiftSteps_eq, ← hpost, ← hposition]
          exact htailFirst.2 (q - t) hdiff
    · rw [← trajectoryFrom_add_shiftSteps_eq, ← hpost, ← hposition]
      exact htailEndpoint

private lemma boundaryExitTime_fiber_eq_marked
    (boundary : Set Point) (start displacement : Point) :
    ((Set.univ ∩ {omega |
        stoppedPosition (boundaryExitTime boundary start) omega = displacement}) ∩
      {omega | boundaryExitTime boundary start omega < ⊤}) =
      boundaryExitMarkedSteps boundary {start + displacement} start := by
  ext omega
  simp only [mem_inter_iff, mem_univ, true_and, mem_ofPred_eq,
    boundaryExitMarkedSteps, mem_singleton_iff]
  constructor
  · rintro ⟨hposition, hfinite⟩
    exact ⟨hfinite, congrArg (start + ·) hposition⟩
  · rintro ⟨hfinite, hposition⟩
    refine ⟨?_, hfinite⟩
    exact add_left_cancel hposition

/-- Strong Markov at a separating literal boundary gives the exact
endpoint-kernel composition law. -/
theorem skeletonExitKernel_compose
    {barrier target : Set Point} {start endpoint : Point}
    (hsep : FirstHitSeparates barrier target start) :
    skeletonExitKernel target start endpoint =
      ∑' y : Point,
        skeletonExitKernel barrier start y *
          skeletonExitKernel target y endpoint := by
  let tau := boundaryExitTime barrier start
  have htau : IsStoppingTime incrementFiltration tau :=
    isStoppingTime_boundaryExitTime barrier start
  have hU : IsMeasurableAtWithTopStopping tau (Set.univ : Set StepPath) := by
    intro n
    simpa using htau.measurableSet_eq n
  let K : Point → Set StepPath := fun x ↦
    boundaryExitMarkedSteps target {endpoint} (start + x)
  have hK : ∀ x, MeasurableSet (K x) := fun x ↦
    measurableSet_boundaryExitMarkedSteps target {endpoint} (start + x)
  have hmarkov := strongMarkov_withTop_stoppedPosition_disintegration
    htau hU K hK
  have hevent : {omega : StepPath | omega ∈ Set.univ ∧ tau omega < ⊤ ∧
      postWithTopStoppingSteps tau omega ∈ K (stoppedPosition tau omega)} =
      boundaryExitMarkedSteps target {endpoint} start := by
    rw [boundaryExitMarkedSteps_compose hsep]
    simp only [tau, K, mem_univ, true_and]
  rw [hevent] at hmarkov
  rw [skeletonExitKernel, skeletonExitMarkKernel]
  rw [hmarkov]
  have htranslated := (Equiv.addLeft start).tsum_eq
    (fun y : Point ↦ skeletonExitKernel barrier start y *
      skeletonExitKernel target y endpoint)
  rw [← htranslated]
  apply tsum_congr
  intro x
  rw [boundaryExitTime_fiber_eq_marked]
  rfl

/-! ## Finite boundary enumerations -/

/-- A finite type lists every point of a literal boundary exactly once. -/
def EnumeratesBoundary {Index : Type*}
    (point : Index → Point) (boundary : Set Point) : Prop :=
  Function.Injective point ∧ ∀ y, y ∈ boundary ↔ ∃ i, point i = y

theorem skeletonExitKernel_eq_zero_of_not_mem
    {boundary : Set Point} {start endpoint : Point}
    (hendpoint : endpoint ∉ boundary) :
    skeletonExitKernel boundary start endpoint = 0 := by
  rw [skeletonExitKernel, skeletonExitMarkKernel]
  have hevent : boundaryExitMarkedSteps boundary {endpoint} start = ∅ := by
    ext omega
    simp only [mem_empty_iff_false, iff_false]
    intro homega
    obtain ⟨N, hfirst, hmark⟩ :=
      (mem_boundaryExitMarkedSteps_iff_exists_first
        boundary {endpoint} start omega).mp homega
    exact hendpoint (by simpa using hmark ▸ hfirst.1)
  rw [hevent, measure_empty]

theorem skeletonExitKernel_self
    {boundary : Set Point} {start : Point} (hstart : start ∈ boundary) :
    skeletonExitKernel boundary start start = 1 := by
  rw [skeletonExitKernel, skeletonExitMarkKernel]
  have hevent : boundaryExitMarkedSteps boundary {start} start = Set.univ := by
    ext omega
    simp only [mem_univ, iff_true]
    apply (mem_boundaryExitMarkedSteps_iff_exists_first
      boundary {start} start omega).mpr
    refine ⟨0, ?_, by norm_num [trajectoryFrom]⟩
    constructor
    · simpa only [trajectoryFrom, trajectory_zero,
        point_add_zero_pair] using hstart
    · intro q hq
      omega
  rw [hevent, measure_univ]

theorem skeletonExitKernel_eq_zero_of_boundary_start_ne
    {boundary : Set Point} {start endpoint : Point}
    (hstart : start ∈ boundary) (hne : endpoint ≠ start) :
    skeletonExitKernel boundary start endpoint = 0 := by
  rw [skeletonExitKernel, skeletonExitMarkKernel]
  have hevent : boundaryExitMarkedSteps boundary {endpoint} start = ∅ := by
    ext omega
    simp only [mem_empty_iff_false, iff_false]
    intro homega
    obtain ⟨N, hfirst, hmark⟩ :=
      (mem_boundaryExitMarkedSteps_iff_exists_first
        boundary {endpoint} start omega).mp homega
    have hN : N = 0 := by
      by_contra hN0
      have hpos : 0 < N := Nat.pos_of_ne_zero hN0
      exact hfirst.2 0 hpos (by
        simpa only [trajectoryFrom, trajectory_zero,
          point_add_zero_pair] using hstart)
    subst N
    apply hne
    simpa only [trajectoryFrom, trajectory_zero,
      point_add_zero_pair] using hmark.symm
  rw [hevent, measure_empty]

theorem FirstHitSeparates.of_subset
    {barrier target : Set Point} {start : Point}
    (hsubset : target ⊆ barrier) :
    FirstHitSeparates barrier target start := by
  intro omega
  by_cases htop : boundaryExitTime target start omega = ⊤
  · rw [htop]
    exact le_top
  · lift boundaryExitTime target start omega to ℕ using htop with N hN
    have htargetTime : boundaryExitTime target start omega = N := hN.symm
    have hspec := (firstHitSetAfter_eq_coe_iff zeroClock
      (relativeBoundary target start) omega N).mp htargetTime
    have hbarrierMem : trajectory omega N ∈ relativeBoundary barrier start := by
      exact hsubset hspec.2.1
    have hle : boundaryExitTime barrier start omega ≤ N :=
      (firstHitSetAfter_le_iff zeroClock
        (relativeBoundary barrier start) omega N).mpr
        ⟨N, le_rfl, hspec.1, hbarrierMem⟩
    exact hle

/-- The inner vertex boundary of `domain` separates every point of the
domain from a target lying outside it.  This is the pathwise crossing lemma
used for nested literal real discs. -/
theorem FirstHitSeparates.innerBoundary
    {domain target : Set Point} {start : Point}
    (hstart : start ∈ domain) (htarget : target ⊆ domainᶜ) :
    FirstHitSeparates (ThickPoint.innerBoundary domain) target start := by
  classical
  intro omega
  by_cases htop : boundaryExitTime target start omega = ⊤
  · rw [htop]
    exact le_top
  · lift boundaryExitTime target start omega to ℕ using htop with N hN
    have htargetTime : boundaryExitTime target start omega = N := hN.symm
    have hspec := (firstHitSetAfter_eq_coe_iff zeroClock
      (relativeBoundary target start) omega N).mp htargetTime
    have hNtarget : trajectoryFrom start omega N ∈ target := by
      exact hspec.2.1
    have hNoutside : trajectoryFrom start omega N ∉ domain :=
      htarget hNtarget
    let hexit : ∃ n : ℕ, trajectoryFrom start omega n ∉ domain :=
      ⟨N, hNoutside⟩
    let t : ℕ := Nat.find hexit
    have htOutside : trajectoryFrom start omega t ∉ domain :=
      Nat.find_spec hexit
    have htN : t ≤ N := Nat.find_min' hexit hNoutside
    have htpos : 0 < t := by
      by_contra ht0
      have htEq : t = 0 := Nat.eq_zero_of_not_pos ht0
      rw [htEq] at htOutside
      exact htOutside (by
        simpa only [trajectoryFrom, trajectory_zero,
          point_add_zero_pair] using hstart)
    let q : ℕ := t - 1
    have hqt : q < t := by
      dsimp only [q]
      omega
    have hqInside : trajectoryFrom start omega q ∈ domain := by
      exact Classical.byContradiction fun hqOutside ↦
        Nat.find_min hexit (by simpa only [t] using hqt) hqOutside
    have hqSucc : q + 1 = t := by
      dsimp only [q]
      omega
    have hqBoundary : trajectoryFrom start omega q ∈
        ThickPoint.innerBoundary domain := by
      refine ⟨hqInside, trajectoryFrom start omega t, htOutside, ?_⟩
      rw [← hqSucc]
      exact TerminalGlobalExitSplice.adjacent_trajectoryFrom_succ start omega q
    have hbarrierLe :
        boundaryExitTime (ThickPoint.innerBoundary domain) start omega ≤ q := by
      apply (firstHitSetAfter_le_iff zeroClock
        (relativeBoundary (ThickPoint.innerBoundary domain) start) omega q).mpr
      refine ⟨q, le_rfl, by simp [zeroClock], ?_⟩
      exact hqBoundary
    exact hbarrierLe.trans (WithTop.coe_le_coe.mpr (hqt.le.trans htN))

theorem enumeratesBoundary_discBoundaryPoint (center : Point) (R : ℝ) :
    EnumeratesBoundary
      (fun z : RealDiscFinite.DiscBoundaryPoint center R ↦ z.1)
      (ThickPoint.discBoundary center R) := by
  constructor
  · exact Subtype.val_injective
  · intro y
    constructor
    · exact fun hy ↦ ⟨⟨y, hy⟩, rfl⟩
    · rintro ⟨z, rfl⟩
      exact z.2

/-- Literal nested real-disc boundaries satisfy the pathwise clock ordering
needed by the renewal theorem. -/
theorem FirstHitSeparates.discBoundaries
    {center start : Point} {rInner rMiddle rOuter : ℝ}
    (hstart : start ∈ ThickPoint.discBoundary center rInner)
    (hInnerMiddle : rInner ≤ rMiddle)
    (hMiddleOuter : rMiddle + 1 ≤ rOuter) :
    FirstHitSeparates (ThickPoint.discBoundary center rMiddle)
      (ThickPoint.discBoundary center rOuter) start := by
  have hstartDisc : start ∈ ThickPoint.disc center rMiddle := by
    exact hstart.1.trans hInnerMiddle
  have houterOutside : ThickPoint.discBoundary center rOuter ⊆
      (ThickPoint.disc center rMiddle)ᶜ := by
    intro y hyOuter hyMiddle
    have hyOuter0 : y - center ∈ ThickPoint.discBoundary 0 rOuter :=
      (BoundaryStoppedHarnack.mem_discBoundary_translate
        center rOuter y).mp hyOuter
    have hyLower :=
      (LiteralRealAnnulus.discBoundary_zero_euclideanRadius_bounds_real
        hyOuter0).1
    have hyMiddle0 : y - center ∈ ThickPoint.disc 0 rMiddle :=
      (BoundaryStoppedHarnack.mem_disc_translate center rMiddle y).mp hyMiddle
    have hyUpper :
        PotentialEuclideanGeometry.euclideanRadius (y - center) ≤ rMiddle := by
      simpa [ThickPoint.disc,
        RadialHarnackSpecialization.latticeDistance_zero_eq_euclideanRadius]
        using hyMiddle0
    linarith
  simpa only [ThickPoint.discBoundary] using
    (FirstHitSeparates.innerBoundary hstartDisc houterOutside)

theorem discBoundaries_disjoint_of_separated
    (center : Point) {rInner rOuter : ℝ}
    (hsep : rInner + 1 ≤ rOuter) :
    Disjoint (ThickPoint.discBoundary center rInner)
      (ThickPoint.discBoundary center rOuter) := by
  rw [Set.disjoint_left]
  intro y hyInner hyOuter
  have hyInner0 : y - center ∈ ThickPoint.discBoundary 0 rInner :=
    (BoundaryStoppedHarnack.mem_discBoundary_translate
      center rInner y).mp hyInner
  have hyOuter0 : y - center ∈ ThickPoint.discBoundary 0 rOuter :=
    (BoundaryStoppedHarnack.mem_discBoundary_translate
      center rOuter y).mp hyOuter
  have hUpper :=
    (LiteralRealAnnulus.discBoundary_zero_euclideanRadius_bounds_real
      hyInner0).2
  have hLower :=
    (LiteralRealAnnulus.discBoundary_zero_euclideanRadius_bounds_real
      hyOuter0).1
  linarith

/-! ## Pathwise recursion of the literal excursion counter -/

private def addCompleted (c : ℕ) (state : BoundaryScanState) :
    BoundaryScanState := ⟨state.seekingOuter, c + state.completed⟩

private theorem visit_addCompleted
    (outer inner : Set Point)
    [DecidablePred (· ∈ outer)] [DecidablePred (· ∈ inner)]
    (c : ℕ) (state : BoundaryScanState) (x : Point) :
    visit outer inner (addCompleted c state) x =
      addCompleted c (visit outer inner state x) := by
  cases state with
  | mk seeking completed =>
      cases seeking <;> simp only [visit, addCompleted] <;>
        split_ifs <;> simp [Nat.add_assoc]

private theorem scanSegment_addCompleted
    (s : WalkPath) (outer inner : Set Point)
    [DecidablePred (· ∈ outer)] [DecidablePred (· ∈ inner)]
    (start length c : ℕ) (state : BoundaryScanState) :
    scanSegment s outer inner start length (addCompleted c state) =
      addCompleted c (scanSegment s outer inner start length state) := by
  induction length with
  | zero => rfl
  | succ length ih =>
      rw [scanSegment_succ, scanSegment_succ, ih, visit_addCompleted]

private theorem completedExcursionCount_shift_succ
    {s : WalkPath} {middle inner : Set Point}
    [DecidablePred (· ∈ middle)] [DecidablePred (· ∈ inner)]
    {t b horizon : ℕ}
    (hdisjoint : Disjoint middle inner)
    (hstart : s 0 ∈ middle)
    (hinner : IsFirstHitSegment s inner 0 t horizon)
    (hmiddle : IsFirstHitSegment s middle t b horizon) :
    completedExcursionCount s middle inner horizon =
      1 + completedExcursionCount (fun q ↦ s (b + q)) middle inner
        (horizon - b) := by
  have htpos : 0 < t :=
    IsFirstHitSegment.lt_of_mem_disjoint hdisjoint hstart hinner
  have htInner : s t ∈ inner := hinner.2.2.1
  have htb : t < b :=
    IsFirstHitSegment.lt_of_mem_disjoint hdisjoint.symm htInner hmiddle
  have hbH : b ≤ horizon := hmiddle.2.1
  let tail : WalkPath := fun q ↦ s (b + q)
  have hfirstVertex :
      scanSegment s middle inner 0 1 initialState = ⟨false, 0⟩ := by
    simp [scanSegment, initialState, visit, hstart]
  have hthroughInner :
      scanSegment s middle inner 1 t ⟨false, 0⟩ = ⟨true, 1⟩ := by
    simpa using scanSegment_after_firstInner_strict
      s middle inner hinner htpos (completed := 0)
  have hthroughMiddle :
      scanSegment s middle inner (t + 1) (b - t) ⟨true, 1⟩ =
        ⟨false, 1⟩ := by
    simpa using scanSegment_after_firstOuter_strict
      s middle inner hmiddle htb (completed := 1)
  have hprefix :
      scanSegment s middle inner 0 (b + 1) initialState = ⟨false, 1⟩ := by
    rw [show b + 1 = 1 + t + (b - t) by omega,
      scanSegment_add, scanSegment_add, hfirstVertex]
    simp only [Nat.zero_add]
    rw [hthroughInner]
    have hstartEq : 1 + t = t + 1 := by omega
    rw [hstartEq, hthroughMiddle]
  have htailStart :
      scanSegment tail middle inner 0 1 initialState = ⟨false, 0⟩ := by
    have htail0 : tail 0 ∈ middle := by
      dsimp only [tail]
      simpa using hmiddle.2.2.1
    simp [scanSegment, initialState, visit, htail0]
  have hrestCongr (state : BoundaryScanState) :
      scanSegment s middle inner (b + 1) (horizon - b) state =
        scanSegment tail middle inner 1 (horizon - b) state := by
    apply scanSegment_congr
    intro q _hq
    dsimp only [tail]
    apply congrArg s
    omega
  have hscan : scanThrough s middle inner horizon =
      addCompleted 1 (scanThrough tail middle inner (horizon - b)) := by
    rw [scanThrough, show horizon + 1 = (b + 1) + (horizon - b) by omega,
      scanSegment_add, hprefix]
    rw [scanThrough, show horizon - b + 1 = 1 + (horizon - b) by omega,
      scanSegment_add, htailStart]
    simp only [Nat.zero_add]
    rw [← scanSegment_addCompleted]
    exact hrestCongr (addCompleted 1 ⟨false, 0⟩)
  rw [← scanThrough_completed_eq_completedExcursionCount
      s middle inner hdisjoint horizon,
    ← scanThrough_completed_eq_completedExcursionCount
      tail middle inner hdisjoint (horizon - b), hscan]
  rfl

private theorem completedExcursionCount_eq_zero_of_avoids_inner
    {s : WalkPath} {middle inner : Set Point}
    [DecidablePred (· ∈ middle)] [DecidablePred (· ∈ inner)]
    {horizon : ℕ} (hdisjoint : Disjoint middle inner)
    (hstart : s 0 ∈ middle)
    (havoid : ∀ q ≤ horizon, s q ∉ inner) :
    completedExcursionCount s middle inner horizon = 0 := by
  have hfirstVertex :
      scanSegment s middle inner 0 1 initialState = ⟨false, 0⟩ := by
    simp [scanSegment, initialState, visit, hstart]
  have htail :
      scanSegment s middle inner 1 horizon ⟨false, 0⟩ = ⟨false, 0⟩ := by
    apply scanSegment_seekingInner_of_avoids
    intro q hq
    apply havoid (1 + q)
    omega
  have hscan : scanThrough s middle inner horizon = ⟨false, 0⟩ := by
    rw [scanThrough, show horizon + 1 = 1 + horizon by omega,
      scanSegment_add, hfirstVertex]
    simpa using htail
  rw [← scanThrough_completed_eq_completedExcursionCount
    s middle inner hdisjoint horizon, hscan]

private theorem completedExcursionCount_pos_of_inner_hit
    {s : WalkPath} {middle inner : Set Point}
    [DecidablePred (· ∈ middle)] [DecidablePred (· ∈ inner)]
    {horizon : ℕ} (hstart : s 0 ∈ middle)
    (hhit : ∃ q ≤ horizon, s q ∈ inner) :
    0 < completedExcursionCount s middle inner horizon := by
  apply (completedExcursionCount_pos_iff s middle inner horizon).mpr
  refine ⟨0, Nat.zero_le _, ?_⟩
  unfold excursionFinish excursionStart
  have hmiddleZero : firstHitThrough s middle 0 horizon = 0 := by
    apply firstHitThrough_eq_of_isFirstHitSegment
    refine ⟨le_rfl, Nat.zero_le _, hstart, ?_⟩
    intro q hq _
    omega
  obtain ⟨q, hqH, hqInner⟩ := hhit
  have hinner : firstHitThrough s inner 0 horizon ≤ horizon :=
    (firstHitThrough_le_horizon_iff s inner 0 horizon).mpr
      ⟨q, Finset.mem_filter.mpr
        ⟨Finset.mem_Icc.mpr ⟨Nat.zero_le q, hqH⟩, hqInner⟩⟩
  simpa only [Function.iterate_zero_apply, hmiddleZero] using hinner

/-! ## Recursive stopped atoms and their exact masses -/

theorem isMeasurableAtWithTopStopping_boundaryExitMarkedSteps
    (boundary mark : Set Point) (start : Point) :
    IsMeasurableAtWithTopStopping (boundaryExitTime boundary start)
      (boundaryExitMarkedSteps boundary mark start) := by
  intro n
  have heq : boundaryExitMarkedSteps boundary mark start ∩
      {omega | boundaryExitTime boundary start omega = (n : WithTop ℕ)} =
      {omega | boundaryExitTime boundary start omega = (n : WithTop ℕ)} ∩
        {omega | start + trajectory omega n ∈ mark} := by
    ext omega
    simp only [boundaryExitMarkedSteps, mem_inter_iff, mem_ofPred_eq]
    constructor
    · rintro ⟨⟨_hfinite, hmark⟩, htime⟩
      refine ⟨htime, ?_⟩
      rw [stoppedPosition_eq_of_eq htime] at hmark
      exact hmark
    · rintro ⟨htime, hmark⟩
      refine ⟨⟨htime ▸ WithTop.coe_lt_top n, ?_⟩, htime⟩
      rw [stoppedPosition_eq_of_eq htime]
      exact hmark
  rw [heq]
  have heval : {omega : StepPath | start + trajectory omega n ∈ mark} =
      {omega : StepPath | trajectory omega n ∈ {x | start + x ∈ mark}} := rfl
  rw [heval]
  exact ((isStoppingTime_boundaryExitTime boundary start).measurableSet_eq n).inter
    (measurableSet_trajectory_mem_incrementFiltration n
      {x | start + x ∈ mark})

private theorem boundaryExitMarkedSteps_subset_finite
    (boundary mark : Set Point) (start : Point) :
    boundaryExitMarkedSteps boundary mark start ⊆
      {omega | boundaryExitTime boundary start omega < ⊤} :=
  fun _ h ↦ h.1

private theorem measure_boundaryExitMarkedSteps_inter_post
    (boundary mark : Set Point) (start : Point)
    {C : Set StepPath} (hC : MeasurableSet C) :
    fairSteps (boundaryExitMarkedSteps boundary mark start ∩
        postWithTopStoppingSteps (boundaryExitTime boundary start) ⁻¹' C) =
      fairSteps (boundaryExitMarkedSteps boundary mark start) * fairSteps C := by
  have hmarkov := strongMarkov_withTop_fullTail_finiteEvent
    (isStoppingTime_boundaryExitTime boundary start)
    (isMeasurableAtWithTopStopping_boundaryExitMarkedSteps boundary mark start)
    hC
  have hfinite : boundaryExitMarkedSteps boundary mark start ∩
      {omega | boundaryExitTime boundary start omega < ⊤} =
      boundaryExitMarkedSteps boundary mark start := by
    apply Set.Subset.antisymm inter_subset_left
    intro omega homega
    exact ⟨homega,
      boundaryExitMarkedSteps_subset_finite boundary mark start homega⟩
  rw [hfinite] at hmarkov
  exact hmarkov

private theorem disjoint_boundaryExitMarkedSteps_of_ne
    (boundary : Set Point) (start a b : Point) (hab : a ≠ b) :
    Disjoint (boundaryExitMarkedSteps boundary {a} start)
      (boundaryExitMarkedSteps boundary {b} start) := by
  rw [Set.disjoint_left]
  intro omega ha hb
  exact hab (by simpa using ha.2.symm.trans hb.2)

/-- Recursive event of exactly `q` completed inner excursions, retaining all
intermediate endpoints and the final outer endpoint. -/
def annularRenewalAtom
    {Middle Inner Exit : Type*}
    [Fintype Middle] [Fintype Inner]
    (outer middle inner : Set Point)
    (middlePoint : Middle → Point) (innerPoint : Inner → Point)
    (exitPoint : Exit → Point) : ℕ → Middle → Exit → Set StepPath
  | 0, u, w =>
      boundaryExitMarkedSteps (inner ∪ outer) {exitPoint w} (middlePoint u)
  | q + 1, u, w =>
      ⋃ z : Inner,
        boundaryExitMarkedSteps (inner ∪ outer) {innerPoint z} (middlePoint u) ∩
          postWithTopStoppingSteps
              (boundaryExitTime (inner ∪ outer) (middlePoint u)) ⁻¹'
            (⋃ v : Middle,
              boundaryExitMarkedSteps middle {middlePoint v} (innerPoint z) ∩
                postWithTopStoppingSteps
                    (boundaryExitTime middle (innerPoint z)) ⁻¹'
                  annularRenewalAtom outer middle inner
                    middlePoint innerPoint exitPoint q v w)

theorem measurableSet_annularRenewalAtom
    {Middle Inner Exit : Type*}
    [Fintype Middle] [Fintype Inner]
    (outer middle inner : Set Point)
    (middlePoint : Middle → Point) (innerPoint : Inner → Point)
    (exitPoint : Exit → Point) :
    ∀ q u w, MeasurableSet (annularRenewalAtom outer middle inner
      middlePoint innerPoint exitPoint q u w) := by
  intro q
  induction q with
  | zero =>
      intro u w
      exact measurableSet_boundaryExitMarkedSteps _ _ _
  | succ q ih =>
      intro u w
      apply MeasurableSet.iUnion
      intro z
      apply (measurableSet_boundaryExitMarkedSteps _ _ _).inter
      apply MeasurableSet.preimage
      · apply MeasurableSet.iUnion
        intro v
        exact (measurableSet_boundaryExitMarkedSteps _ _ _).inter
          ((ih v w).preimage (measurable_postWithTopStoppingSteps
            (isStoppingTime_boundaryExitTime middle (innerPoint z))))
      · exact measurable_postWithTopStoppingSteps
          (isStoppingTime_boundaryExitTime (inner ∪ outer) (middlePoint u))

private theorem annularRenewalAtom_outer_pairwise
    {Middle Inner Exit : Type*}
    [Fintype Middle] [Fintype Inner]
    (outer middle inner : Set Point)
    (middlePoint : Middle → Point) (innerPoint : Inner → Point)
    (exitPoint : Exit → Point) (hinnerInjective : Function.Injective innerPoint)
    (q : ℕ) (u : Middle) (w : Exit) :
    Pairwise fun z z' : Inner ↦ Disjoint
      (boundaryExitMarkedSteps (inner ∪ outer) {innerPoint z} (middlePoint u) ∩
        postWithTopStoppingSteps
            (boundaryExitTime (inner ∪ outer) (middlePoint u)) ⁻¹'
          (⋃ v : Middle,
            boundaryExitMarkedSteps middle {middlePoint v} (innerPoint z) ∩
              postWithTopStoppingSteps
                  (boundaryExitTime middle (innerPoint z)) ⁻¹'
                annularRenewalAtom outer middle inner
                  middlePoint innerPoint exitPoint q v w))
      (boundaryExitMarkedSteps (inner ∪ outer) {innerPoint z'} (middlePoint u) ∩
        postWithTopStoppingSteps
            (boundaryExitTime (inner ∪ outer) (middlePoint u)) ⁻¹'
          (⋃ v : Middle,
            boundaryExitMarkedSteps middle {middlePoint v} (innerPoint z') ∩
              postWithTopStoppingSteps
                  (boundaryExitTime middle (innerPoint z')) ⁻¹'
                annularRenewalAtom outer middle inner
                  middlePoint innerPoint exitPoint q v w)) := by
  intro z z' hne
  exact (disjoint_boundaryExitMarkedSteps_of_ne
    (inner ∪ outer) (middlePoint u) (innerPoint z) (innerPoint z')
    (fun h ↦ hne (hinnerInjective h))).mono inter_subset_left inter_subset_left

private theorem annularRenewalAtom_inner_pairwise
    {Middle Inner Exit : Type*}
    [Fintype Middle] [Fintype Inner]
    (outer middle inner : Set Point)
    (middlePoint : Middle → Point) (innerPoint : Inner → Point)
    (exitPoint : Exit → Point) (hmiddleInjective : Function.Injective middlePoint)
    (q : ℕ) (z : Inner) (w : Exit) :
    Pairwise fun v v' : Middle ↦ Disjoint
      (boundaryExitMarkedSteps middle {middlePoint v} (innerPoint z) ∩
        postWithTopStoppingSteps (boundaryExitTime middle (innerPoint z)) ⁻¹'
          annularRenewalAtom outer middle inner
            middlePoint innerPoint exitPoint q v w)
      (boundaryExitMarkedSteps middle {middlePoint v'} (innerPoint z) ∩
        postWithTopStoppingSteps (boundaryExitTime middle (innerPoint z)) ⁻¹'
          annularRenewalAtom outer middle inner
            middlePoint innerPoint exitPoint q v' w) := by
  intro v v' hne
  exact (disjoint_boundaryExitMarkedSteps_of_ne middle (innerPoint z)
    (middlePoint v) (middlePoint v')
    (fun h ↦ hne (hmiddleInjective h))).mono inter_subset_left inter_subset_left

def markedOffspringKernelENNReal
    {State Exit : Type*} [Fintype State]
    (cycle : State → State → ℝ≥0∞) (escape : State → Exit → ℝ≥0∞) :
    ℕ → State → Exit → ℝ≥0∞
  | 0, u, w => escape u w
  | q + 1, u, w => ∑ v, cycle u v *
      markedOffspringKernelENNReal cycle escape q v w

@[simp] theorem markedOffspringKernelENNReal_zero
    {State Exit : Type*} [Fintype State]
    (cycle : State → State → ℝ≥0∞) (escape : State → Exit → ℝ≥0∞)
    (u : State) (w : Exit) :
    markedOffspringKernelENNReal cycle escape 0 u w = escape u w := rfl

theorem markedOffspringKernelENNReal_succ
    {State Exit : Type*} [Fintype State]
    (cycle : State → State → ℝ≥0∞) (escape : State → Exit → ℝ≥0∞)
    (q : ℕ) (u : State) (w : Exit) :
    markedOffspringKernelENNReal cycle escape (q + 1) u w =
      ∑ v, cycle u v * markedOffspringKernelENNReal cycle escape q v w := rfl

/-- The recursive stopped atom has exactly the iterated cycle/escape mass. -/
theorem fairSteps_annularRenewalAtom
    {Middle Inner Exit : Type*}
    [Fintype Middle] [Fintype Inner]
    (outer middle inner : Set Point)
    (middlePoint : Middle → Point) (innerPoint : Inner → Point)
    (exitPoint : Exit → Point)
    (hmiddleInjective : Function.Injective middlePoint)
    (hinnerInjective : Function.Injective innerPoint) :
    ∀ q u w,
      fairSteps (annularRenewalAtom outer middle inner
        middlePoint innerPoint exitPoint q u w) =
        markedOffspringKernelENNReal
          (annularCycleKernel outer middle inner middlePoint innerPoint)
          (annularEscapeKernel outer inner middlePoint exitPoint) q u w := by
  intro q
  induction q with
  | zero =>
      intro u w
      rfl
  | succ q ih =>
      intro u w
      rw [annularRenewalAtom, measure_iUnion
        (annularRenewalAtom_outer_pairwise outer middle inner middlePoint
          innerPoint exitPoint hinnerInjective q u w)]
      · rw [markedOffspringKernelENNReal_succ]
        have hz (z : Inner) :
            fairSteps
                (boundaryExitMarkedSteps (inner ∪ outer) {innerPoint z}
                    (middlePoint u) ∩
                  postWithTopStoppingSteps
                      (boundaryExitTime (inner ∪ outer) (middlePoint u)) ⁻¹'
                    (⋃ v : Middle,
                      boundaryExitMarkedSteps middle {middlePoint v}
                          (innerPoint z) ∩
                        postWithTopStoppingSteps
                            (boundaryExitTime middle (innerPoint z)) ⁻¹'
                          annularRenewalAtom outer middle inner middlePoint
                            innerPoint exitPoint q v w)) =
              skeletonExitKernel (inner ∪ outer) (middlePoint u) (innerPoint z) *
                ∑' v : Middle,
                  skeletonExitKernel middle (innerPoint z) (middlePoint v) *
                    markedOffspringKernelENNReal
                      (annularCycleKernel outer middle inner middlePoint innerPoint)
                      (annularEscapeKernel outer inner middlePoint exitPoint)
                      q v w := by
          rw [measure_boundaryExitMarkedSteps_inter_post]
          · rw [measure_iUnion
              (annularRenewalAtom_inner_pairwise outer middle inner middlePoint
                innerPoint exitPoint hmiddleInjective q z w)]
            · apply congrArg (fun a ↦
                fairSteps (boundaryExitMarkedSteps (inner ∪ outer)
                  {innerPoint z} (middlePoint u)) * a)
              apply tsum_congr
              intro v
              rw [measure_boundaryExitMarkedSteps_inter_post]
              · rw [ih]
                rfl
              · exact measurableSet_annularRenewalAtom outer middle inner
                  middlePoint innerPoint exitPoint q v w
            · intro v
              exact (measurableSet_boundaryExitMarkedSteps _ _ _).inter
                ((measurableSet_annularRenewalAtom outer middle inner middlePoint
                  innerPoint exitPoint q v w).preimage
                  (measurable_postWithTopStoppingSteps
                    (isStoppingTime_boundaryExitTime middle (innerPoint z))))
          · exact MeasurableSet.iUnion fun v ↦
              (measurableSet_boundaryExitMarkedSteps _ _ _).inter
                ((measurableSet_annularRenewalAtom outer middle inner middlePoint
                  innerPoint exitPoint q v w).preimage
                  (measurable_postWithTopStoppingSteps
                    (isStoppingTime_boundaryExitTime middle (innerPoint z))))
        calc
          (∑' z : Inner,
              fairSteps
                (boundaryExitMarkedSteps (inner ∪ outer) {innerPoint z}
                    (middlePoint u) ∩
                  postWithTopStoppingSteps
                      (boundaryExitTime (inner ∪ outer) (middlePoint u)) ⁻¹'
                    (⋃ v : Middle,
                      boundaryExitMarkedSteps middle {middlePoint v}
                          (innerPoint z) ∩
                        postWithTopStoppingSteps
                            (boundaryExitTime middle (innerPoint z)) ⁻¹'
                          annularRenewalAtom outer middle inner middlePoint
                            innerPoint exitPoint q v w))) =
              ∑' z : Inner,
                skeletonExitKernel (inner ∪ outer) (middlePoint u) (innerPoint z) *
                  ∑' v : Middle,
                    skeletonExitKernel middle (innerPoint z) (middlePoint v) *
                      markedOffspringKernelENNReal
                        (annularCycleKernel outer middle inner middlePoint innerPoint)
                        (annularEscapeKernel outer inner middlePoint exitPoint)
                        q v w := tsum_congr hz
          _ = ∑ v : Middle,
              annularCycleKernel outer middle inner middlePoint innerPoint u v *
                markedOffspringKernelENNReal
                  (annularCycleKernel outer middle inner middlePoint innerPoint)
                  (annularEscapeKernel outer inner middlePoint exitPoint)
                  q v w := by
            simp only [tsum_fintype]
            unfold annularCycleKernel
            simp_rw [Finset.mul_sum, Finset.sum_mul]
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro v _
            apply Finset.sum_congr rfl
            intro z _
            rw [mul_assoc]
      · intro z
        exact (measurableSet_boundaryExitMarkedSteps _ _ _).inter
          ((MeasurableSet.iUnion fun v ↦
            (measurableSet_boundaryExitMarkedSteps _ _ _).inter
              ((measurableSet_annularRenewalAtom outer middle inner middlePoint
                innerPoint exitPoint q v w).preimage
                (measurable_postWithTopStoppingSteps
                  (isStoppingTime_boundaryExitTime middle (innerPoint z))))) |>.preimage
            (measurable_postWithTopStoppingSteps
              (isStoppingTime_boundaryExitTime (inner ∪ outer) (middlePoint u))))

/-! ## Identification with the literal completed-excursion counter -/

/-- The recursive stopped atom is exactly the literal atom defined by the
completed-excursion counter. -/
theorem boundaryExcursionExitAtom_eq_annularRenewalAtom
    {Middle Inner Exit : Type*}
    [Fintype Middle] [Fintype Inner]
    (outer middle inner : Set Point)
    (middlePoint : Middle → Point) (innerPoint : Inner → Point)
    (exitPoint : Exit → Point)
    (hmiddle : EnumeratesBoundary middlePoint middle)
    (hinner : EnumeratesBoundary innerPoint inner)
    (houter : EnumeratesBoundary exitPoint outer)
    (hMiddleInner : Disjoint middle inner)
    (hInnerOuter : Disjoint inner outer)
    (_hMiddleOuter : Disjoint middle outer)
    (hseparates : ∀ z : Inner,
      FirstHitSeparates middle outer (innerPoint z)) :
    ∀ q u w,
      boundaryExcursionExitAtom outer middle inner (middlePoint u) q
          (exitPoint w) =
        annularRenewalAtom outer middle inner middlePoint innerPoint
          exitPoint q u w := by
  classical
  intro q
  induction q with
  | zero =>
      intro u w
      ext omega
      constructor
      · intro homega
        obtain ⟨N, houterFirst, hcount, hendpoint⟩ :=
          Set.mem_iUnion.mp homega
        let s : WalkPath := trajectoryFrom (middlePoint u) omega
        have hstart : s 0 ∈ middle := by
          dsimp only [s]
          simpa using (hmiddle.2 (middlePoint u)).mpr ⟨u, rfl⟩
        have havoid : ∀ r ≤ N, s r ∉ inner := by
          intro r hr hrInner
          have hpos := completedExcursionCount_pos_of_inner_hit
            hstart ⟨r, hr, hrInner⟩
          unfold boundaryExcursionCount at hcount
          dsimp only [s] at hpos
          rw [hcount] at hpos
          omega
        have hunionFirst : AbsoluteBoundaryFirstAt (inner ∪ outer)
            (middlePoint u) omega N := by
          refine ⟨Or.inr houterFirst.1, ?_⟩
          intro r hr
          exact fun hrUnion ↦ hrUnion.elim
            (havoid r hr.le) (houterFirst.2 r hr)
        change omega ∈ boundaryExitMarkedSteps (inner ∪ outer)
          {exitPoint w} (middlePoint u)
        apply (mem_boundaryExitMarkedSteps_iff_exists_first
          (inner ∪ outer) {exitPoint w} (middlePoint u) omega).mpr
        exact ⟨N, hunionFirst, by simpa using hendpoint⟩
      · intro homega
        change omega ∈ boundaryExitMarkedSteps (inner ∪ outer)
          {exitPoint w} (middlePoint u) at homega
        obtain ⟨N, hunionFirst, hendpoint⟩ :=
          (mem_boundaryExitMarkedSteps_iff_exists_first
            (inner ∪ outer) {exitPoint w} (middlePoint u) omega).mp homega
        have houterEndpoint : exitPoint w ∈ outer :=
          (houter.2 (exitPoint w)).mpr ⟨w, rfl⟩
        have hendpointEq : trajectoryFrom (middlePoint u) omega N =
            exitPoint w := by simpa using hendpoint
        have houterFirst : AbsoluteBoundaryFirstAt outer
            (middlePoint u) omega N := by
          refine ⟨hendpointEq ▸ houterEndpoint, ?_⟩
          intro r hr
          exact fun hrOuter ↦ hunionFirst.2 r hr (Or.inr hrOuter)
        let s : WalkPath := trajectoryFrom (middlePoint u) omega
        have hstart : s 0 ∈ middle := by
          dsimp only [s]
          simpa using (hmiddle.2 (middlePoint u)).mpr ⟨u, rfl⟩
        have havoid : ∀ r ≤ N, s r ∉ inner := by
          intro r hr
          by_cases hrN : r = N
          · subst r
            intro hrInner
            apply Set.disjoint_left.mp hInnerOuter (hendpointEq ▸ hrInner)
              houterEndpoint
          · exact fun hrInner ↦ hunionFirst.2 r (lt_of_le_of_ne hr hrN)
              (Or.inl hrInner)
        have hcount : boundaryExcursionCount middle inner (middlePoint u)
            omega N = 0 := by
          unfold boundaryExcursionCount
          exact completedExcursionCount_eq_zero_of_avoids_inner
            hMiddleInner hstart havoid
        exact Set.mem_iUnion.mpr
          ⟨N, houterFirst, hcount, hendpointEq⟩
  | succ q ih =>
      intro u w
      ext omega
      constructor
      · intro homega
        obtain ⟨N, houterFirst, hcount, hendpoint⟩ :=
          Set.mem_iUnion.mp homega
        let s : WalkPath := trajectoryFrom (middlePoint u) omega
        have hstart : s 0 ∈ middle := by
          dsimp only [s]
          simpa using (hmiddle.2 (middlePoint u)).mpr ⟨u, rfl⟩
        have hpositive : 0 < completedExcursionCount s middle inner N := by
          unfold boundaryExcursionCount at hcount
          change completedExcursionCount s middle inner N = q + 1 at hcount
          rw [hcount]
          omega
        obtain ⟨j, _hj, hjfinish⟩ :=
          (completedExcursionCount_pos_iff s middle inner N).mp hpositive
        have hinnerHit : ∃ r ≤ N, s r ∈ inner :=
          ⟨excursionFinish s middle inner N j, hjfinish,
            excursionFinish_mem_inner_of_le s middle inner N j hjfinish⟩
        let t := firstHitThrough s inner 0 N
        have htN : t ≤ N :=
          (firstHitThrough_le_horizon_iff s inner 0 N).mpr (by
            obtain ⟨r, hrN, hrInner⟩ := hinnerHit
            exact ⟨r, Finset.mem_filter.mpr
              ⟨Finset.mem_Icc.mpr ⟨Nat.zero_le r, hrN⟩, hrInner⟩⟩)
        have hinnerFirst : IsFirstHitSegment s inner 0 t N :=
          isFirstHitSegment_firstHitThrough_of_le s inner 0 N htN
        have htStrict : t < N := by
          have htNe : t ≠ N := by
            intro htEq
            exact Set.disjoint_left.mp hInnerOuter hinnerFirst.2.2.1
              (htEq ▸ houterFirst.1)
          omega
        have hunionFirst : AbsoluteBoundaryFirstAt (inner ∪ outer)
            (middlePoint u) omega t := by
          refine ⟨Or.inl hinnerFirst.2.2.1, ?_⟩
          intro r hr
          exact fun hrUnion ↦ hrUnion.elim
            (hinnerFirst.2.2.2 r (Nat.zero_le r) hr)
            (houterFirst.2 r (hr.trans htStrict))
        obtain ⟨z, hz⟩ := (hinner.2 (s t)).mp hinnerFirst.2.2.1
        have htPoint : trajectoryFrom (middlePoint u) omega t = innerPoint z :=
          hz.symm
        let omega₁ : StepPath := shiftSteps t omega
        have houterTail : AbsoluteBoundaryFirstAt outer (innerPoint z)
            omega₁ (N - t) := by
          dsimp only [omega₁]
          exact absoluteBoundaryFirstAt_shift houterFirst htN htPoint
        have houterTime : boundaryExitTime outer (innerPoint z) omega₁ =
            (N - t : ℕ) :=
          boundaryExitTime_eq_of_absoluteBoundaryFirstAt houterTail
        have hmiddleFinite : boundaryExitTime middle (innerPoint z) omega₁ < ⊤ :=
          lt_of_le_of_lt (hseparates z omega₁)
            (houterTime.symm ▸ WithTop.coe_lt_top (N - t))
        have hmiddleMarked : omega₁ ∈ boundaryExitMarkedSteps middle Set.univ
            (innerPoint z) := ⟨hmiddleFinite, Set.mem_univ _⟩
        obtain ⟨r, hmiddleFirst, _⟩ :=
          (mem_boundaryExitMarkedSteps_iff_exists_first middle Set.univ
            (innerPoint z) omega₁).mp hmiddleMarked
        have hmiddleTime : boundaryExitTime middle (innerPoint z) omega₁ = r :=
          boundaryExitTime_eq_of_absoluteBoundaryFirstAt hmiddleFirst
        have hrN : r ≤ N - t := by
          have hle := hseparates z omega₁
          rw [hmiddleTime, houterTime] at hle
          exact WithTop.coe_le_coe.mp hle
        obtain ⟨v, hv⟩ := (hmiddle.2
          (trajectoryFrom (innerPoint z) omega₁ r)).mp hmiddleFirst.1
        have hrPoint : trajectoryFrom (innerPoint z) omega₁ r = middlePoint v :=
          hv.symm
        let b := t + r
        have hbN : b ≤ N := by dsimp only [b]; omega
        have hmiddleSegment : IsFirstHitSegment s middle t b N := by
          refine ⟨by dsimp only [b]; omega, hbN, ?_, ?_⟩
          · dsimp only [s, b, omega₁]
            rw [← trajectoryFrom_shiftSteps_eq', htPoint]
            exact hmiddleFirst.1
          · intro a hta hab haMiddle
            let d := a - t
            have htd : t + d = a := Nat.add_sub_of_le hta
            have hdr : d < r := by dsimp only [b] at hab; omega
            apply hmiddleFirst.2 d hdr
            dsimp only [s, omega₁]
            rw [← htPoint, trajectoryFrom_shiftSteps_eq', htd]
            exact haMiddle
        have hshiftCount := completedExcursionCount_shift_succ
          hMiddleInner hstart hinnerFirst hmiddleSegment
        have htailCount : completedExcursionCount
            (fun a ↦ s (b + a)) middle inner (N - b) = q := by
          unfold boundaryExcursionCount at hcount
          change completedExcursionCount s middle inner N = q + 1 at hcount
          rw [hcount] at hshiftCount
          omega
        let omega₂ : StepPath := shiftSteps r omega₁
        have homega₂ : omega₂ = shiftSteps b omega := by
          dsimp only [omega₂, omega₁, b]
          exact shiftSteps_add omega t r
        have hbPoint : trajectoryFrom (middlePoint u) omega b = middlePoint v :=
          calc
            trajectoryFrom (middlePoint u) omega b =
                trajectoryFrom (innerPoint z) omega₁ r := by
              dsimp only [b, omega₁]
              rw [← trajectoryFrom_shiftSteps_eq', htPoint]
            _ = middlePoint v := hrPoint
        have houterTail₂ : AbsoluteBoundaryFirstAt outer (middlePoint v)
            omega₂ (N - b) := by
          rw [homega₂]
          exact absoluteBoundaryFirstAt_shift houterFirst hbN hbPoint
        have htailPath : trajectoryFrom (middlePoint v) omega₂ =
            fun a ↦ s (b + a) := by
          funext a
          rw [homega₂, ← hbPoint, trajectoryFrom_shiftSteps_eq']
        have htailAtom : omega₂ ∈ boundaryExcursionExitAtom outer middle inner
            (middlePoint v) q (exitPoint w) := by
          apply Set.mem_iUnion.mpr
          refine ⟨N - b, houterTail₂, ?_, ?_⟩
          · unfold boundaryExcursionCount
            rw [htailPath]
            exact htailCount
          · rw [htailPath]
            change s (b + (N - b)) = exitPoint w
            rw [Nat.add_sub_of_le hbN]
            exact hendpoint
        rw [annularRenewalAtom]
        apply Set.mem_iUnion.mpr
        refine ⟨z, ?_, ?_⟩
        · exact (mem_boundaryExitMarkedSteps_iff_of_absoluteBoundaryFirstAt
            hunionFirst).mpr (by simpa using htPoint)
        · simp only [mem_preimage]
          have hunionTime := boundaryExitTime_eq_of_absoluteBoundaryFirstAt
            hunionFirst
          rw [postWithTopStoppingSteps_eq_shiftSteps_of_eq hunionTime]
          change omega₁ ∈ _
          apply Set.mem_iUnion.mpr
          refine ⟨v, ?_, ?_⟩
          · exact (mem_boundaryExitMarkedSteps_iff_of_absoluteBoundaryFirstAt
              hmiddleFirst).mpr (by simpa using hrPoint)
          · simp only [mem_preimage]
            rw [postWithTopStoppingSteps_eq_shiftSteps_of_eq hmiddleTime]
            change omega₂ ∈ _
            rw [← ih v w]
            exact htailAtom
      · intro homega
        rw [annularRenewalAtom] at homega
        obtain ⟨z, hzfirst, hzfuture⟩ := Set.mem_iUnion.mp homega
        obtain ⟨t, hunionFirst, htPointMem⟩ :=
          (mem_boundaryExitMarkedSteps_iff_exists_first
            (inner ∪ outer) {innerPoint z} (middlePoint u) omega).mp hzfirst
        have htPoint : trajectoryFrom (middlePoint u) omega t = innerPoint z := by
          simpa using htPointMem
        have hunionTime : boundaryExitTime (inner ∪ outer) (middlePoint u)
            omega = t := boundaryExitTime_eq_of_absoluteBoundaryFirstAt
              hunionFirst
        let omega₁ : StepPath := shiftSteps t omega
        simp only [mem_preimage] at hzfuture
        rw [postWithTopStoppingSteps_eq_shiftSteps_of_eq hunionTime] at hzfuture
        change omega₁ ∈ _ at hzfuture
        obtain ⟨v, hvfirst, hvfuture⟩ := Set.mem_iUnion.mp hzfuture
        obtain ⟨r, hmiddleFirst, hrPointMem⟩ :=
          (mem_boundaryExitMarkedSteps_iff_exists_first middle {middlePoint v}
            (innerPoint z) omega₁).mp hvfirst
        have hrPoint : trajectoryFrom (innerPoint z) omega₁ r = middlePoint v := by
          simpa using hrPointMem
        have hmiddleTime : boundaryExitTime middle (innerPoint z) omega₁ = r :=
          boundaryExitTime_eq_of_absoluteBoundaryFirstAt hmiddleFirst
        let omega₂ : StepPath := shiftSteps r omega₁
        simp only [mem_preimage] at hvfuture
        rw [postWithTopStoppingSteps_eq_shiftSteps_of_eq hmiddleTime] at hvfuture
        change omega₂ ∈ _ at hvfuture
        rw [← ih v w] at hvfuture
        obtain ⟨M, houterTail, htailCount, htailEndpoint⟩ :=
          Set.mem_iUnion.mp hvfuture
        let s : WalkPath := trajectoryFrom (middlePoint u) omega
        let b := t + r
        have homega₂ : omega₂ = shiftSteps b omega := by
          dsimp only [omega₂, omega₁, b]
          exact shiftSteps_add omega t r
        have hstart : s 0 ∈ middle := by
          dsimp only [s]
          simpa using (hmiddle.2 (middlePoint u)).mpr ⟨u, rfl⟩
        have hinnerSegment : IsFirstHitSegment s inner 0 t (b + M) := by
          refine ⟨Nat.zero_le _, by dsimp only [b]; omega, ?_, ?_⟩
          · dsimp only [s]
            exact htPoint ▸ (hinner.2 (innerPoint z)).mpr ⟨z, rfl⟩
          · intro a _hat hat haInner
            exact hunionFirst.2 a hat (Or.inl haInner)
        have hmiddleSegment : IsFirstHitSegment s middle t b (b + M) := by
          refine ⟨by dsimp only [b]; omega, by omega, ?_, ?_⟩
          · dsimp only [s, b, omega₁]
            rw [← trajectoryFrom_shiftSteps_eq', htPoint]
            exact hmiddleFirst.1
          · intro a hta hab haMiddle
            let d := a - t
            have htd : t + d = a := Nat.add_sub_of_le hta
            have hdr : d < r := by dsimp only [b] at hab; omega
            apply hmiddleFirst.2 d hdr
            dsimp only [s, omega₁]
            rw [← htPoint, trajectoryFrom_shiftSteps_eq', htd]
            exact haMiddle
        have hbPoint : trajectoryFrom (middlePoint u) omega b = middlePoint v :=
          calc
            trajectoryFrom (middlePoint u) omega b =
                trajectoryFrom (innerPoint z) omega₁ r := by
              dsimp only [b, omega₁]
              rw [← trajectoryFrom_shiftSteps_eq', htPoint]
            _ = middlePoint v := hrPoint
        have hbeforeOuter : ∀ a < b,
            trajectoryFrom (middlePoint u) omega a ∉ outer := by
          intro a hab haOuter
          by_cases hat : a < t
          · exact hunionFirst.2 a hat (Or.inr haOuter)
          · have hta : t ≤ a := Nat.le_of_not_gt hat
            let d := a - t
            have htd : t + d = a := Nat.add_sub_of_le hta
            have hdr : d < r := by dsimp only [b] at hab; omega
            have houterLe : boundaryExitTime outer (innerPoint z) omega₁ ≤ d := by
              apply (firstHitSetAfter_le_iff zeroClock
                (relativeBoundary outer (innerPoint z)) omega₁ d).mpr
              refine ⟨d, le_rfl, by simp [zeroClock], ?_⟩
              change innerPoint z + trajectory omega₁ d ∈ outer
              change trajectoryFrom (innerPoint z) omega₁ d ∈ outer
              dsimp only [s, omega₁]
              rw [← htPoint, trajectoryFrom_shiftSteps_eq', htd]
              exact haOuter
            have hmiddleLeOuter := hseparates z omega₁
            rw [hmiddleTime] at hmiddleLeOuter
            have hrd : (r : WithTop ℕ) ≤ d :=
              hmiddleLeOuter.trans houterLe
            exact (not_le_of_gt hdr) (WithTop.coe_le_coe.mp hrd)
        have houterFirst : AbsoluteBoundaryFirstAt outer (middlePoint u)
            omega (b + M) := by
          rw [homega₂] at houterTail htailEndpoint
          exact absoluteBoundaryFirstAt_concat hbeforeOuter hbPoint houterTail
        have htailPath : trajectoryFrom (middlePoint v) omega₂ =
            fun a ↦ s (b + a) := by
          funext a
          rw [homega₂, ← hbPoint, trajectoryFrom_shiftSteps_eq']
        have hshiftCount := completedExcursionCount_shift_succ
          hMiddleInner hstart hinnerSegment hmiddleSegment
        have hcount : boundaryExcursionCount middle inner (middlePoint u)
            omega (b + M) = q + 1 := by
          unfold boundaryExcursionCount at htailCount ⊢
          rw [htailPath] at htailCount
          change completedExcursionCount s middle inner (b + M) = q + 1
          rw [hshiftCount, Nat.add_sub_cancel_left, htailCount]
          omega
        have hendpoint : trajectoryFrom (middlePoint u) omega (b + M) =
            exitPoint w := by
          rw [← trajectoryFrom_shiftSteps_eq', hbPoint, ← homega₂]
          exact htailEndpoint
        exact Set.mem_iUnion.mpr
          ⟨b + M, houterFirst, hcount, hendpoint⟩

/-- Endpointwise, the literal count kernel is the ENNReal renewal iterate of
the actual cycle and escape kernels. -/
theorem boundaryExcursionExitKernel_eq_markedOffspringKernelENNReal
    {Middle Inner Exit : Type*}
    [Fintype Middle] [Fintype Inner]
    (outer middle inner : Set Point)
    (middlePoint : Middle → Point) (innerPoint : Inner → Point)
    (exitPoint : Exit → Point)
    (hmiddle : EnumeratesBoundary middlePoint middle)
    (hinner : EnumeratesBoundary innerPoint inner)
    (houter : EnumeratesBoundary exitPoint outer)
    (hMiddleInner : Disjoint middle inner)
    (hInnerOuter : Disjoint inner outer)
    (hMiddleOuter : Disjoint middle outer)
    (hseparates : ∀ z : Inner,
      FirstHitSeparates middle outer (innerPoint z))
    (q : ℕ) (u : Middle) (w : Exit) :
    boundaryExcursionExitKernel outer middle inner (middlePoint u) q
        (exitPoint w) =
      markedOffspringKernelENNReal
        (annularCycleKernel outer middle inner middlePoint innerPoint)
        (annularEscapeKernel outer inner middlePoint exitPoint) q u w := by
  unfold boundaryExcursionExitKernel
  rw [boundaryExcursionExitAtom_eq_annularRenewalAtom outer middle inner
    middlePoint innerPoint exitPoint hmiddle hinner houter hMiddleInner
    hInnerOuter hMiddleOuter hseparates q u w]
  exact fairSteps_annularRenewalAtom outer middle inner middlePoint innerPoint
    exitPoint hmiddle.1 hinner.1 q u w

theorem markedOffspringKernelENNReal_ne_top
    {State Exit : Type*} [Fintype State]
    (cycle : State → State → ℝ≥0∞) (escape : State → Exit → ℝ≥0∞)
    (hcycle : ∀ u v, cycle u v ≠ ⊤)
    (hescape : ∀ u w, escape u w ≠ ⊤) :
    ∀ q u w, markedOffspringKernelENNReal cycle escape q u w ≠ ⊤ := by
  intro q
  induction q with
  | zero => exact hescape
  | succ q ih =>
      intro u w
      rw [markedOffspringKernelENNReal_succ]
      exact ENNReal.sum_ne_top.mpr fun v _ ↦
        ENNReal.mul_ne_top (hcycle u v) (ih v w)

/-- Taking finite real parts commutes exactly with the finite-state ENNReal
renewal recursion. -/
theorem markedOffspringKernelENNReal_toReal
    {State Exit : Type*} [Fintype State]
    (cycle : State → State → ℝ≥0∞) (escape : State → Exit → ℝ≥0∞)
    (hcycle : ∀ u v, cycle u v ≠ ⊤)
    (hescape : ∀ u w, escape u w ≠ ⊤) :
    ∀ q u w,
      (markedOffspringKernelENNReal cycle escape q u w).toReal =
        markedOffspringKernel (fun u v ↦ (cycle u v).toReal)
          (fun u w ↦ (escape u w).toReal) q u w := by
  intro q
  induction q with
  | zero => exact fun _ _ ↦ rfl
  | succ q ih =>
      intro u w
      rw [markedOffspringKernelENNReal_succ, markedOffspringKernel_succ,
        ENNReal.toReal_sum]
      · simp_rw [ENNReal.toReal_mul, ih]
      · intro v _
        exact ENNReal.mul_ne_top (hcycle u v)
          (markedOffspringKernelENNReal_ne_top cycle escape hcycle hescape q v w)

/-- Summing the retained exit endpoint is exactly the integrated marked
offspring recursion. -/
theorem sum_markedOffspringKernel_eq_integratedMarkedOffspringKernel
    {State Exit : Type*} [Fintype State] [Fintype Exit]
    (cycle : State → State → ℝ) (escape : State → Exit → ℝ) :
    ∀ q u,
      (∑ w : Exit, markedOffspringKernel cycle escape q u w) =
        integratedMarkedOffspringKernel cycle (fun v ↦ ∑ w, escape v w) q u := by
  intro q
  induction q with
  | zero =>
      intro u
      rfl
  | succ q ih =>
      intro u
      simp only [markedOffspringKernel_succ, integratedMarkedOffspringKernel]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro v _
      rw [← Finset.mul_sum, ih]
      rfl

theorem boundaryExcursionExitKernel_eq_zero_of_not_mem
    {outer middle inner : Set Point} {start exit : Point} {q : ℕ}
    (hexit : exit ∉ outer) :
    boundaryExcursionExitKernel outer middle inner start q exit = 0 := by
  unfold boundaryExcursionExitKernel
  have hempty : boundaryExcursionExitAtom outer middle inner start q exit = ∅ := by
    ext omega
    constructor
    · intro homega
      obtain ⟨N, hfirst, _hcount, hendpoint⟩ := Set.mem_iUnion.mp homega
      exact (hexit (hendpoint ▸ hfirst.1)).elim
    · simp
  rw [hempty, measure_empty]

theorem skeletonExitKernel_compose_finite
    {Index : Type*} [Fintype Index]
    {barrier target : Set Point} {start endpoint : Point}
    {point : Index → Point}
    (hsep : FirstHitSeparates barrier target start)
    (henum : EnumeratesBoundary point barrier) :
    skeletonExitKernel target start endpoint =
      ∑ i, skeletonExitKernel barrier start (point i) *
        skeletonExitKernel target (point i) endpoint := by
  rw [skeletonExitKernel_compose hsep]
  let support : Finset Point := Finset.univ.image point
  rw [tsum_eq_sum (s := support)]
  · rw [Finset.sum_image]
    intro a _ b _ hab
    exact henum.1 hab
  · intro y hy
    have hynot : y ∉ barrier := by
      intro hybarrier
      obtain ⟨i, hi⟩ := (henum.2 y).mp hybarrier
      exact hy (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hi⟩)
    rw [skeletonExitKernel_eq_zero_of_not_mem hynot, zero_mul]

theorem enumeratesBoundary_sum_union
    {Left Right : Type*}
    {left right : Set Point} {leftPoint : Left → Point}
    {rightPoint : Right → Point}
    (hleft : EnumeratesBoundary leftPoint left)
    (hright : EnumeratesBoundary rightPoint right)
    (hdisjoint : Disjoint left right) :
    EnumeratesBoundary (Sum.elim leftPoint rightPoint) (left ∪ right) := by
  constructor
  · intro a b hab
    cases a with
    | inl a =>
        cases b with
        | inl b => exact congrArg Sum.inl (hleft.1 hab)
        | inr b =>
            exfalso
            change leftPoint a = rightPoint b at hab
            have ha : leftPoint a ∈ left := (hleft.2 _).mpr ⟨a, rfl⟩
            have hb : rightPoint b ∈ right := (hright.2 _).mpr ⟨b, rfl⟩
            exact Set.disjoint_left.mp hdisjoint (hab ▸ ha) hb
    | inr a =>
        cases b with
        | inl b =>
            exfalso
            change rightPoint a = leftPoint b at hab
            have ha : rightPoint a ∈ right := (hright.2 _).mpr ⟨a, rfl⟩
            have hb : leftPoint b ∈ left := (hleft.2 _).mpr ⟨b, rfl⟩
            exact Set.disjoint_left.mp hdisjoint hb (hab ▸ ha)
        | inr b => exact congrArg Sum.inr (hright.1 hab)
  · intro y
    rw [mem_union]
    constructor
    · rintro (hy | hy)
      · obtain ⟨i, rfl⟩ := (hleft.2 y).mp hy
        exact ⟨Sum.inl i, rfl⟩
      · obtain ⟨i, rfl⟩ := (hright.2 y).mp hy
        exact ⟨Sum.inr i, rfl⟩
    · rintro ⟨i, hi⟩
      cases i with
      | inl i => exact Or.inl ((hleft.2 y).mpr ⟨i, hi⟩)
      | inr i => exact Or.inr ((hright.2 y).mpr ⟨i, hi⟩)

/-! ## The literal annular renewal equation -/

/-- Exact `ENNReal` renewal identity before taking finite real parts. -/
theorem annularKernel_renewal_ennreal
    {Middle Inner Exit : Type*}
    [Fintype Middle] [Fintype Inner] [Fintype Exit]
    (outer middle inner : Set Point)
    (middlePoint : Middle → Point) (innerPoint : Inner → Point)
    (exitPoint : Exit → Point)
    (hmiddle : EnumeratesBoundary middlePoint middle)
    (hinner : EnumeratesBoundary innerPoint inner)
    (houter : EnumeratesBoundary exitPoint outer)
    (hdisjoint : Disjoint inner outer)
    (hseparates : ∀ z : Inner,
      FirstHitSeparates middle outer (innerPoint z))
    (u : Middle) (w : Exit) :
    annularUnmarkedKernel outer middlePoint exitPoint u w =
      annularEscapeKernel outer inner middlePoint exitPoint u w +
        ∑ v : Middle,
          annularCycleKernel outer middle inner
              middlePoint innerPoint u v *
            annularUnmarkedKernel outer middlePoint exitPoint v w := by
  let unionPoint : Inner ⊕ Exit → Point := Sum.elim innerPoint exitPoint
  have hunion : EnumeratesBoundary unionPoint (inner ∪ outer) :=
    enumeratesBoundary_sum_union hinner houter hdisjoint
  have hfirst := skeletonExitKernel_compose_finite
    (start := middlePoint u) (endpoint := exitPoint w)
    (FirstHitSeparates.of_subset (subset_union_right : outer ⊆ inner ∪ outer))
    hunion
  rw [Fintype.sum_sum_type] at hfirst
  have houterSum :
      (∑ e : Exit,
        skeletonExitKernel (inner ∪ outer) (middlePoint u) (exitPoint e) *
          skeletonExitKernel outer (exitPoint e) (exitPoint w)) =
        skeletonExitKernel (inner ∪ outer) (middlePoint u) (exitPoint w) := by
    classical
    rw [Finset.sum_eq_single w]
    · rw [skeletonExitKernel_self ((houter.2 (exitPoint w)).mpr ⟨w, rfl⟩),
        mul_one]
    · intro e _ hew
      have hpointNe : exitPoint w ≠ exitPoint e := by
        intro heq
        exact hew (houter.1 heq.symm)
      rw [skeletonExitKernel_eq_zero_of_boundary_start_ne
          ((houter.2 (exitPoint e)).mpr ⟨e, rfl⟩) hpointNe,
        mul_zero]
    · simp
  have hsecond (z : Inner) := skeletonExitKernel_compose_finite
    (start := innerPoint z) (endpoint := exitPoint w)
    (hseparates z) hmiddle
  change skeletonExitKernel outer (middlePoint u) (exitPoint w) = _
  change skeletonExitKernel outer (middlePoint u) (exitPoint w) =
      skeletonExitKernel (inner ∪ outer) (middlePoint u) (exitPoint w) +
        ∑ v : Middle,
          (∑ z : Inner,
            skeletonExitKernel (inner ∪ outer) (middlePoint u) (innerPoint z) *
              skeletonExitKernel middle (innerPoint z) (middlePoint v)) *
            skeletonExitKernel outer (middlePoint v) (exitPoint w)
  calc
    skeletonExitKernel outer (middlePoint u) (exitPoint w) =
        (∑ z : Inner,
          skeletonExitKernel (inner ∪ outer) (middlePoint u) (innerPoint z) *
            skeletonExitKernel outer (innerPoint z) (exitPoint w)) +
          skeletonExitKernel (inner ∪ outer) (middlePoint u) (exitPoint w) := by
      simpa only [unionPoint, Sum.elim_inl, Sum.elim_inr, houterSum] using hfirst
    _ = skeletonExitKernel (inner ∪ outer) (middlePoint u) (exitPoint w) +
        ∑ v : Middle,
          (∑ z : Inner,
            skeletonExitKernel (inner ∪ outer) (middlePoint u) (innerPoint z) *
              skeletonExitKernel middle (innerPoint z) (middlePoint v)) *
            skeletonExitKernel outer (middlePoint v) (exitPoint w) := by
      simp_rw [hsecond, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      ac_rfl

private theorem annularCycleKernel_ne_top
    {Middle Inner : Type*} [Fintype Inner]
    (outer middle inner : Set Point)
    (middlePoint : Middle → Point) (innerPoint : Inner → Point)
    (u v : Middle) :
    annularCycleKernel outer middle inner middlePoint innerPoint u v ≠ ⊤ := by
  unfold annularCycleKernel
  exact ENNReal.sum_ne_top.mpr fun z _ ↦
    ENNReal.mul_ne_top (measure_ne_top fairSteps _)
      (measure_ne_top fairSteps _)

private theorem annularEscapeKernel_ne_top
    {Middle Exit : Type*}
    (outer inner : Set Point)
    (middlePoint : Middle → Point) (exitPoint : Exit → Point)
    (u : Middle) (w : Exit) :
    annularEscapeKernel outer inner middlePoint exitPoint u w ≠ ⊤ :=
  measure_ne_top fairSteps _

private theorem annularUnmarkedKernel_ne_top
    {Middle Exit : Type*}
    (outer : Set Point)
    (middlePoint : Middle → Point) (exitPoint : Exit → Point)
    (u : Middle) (w : Exit) :
    annularUnmarkedKernel outer middlePoint exitPoint u w ≠ ⊤ :=
  measure_ne_top fairSteps _

/-- Real-valued endpointwise identification with the actual literal
cycle/escape kernels. -/
theorem boundaryExcursionExitKernel_toReal_eq_markedOffspringKernel
    {Middle Inner Exit : Type*}
    [Fintype Middle] [Fintype Inner]
    (outer middle inner : Set Point)
    (middlePoint : Middle → Point) (innerPoint : Inner → Point)
    (exitPoint : Exit → Point)
    (hmiddle : EnumeratesBoundary middlePoint middle)
    (hinner : EnumeratesBoundary innerPoint inner)
    (houter : EnumeratesBoundary exitPoint outer)
    (hMiddleInner : Disjoint middle inner)
    (hInnerOuter : Disjoint inner outer)
    (hMiddleOuter : Disjoint middle outer)
    (hseparates : ∀ z : Inner,
      FirstHitSeparates middle outer (innerPoint z))
    (q : ℕ) (u : Middle) (w : Exit) :
    (boundaryExcursionExitKernel outer middle inner (middlePoint u) q
        (exitPoint w)).toReal =
      markedOffspringKernel
        (annularCycleKernelReal outer middle inner middlePoint innerPoint)
        (annularEscapeKernelReal outer inner middlePoint exitPoint) q u w := by
  rw [boundaryExcursionExitKernel_eq_markedOffspringKernelENNReal
    outer middle inner middlePoint innerPoint exitPoint hmiddle hinner houter
    hMiddleInner hInnerOuter hMiddleOuter hseparates q u w]
  unfold annularCycleKernelReal annularEscapeKernelReal
  exact markedOffspringKernelENNReal_toReal
      (annularCycleKernel outer middle inner middlePoint innerPoint)
      (annularEscapeKernel outer inner middlePoint exitPoint)
      (annularCycleKernel_ne_top outer middle inner middlePoint innerPoint)
      (annularEscapeKernel_ne_top outer inner middlePoint exitPoint) q u w

/-- ENNReal form of the endpointwise identification, expressed through the
real offspring kernel used by the analytic algebra. -/
theorem boundaryExcursionExitKernel_eq_ofReal_markedOffspringKernel
    {Middle Inner Exit : Type*}
    [Fintype Middle] [Fintype Inner]
    (outer middle inner : Set Point)
    (middlePoint : Middle → Point) (innerPoint : Inner → Point)
    (exitPoint : Exit → Point)
    (hmiddle : EnumeratesBoundary middlePoint middle)
    (hinner : EnumeratesBoundary innerPoint inner)
    (houter : EnumeratesBoundary exitPoint outer)
    (hMiddleInner : Disjoint middle inner)
    (hInnerOuter : Disjoint inner outer)
    (hMiddleOuter : Disjoint middle outer)
    (hseparates : ∀ z : Inner,
      FirstHitSeparates middle outer (innerPoint z))
    (q : ℕ) (u : Middle) (w : Exit) :
    boundaryExcursionExitKernel outer middle inner (middlePoint u) q
        (exitPoint w) =
      ENNReal.ofReal
        (markedOffspringKernel
          (annularCycleKernelReal outer middle inner middlePoint innerPoint)
          (annularEscapeKernelReal outer inner middlePoint exitPoint) q u w) := by
  let K := boundaryExcursionExitKernel outer middle inner (middlePoint u) q
    (exitPoint w)
  have hfinite : K ≠ ⊤ := by
    dsimp only [K, boundaryExcursionExitKernel]
    exact measure_ne_top fairSteps _
  calc
    K = ENNReal.ofReal K.toReal :=
      (ENNReal.ofReal_toReal hfinite).symm
    _ = ENNReal.ofReal
        (markedOffspringKernel
          (annularCycleKernelReal outer middle inner middlePoint innerPoint)
          (annularEscapeKernelReal outer inner middlePoint exitPoint) q u w) := by
      apply congrArg ENNReal.ofReal
      exact boundaryExcursionExitKernel_toReal_eq_markedOffspringKernel
        outer middle inner middlePoint innerPoint exitPoint hmiddle hinner houter
        hMiddleInner hInnerOuter hMiddleOuter hseparates q u w

/-- After summing the literal outer endpoint, the exact count kernel is the
integrated marked offspring kernel of the actual real cycle and escape
kernels. -/
theorem literalGapIntegratedMarkedKernel_toReal_eq_integratedMarkedOffspringKernel
    {Middle Inner Exit : Type*}
    [Fintype Middle] [Fintype Inner] [Fintype Exit]
    (outer middle inner : Set Point)
    (middlePoint : Middle → Point) (innerPoint : Inner → Point)
    (exitPoint : Exit → Point)
    (hmiddle : EnumeratesBoundary middlePoint middle)
    (hinner : EnumeratesBoundary innerPoint inner)
    (houter : EnumeratesBoundary exitPoint outer)
    (hMiddleInner : Disjoint middle inner)
    (hInnerOuter : Disjoint inner outer)
    (hMiddleOuter : Disjoint middle outer)
    (hseparates : ∀ z : Inner,
      FirstHitSeparates middle outer (innerPoint z))
    (q : ℕ) (u : Middle) :
    (literalGapIntegratedMarkedKernel outer middle inner (middlePoint u) q).toReal =
      integratedMarkedOffspringKernel
        (annularCycleKernelReal outer middle inner middlePoint innerPoint)
        (fun v ↦ ∑ w : Exit,
          annularEscapeKernelReal outer inner middlePoint exitPoint v w) q u := by
  have hfiniteSum :
      (∑' y : Point,
        boundaryExcursionExitKernel outer middle inner (middlePoint u) q y) =
      ∑ w : Exit,
        boundaryExcursionExitKernel outer middle inner (middlePoint u) q
          (exitPoint w) := by
    let support : Finset Point := Finset.univ.image exitPoint
    rw [tsum_eq_sum (s := support)]
    · dsimp only [support]
      rw [Finset.sum_image]
      intro a _ b _ hab
      exact houter.1 hab
    · intro y hy
      have hynot : y ∉ outer := by
        intro hyouter
        obtain ⟨w, hw⟩ := (houter.2 y).mp hyouter
        exact hy (Finset.mem_image.mpr ⟨w, Finset.mem_univ w, hw⟩)
      rw [boundaryExcursionExitKernel_eq_zero_of_not_mem hynot]
  rw [literalGapIntegratedMarkedKernel_eq_tsum_exit]
  unfold literalGapMarkedKernel
  rw [hfiniteSum, ENNReal.toReal_sum]
  · simp_rw [boundaryExcursionExitKernel_toReal_eq_markedOffspringKernel
      outer middle inner middlePoint innerPoint exitPoint hmiddle hinner houter
      hMiddleInner hInnerOuter hMiddleOuter hseparates]
    exact sum_markedOffspringKernel_eq_integratedMarkedOffspringKernel
      (annularCycleKernelReal outer middle inner middlePoint innerPoint)
      (annularEscapeKernelReal outer inner middlePoint exitPoint) q u
  · intro w _
    unfold boundaryExcursionExitKernel
    exact measure_ne_top fairSteps _

/-- The actual literal real kernels satisfy the `IsRenewalKernel` premise of
the offspring algebra.  No kernel equality is assumed: it follows from the
two strong-Markov boundary compositions above. -/
theorem annularKernelsReal_isRenewalKernel
    {Middle Inner Exit : Type*}
    [Fintype Middle] [Fintype Inner] [Fintype Exit]
    (outer middle inner : Set Point)
    (middlePoint : Middle → Point) (innerPoint : Inner → Point)
    (exitPoint : Exit → Point)
    (hmiddle : EnumeratesBoundary middlePoint middle)
    (hinner : EnumeratesBoundary innerPoint inner)
    (houter : EnumeratesBoundary exitPoint outer)
    (hdisjoint : Disjoint inner outer)
    (hseparates : ∀ z : Inner,
      FirstHitSeparates middle outer (innerPoint z)) :
    IsRenewalKernel
      (annularCycleKernelReal outer middle inner middlePoint innerPoint)
      (annularEscapeKernelReal outer inner middlePoint exitPoint)
      (annularUnmarkedKernelReal outer middlePoint exitPoint) := by
  intro u w
  have hrenewal := annularKernel_renewal_ennreal outer middle inner
    middlePoint innerPoint exitPoint hmiddle hinner houter hdisjoint
    hseparates u w
  unfold annularUnmarkedKernelReal annularEscapeKernelReal
  rw [hrenewal, ENNReal.toReal_add
    (annularEscapeKernel_ne_top outer inner middlePoint exitPoint u w)]
  · rw [ENNReal.toReal_sum]
    · simp only [ENNReal.toReal_mul]
      unfold kernelAction annularCycleKernelReal
      rfl
    intro v _
    exact ENNReal.mul_ne_top
      (annularCycleKernel_ne_top outer middle inner middlePoint innerPoint u v)
      (annularUnmarkedKernel_ne_top outer middlePoint exitPoint v w)
  · exact ENNReal.sum_ne_top.mpr fun v _ ↦
      ENNReal.mul_ne_top
        (annularCycleKernel_ne_top outer middle inner middlePoint innerPoint u v)
        (annularUnmarkedKernel_ne_top outer middlePoint exitPoint v w)

/-- Fully discharged specialization to three nested literal real-radius disc
boundaries, using their canonical finite subtypes. -/
theorem literalRealDiscKernels_isRenewalKernel
    (center : Point) (rOuter rMiddle rInner : ℝ)
    (hInnerMiddle : rInner ≤ rMiddle)
    (hMiddleOuter : rMiddle + 1 ≤ rOuter) :
    IsRenewalKernel
      (annularCycleKernelReal
        (ThickPoint.discBoundary center rOuter)
        (ThickPoint.discBoundary center rMiddle)
        (ThickPoint.discBoundary center rInner)
        (fun z : RealDiscFinite.DiscBoundaryPoint center rMiddle ↦ z.1)
        (fun z : RealDiscFinite.DiscBoundaryPoint center rInner ↦ z.1))
      (annularEscapeKernelReal
        (ThickPoint.discBoundary center rOuter)
        (ThickPoint.discBoundary center rInner)
        (fun z : RealDiscFinite.DiscBoundaryPoint center rMiddle ↦ z.1)
        (fun z : RealDiscFinite.DiscBoundaryPoint center rOuter ↦ z.1))
      (annularUnmarkedKernelReal
        (ThickPoint.discBoundary center rOuter)
        (fun z : RealDiscFinite.DiscBoundaryPoint center rMiddle ↦ z.1)
        (fun z : RealDiscFinite.DiscBoundaryPoint center rOuter ↦ z.1)) := by
  apply annularKernelsReal_isRenewalKernel
  · exact enumeratesBoundary_discBoundaryPoint center rMiddle
  · exact enumeratesBoundary_discBoundaryPoint center rInner
  · exact enumeratesBoundary_discBoundaryPoint center rOuter
  · apply discBoundaries_disjoint_of_separated
    linarith
  · intro z
    exact FirstHitSeparates.discBoundaries z.2 hInnerMiddle hMiddleOuter

end

end Erdos1165.AnnularOffspringRenewal
