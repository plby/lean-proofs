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

import ErdosProblems.Erdos1165.AsymmetricPairTwoStageMass
import ErdosProblems.Erdos1165.AnnularOffspringRenewal
import ErdosProblems.Erdos1165.MarkedBridgeFactorization
import ErdosProblems.Erdos1165.MarkedBoundaryVisitKernel
import ErdosProblems.Erdos1165.TerminalProfileClockEquivalence
import ErdosProblems.Erdos1165.TerminalRetainedHitSplice
import ErdosProblems.Erdos1165.TerminalSkeletonInvariance

/-!
# The asymmetric split-level splice

At the separation level one must not replace a whole annular gap: its
middle-to-inner and final escape pieces may affect the other point's outer
scanner.  We instead retain those pieces and erase only the inner-to-middle
return intervals.  The erased words are restricted to the subtype having
the same scanner transition as the source word.  Thus scanner preservation
is true by construction, while the restricted word mass is bounded by the
unrestricted first-boundary kernel.

This file contains the exact word/event/mass layer.  It does not condition a
future event at an entrance clock.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace Erdos1165.AsymmetricSplitLevelSplice

open ThickPoint TerminalExcursionPathwise TerminalSequentialVisitLaw
open TerminalSkeletonWords TerminalGlobalExitSplice
open TerminalRetainedHitSplice TerminalProfileClockEquivalence
open TerminalSkeletonInvariance
open MarkedBridgeFactorization
open MarkedBoundaryVisitKernel
open AsymmetricPairTwoStageMass
open AnnularBoundaryExcursionKernel AnnularOffspringRenewal
open AnnularProfileClocks

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## Restricting an exact complementary-skeleton factorization -/

/-- Restrict every erased bridge of an existing exact stopped-word
factorization by an arbitrary predicate.  Retained data and assembled words
are unchanged. -/
def restrictBridges
    {m : ℕ} {Complement : Type*} {Bridge : Fin m → Type*}
    (atom : ComplementarySkeletonAtom m Complement Bridge)
    (admissible : ∀ j, Bridge j → Prop) :
    ComplementarySkeletonAtom m Complement
      (fun j ↦ {b : Bridge j // admissible j b}) where
  complementWord := atom.complementWord
  bridgeWord := fun j b ↦ atom.bridgeWord j b.1
  assemble := fun code ↦ atom.assemble (code.1, fun j ↦ (code.2 j).1)
  prefixFree_assemble := by
    intro a b hab
    apply atom.prefixFree_assemble
    intro h
    apply hab
    cases a with
    | mk ac ab =>
      cases b with
      | mk bc bb =>
        simp only [Prod.mk.injEq] at h ⊢
        refine ⟨h.1, ?_⟩
        funext j
        exact Subtype.ext (congrFun h.2 j)
  prefixFree_bridge := by
    intro j a b hab
    apply atom.prefixFree_bridge j
    intro h
    exact hab (Subtype.ext h)
  length_assemble := by
    intro code
    simpa only using atom.length_assemble
      (code.1, fun j ↦ (code.2 j).1)

@[simp] theorem restrictBridges_complementWord
    {m : ℕ} {Complement : Type*} {Bridge : Fin m → Type*}
    (atom : ComplementarySkeletonAtom m Complement Bridge)
    (admissible : ∀ j, Bridge j → Prop) (c : Complement) :
    (restrictBridges atom admissible).complementWord c =
      atom.complementWord c := rfl

@[simp] theorem restrictBridges_bridgeWord
    {m : ℕ} {Complement : Type*} {Bridge : Fin m → Type*}
    (atom : ComplementarySkeletonAtom m Complement Bridge)
    (admissible : ∀ j, Bridge j → Prop) (j : Fin m)
    (b : {b : Bridge j // admissible j b}) :
    (restrictBridges atom admissible).bridgeWord j b =
      atom.bridgeWord j b.1 := rfl

@[simp] theorem restrictBridges_weight
    {m : ℕ} {Complement : Type*} {Bridge : Fin m → Type*}
    (atom : ComplementarySkeletonAtom m Complement Bridge)
    (admissible : ∀ j, Bridge j → Prop) :
    (restrictBridges atom admissible).weight = atom.weight := rfl

theorem restrictBridges_kernel_le
    {m : ℕ} {Complement : Type*} {Bridge : Fin m → Type*}
    (atom : ComplementarySkeletonAtom m Complement Bridge)
    (admissible : ∀ j, Bridge j → Prop) (j : Fin m) :
    (restrictBridges atom admissible).kernel j ≤ atom.kernel j := by
  exact ENNReal.tsum_comp_le_tsum_of_injective Subtype.coe_injective
    (fun b ↦ stoppedWordMass (atom.bridgeWord j b))

theorem restrictBridges_event_subset
    {m : ℕ} {Complement : Type*} {Bridge : Fin m → Type*}
    (atom : ComplementarySkeletonAtom m Complement Bridge)
    (admissible : ∀ j, Bridge j → Prop) :
    (restrictBridges atom admissible).event ⊆ atom.event := by
  intro omega homega
  rw [ComplementarySkeletonAtom.event, stoppedWordEvent] at homega ⊢
  obtain ⟨code, hcode⟩ := Set.mem_iUnion.mp homega
  exact Set.mem_iUnion.mpr
    ⟨(code.1, fun j ↦ (code.2 j).1), hcode⟩

/-- Exact fair-walk factorization survives the bridge restriction. -/
theorem fairSteps_restrictBridges
    {m : ℕ} {Complement : Type*} {Bridge : Fin m → Type*}
    [Countable Complement] [∀ j, Countable (Bridge j)]
    (atom : ComplementarySkeletonAtom m Complement Bridge)
    (admissible : ∀ j, Bridge j → Prop) :
    fairSteps (restrictBridges atom admissible).event =
      atom.weight * ∏ j, (restrictBridges atom admissible).kernel j := by
  simpa only [restrictBridges_weight] using
    fairSteps_event_eq_weight_mul_prod_kernel
      (restrictBridges atom admissible)

/-! ## The split-level compatibility subtype -/

/-- A replacement return word is admissible exactly when it has the same
effect as the retained source return word on the incoming `x` scanner state.
The endpoint is already fixed by the underlying first-boundary word code. -/
def ScanCompatible
    (outer inner : Set Point) (start : Point)
    (state : BoundaryScanState) {Code : Type*}
    (word : Code → StoppedWord) (source candidate : Code) : Prop :=
  scanWordFrom outer inner start state (List.ofFn (word candidate).2) =
    scanWordFrom outer inner start state (List.ofFn (word source).2)

@[simp] theorem scanCompatible_self
    (outer inner : Set Point) (start : Point)
    (state : BoundaryScanState) {Code : Type*}
    (word : Code → StoppedWord) (source : Code) :
    ScanCompatible outer inner start state word source source := rfl

/-- The actual source tuple always inhabits the compatible subtype. -/
def sourceCompatibleTuple
    {m : ℕ} {Bridge : Fin m → Type*}
    (outer inner : Fin m → Set Point) (start : Fin m → Point)
    (state : Fin m → BoundaryScanState)
    (word : (j : Fin m) → Bridge j → StoppedWord)
    (source : (j : Fin m) → Bridge j) :
    (j : Fin m) → {b : Bridge j //
      ScanCompatible (outer j) (inner j) (start j) (state j)
        (word j) (source j) b} :=
  fun j ↦ ⟨source j, scanCompatible_self _ _ _ _ _ _⟩

theorem compatibleTuple_scan_eq_source
    {m : ℕ} {Bridge : Fin m → Type*}
    (outer inner : Fin m → Set Point) (start : Fin m → Point)
    (state : Fin m → BoundaryScanState)
    (word : (j : Fin m) → Bridge j → StoppedWord)
    (source : (j : Fin m) → Bridge j)
    (candidate : (j : Fin m) → {b : Bridge j //
      ScanCompatible (outer j) (inner j) (start j) (state j)
        (word j) (source j) b}) (j : Fin m) :
    scanWordFrom (outer j) (inner j) (start j) (state j)
        (List.ofFn (word j (candidate j).1).2) =
      scanWordFrom (outer j) (inner j) (start j) (state j)
        (List.ofFn (word j (source j)).2) :=
  (candidate j).2

/-- First-boundary return words restricted to one retained scanner
transition.  This is the bridge type used only at the problematic split
level. -/
abbrev CompatibleReturnWordCode
    (scanOuter scanInner returnBoundary : Set Point)
    (start endpoint : Point) (state : BoundaryScanState)
    (source : MarkedBridgeFactorization.BoundaryExitWordCode
      returnBoundary start endpoint) :=
  {b : MarkedBridgeFactorization.BoundaryExitWordCode
      returnBoundary start endpoint //
    ScanCompatible scanOuter scanInner start state
      (fun c ↦ c.1) source b}

/-- Literal mass of a compatible return row. -/
def compatibleReturnKernel
    (scanOuter scanInner returnBoundary : Set Point)
    (start endpoint : Point) (state : BoundaryScanState)
    (source : MarkedBridgeFactorization.BoundaryExitWordCode
      returnBoundary start endpoint) : ℝ≥0∞ :=
  ∑' b : CompatibleReturnWordCode scanOuter scanInner returnBoundary
      start endpoint state source, stoppedWordMass b.1.1

/-- Compatibility restriction costs no more than the unrestricted joint
return-endpoint kernel. -/
theorem compatibleReturnKernel_le_skeletonExitKernel
    (scanOuter scanInner returnBoundary : Set Point)
    (start endpoint : Point) (state : BoundaryScanState)
    (source : MarkedBridgeFactorization.BoundaryExitWordCode
      returnBoundary start endpoint) :
    compatibleReturnKernel scanOuter scanInner returnBoundary
        start endpoint state source ≤
      skeletonExitKernel returnBoundary start endpoint := by
  calc
    compatibleReturnKernel scanOuter scanInner returnBoundary
        start endpoint state source ≤
        ∑' b : MarkedBridgeFactorization.BoundaryExitWordCode
          returnBoundary start endpoint, stoppedWordMass b.1 :=
      ENNReal.tsum_comp_le_tsum_of_injective Subtype.coe_injective _
    _ = fairSteps (boundaryExitEndpointSteps
          returnBoundary start endpoint) := by
      rw [boundaryExitEndpointSteps_eq_stoppedWordEvent,
        fairSteps_stoppedWordEvent
          (prefixFree_boundaryExitWordCode returnBoundary start endpoint)]
    _ = skeletonExitKernel returnBoundary start endpoint :=
      (skeletonExitKernel_eq_canonical returnBoundary start endpoint).symm

/-- The cylinder assembled from the retained complement and its source
return tuple belongs to the compatible insertion event. -/
theorem stoppedWordCylinder_source_subset_restrictedEvent
    {m : ℕ} {Complement : Type*} {Bridge : Fin m → Type*}
    (atom : ComplementarySkeletonAtom m Complement Bridge)
    (outer inner : Fin m → Set Point) (start : Fin m → Point)
    (state : Fin m → BoundaryScanState)
    (source : (j : Fin m) → Bridge j) (c : Complement) :
    stoppedWordCylinder (atom.assemble (c, source)) ⊆
      (restrictBridges atom (fun j b ↦
        ScanCompatible (outer j) (inner j) (start j) (state j)
          (atom.bridgeWord j) (source j) b)).event := by
  intro omega homega
  rw [ComplementarySkeletonAtom.event, stoppedWordEvent]
  apply Set.mem_iUnion.mpr
  refine ⟨(c, sourceCompatibleTuple outer inner start state
    atom.bridgeWord source), ?_⟩
  exact homega

def compatibleFixedComplementEvent
    {m : ℕ} {Complement : Type*} {Bridge : Fin m → Type*}
    (atom : ComplementarySkeletonAtom m Complement Bridge)
    (admissible : ∀ j, Bridge j → Prop) (c : Complement) : Set StepPath :=
  (fixComplement (restrictBridges atom admissible) c).event

/-- Conditional mass of the compatible return family at a fixed retained
word. -/
def compatibleFixedComplementWeight
    {m : ℕ} {Complement : Type*} {Bridge : Fin m → Type*}
    (atom : ComplementarySkeletonAtom m Complement Bridge)
    (admissible : ∀ j, Bridge j → Prop) : ℝ≥0∞ :=
  ∏ j, (restrictBridges atom admissible).kernel j

/-- Exact atom mass needed by the asymmetric two-stage constructor. -/
theorem fairSteps_compatibleFixedComplementEvent
    {m : ℕ} {Complement : Type*} {Bridge : Fin m → Type*}
    [∀ j, Countable (Bridge j)]
    (atom : ComplementarySkeletonAtom m Complement Bridge)
    (admissible : ∀ j, Bridge j → Prop) (c : Complement) :
    fairSteps (compatibleFixedComplementEvent atom admissible c) =
      compatibleFixedComplementWeight atom admissible *
        fairSteps (stoppedWordCylinder (atom.complementWord c)) := by
  exact fairSteps_fixComplement_event_eq_prod_mul_retainedCylinder
    (restrictBridges atom admissible) c

/-- The compatible row is pointwise bounded by the unrestricted bridge-row
product. -/
theorem compatibleFixedComplementWeight_le
    {m : ℕ} {Complement : Type*} {Bridge : Fin m → Type*}
    (atom : ComplementarySkeletonAtom m Complement Bridge)
    (admissible : ∀ j, Bridge j → Prop) :
    compatibleFixedComplementWeight atom admissible ≤
      ∏ j, atom.kernel j := by
  apply Finset.prod_le_prod
  · intro j _hj
    exact bot_le
  · intro j _hj
    exact restrictBridges_kernel_le atom admissible j

/-- Source-word coverage in the fixed-complement form consumed by the
two-stage mixture. -/
theorem stoppedWordCylinder_source_subset_compatibleFixedComplementEvent
    {m : ℕ} {Complement : Type*} {Bridge : Fin m → Type*}
    (atom : ComplementarySkeletonAtom m Complement Bridge)
    (outer inner : Fin m → Set Point) (start : Fin m → Point)
    (state : Fin m → BoundaryScanState)
    (source : (j : Fin m) → Bridge j) (c : Complement) :
    stoppedWordCylinder (atom.assemble (c, source)) ⊆
      compatibleFixedComplementEvent atom (fun j b ↦
        ScanCompatible (outer j) (inner j) (start j) (state j)
          (atom.bridgeWord j) (source j) b) c := by
  intro omega homega
  rw [compatibleFixedComplementEvent, ComplementarySkeletonAtom.event,
    stoppedWordEvent]
  apply Set.mem_iUnion.mpr
  refine ⟨(PUnit.unit, sourceCompatibleTuple outer inner start state
    atom.bridgeWord source), ?_⟩
  exact homega

/-! ## Literal extraction of the confined return intervals -/

noncomputable abbrev returnEntranceTime
    (omega : StepPath) (start : Point) (middle inner : Set Point)
    (horizon j : ℕ) : ℕ :=
  excursionFinish (PlanarPotential.trajectoryFrom start omega)
    middle inner horizon j

noncomputable abbrev returnExitTime
    (omega : StepPath) (start : Point) (middle inner : Set Point)
    (horizon j : ℕ) : ℕ :=
  excursionStart (PlanarPotential.trajectoryFrom start omega)
    middle inner horizon (j + 1)

noncomputable abbrev returnEntrancePoint
    (omega : StepPath) (start : Point) (middle inner : Set Point)
    (horizon j : ℕ) : Point :=
  PlanarPotential.trajectoryFrom start omega
    (returnEntranceTime omega start middle inner horizon j)

noncomputable abbrev returnExitPoint
    (omega : StepPath) (start : Point) (middle inner : Set Point)
    (horizon j : ℕ) : Point :=
  PlanarPotential.trajectoryFrom start omega
    (returnExitTime omega start middle inner horizon j)

/-- Timed deletion of the `q` inner-to-middle return pieces of one annular
renewal word.  The middle-to-inner legs and final escape remain in the
complementary pieces. -/
def extractTimedReturnSkeleton
    (omega : StepPath) (start : Point)
    (middle inner : Set Point) (horizon q : ℕ) :
    TimedTerminalSkeleton q :=
  { horizon := horizon
    entrance := fun j ↦ returnEntranceTime omega start middle inner horizon j
    exit := fun j ↦ returnExitTime omega start middle inner horizon j
    entrancePoint := fun j ↦ returnEntrancePoint omega start middle inner horizon j
    exitPoint := fun j ↦ returnExitPoint omega start middle inner horizon j }

/-- Completion of all selected returns is the only hypothesis needed for
chronological well-formedness of the split skeleton. -/
theorem extractTimedReturnSkeleton_wellFormed
    {omega : StepPath} {start : Point} {middle inner : Set Point}
    {horizon q : ℕ}
    (hcomplete : ∀ j : Fin q,
      excursionStart (PlanarPotential.trajectoryFrom start omega)
        middle inner horizon (j + 1) ≤ horizon) :
    (extractTimedReturnSkeleton omega start middle inner horizon q).WellFormed := by
  let s := PlanarPotential.trajectoryFrom start omega
  constructor
  · intro j
    exact ⟨excursionFinish_le_next_start s middle inner horizon j,
      hcomplete j⟩
  · intro i j hij
    exact (excursionStart_le_finish s middle inner horizon (i + 1)).trans
      (excursionFinish_mono s middle inner horizon (by omega))

/-- Reinsert the extracted return words into the retained middle-to-inner
spine and recover the original stopped prefix exactly. -/
theorem reconstruct_extractTimedReturnSkeleton
    {omega : StepPath} {start : Point} {middle inner : Set Point}
    {horizon q : ℕ}
    (hcomplete : ∀ j : Fin q,
      excursionStart (PlanarPotential.trajectoryFrom start omega)
        middle inner horizon (j + 1) ≤ horizon) :
    reconstructTerminalPacket
        (packetOfTimedSkeleton omega
          (extractTimedReturnSkeleton omega start middle inner horizon q)) =
      incrementSlice omega 0 horizon := by
  exact reconstruct_packetOfTimedSkeleton omega _
    (extractTimedReturnSkeleton_wellFormed hcomplete)

/-! ## Completion supplied by the literal annular-renewal atom -/

theorem trajectoryFrom_shiftSteps_eq_from
    (start : Point) (omega : StepPath) (t r : ℕ) :
    PlanarPotential.trajectoryFrom
        (PlanarPotential.trajectoryFrom start omega t)
        (shiftSteps t omega) r =
      PlanarPotential.trajectoryFrom start omega (t + r) := by
  unfold PlanarPotential.trajectoryFrom
  rw [← trajectory_add_sub_trajectory omega t r]
  abel

theorem absoluteBoundaryFirstAt_shift_from
    {boundary : Set Point} {start : Point} {omega : StepPath}
    {t horizon : ℕ}
    (hfirst : AbsoluteBoundaryFirstAt boundary start omega horizon)
    (ht : t ≤ horizon) :
    AbsoluteBoundaryFirstAt boundary
      (PlanarPotential.trajectoryFrom start omega t)
      (shiftSteps t omega) (horizon - t) := by
  constructor
  · rw [trajectoryFrom_shiftSteps_eq_from, Nat.add_sub_of_le ht]
    exact hfirst.1
  · intro r hr
    rw [trajectoryFrom_shiftSteps_eq_from]
    exact hfirst.2 (t + r) (by omega)

/-- Every completed inner hit occurring before a literal first outer exit
has a complete inner-to-middle return, provided the middle boundary
separates all inner points from the outer boundary. -/
theorem returnExitTime_le_of_boundaryExcursionExitAtom
    {outer middle inner : Set Point} {start : Point}
    {omega : StepPath} {q horizon : ℕ}
    (hfirst : AbsoluteBoundaryFirstAt outer start omega horizon)
    (hcount : boundaryExcursionCount middle inner start omega horizon = q)
    (hseparates : ∀ z ∈ inner,
      FirstHitSeparates middle outer z) :
    ∀ j : Fin q,
      returnExitTime omega start middle inner horizon j ≤ horizon := by
  intro j
  let s := PlanarPotential.trajectoryFrom start omega
  let a := excursionFinish s middle inner horizon (j : ℕ)
  have ha : a ≤ horizon := by
    apply finish_le_horizon_of_lt_completedExcursionCount
    unfold boundaryExcursionCount at hcount
    rw [hcount]
    exact j.isLt
  have hainner : s a ∈ inner :=
    excursionFinish_mem_inner_of_le s middle inner horizon j ha
  let tail := shiftSteps a omega
  have houterTail : AbsoluteBoundaryFirstAt outer (s a) tail (horizon - a) := by
    exact absoluteBoundaryFirstAt_shift_from hfirst ha
  have houterClock : boundaryExitTime outer (s a) tail = (horizon - a : ℕ) :=
    boundaryExitTime_eq_of_absoluteBoundaryFirstAt houterTail
  have hmiddleLe : boundaryExitTime middle (s a) tail ≤
      ((horizon - a : ℕ) : WithTop ℕ) := by
    calc
      boundaryExitTime middle (s a) tail ≤
          boundaryExitTime outer (s a) tail :=
        hseparates (s a) hainner tail
      _ = ((horizon - a : ℕ) : WithTop ℕ) := houterClock
  have hmiddleFinite : boundaryExitTime middle (s a) tail < ⊤ :=
    hmiddleLe.trans_lt (WithTop.coe_lt_top _)
  have hmarked : tail ∈ boundaryExitMarkedSteps middle Set.univ (s a) :=
    ⟨hmiddleFinite, Set.mem_univ _⟩
  obtain ⟨r, hrfirst, _⟩ :=
    (mem_boundaryExitMarkedSteps_iff_exists_first
      middle Set.univ (s a) tail).mp hmarked
  have hrClock : boundaryExitTime middle (s a) tail = r :=
    boundaryExitTime_eq_of_absoluteBoundaryFirstAt hrfirst
  have hrle : r ≤ horizon - a := by
    rw [hrClock] at hmiddleLe
    exact WithTop.coe_le_coe.mp hmiddleLe
  have hhit : s (a + r) ∈ middle := by
    change PlanarPotential.trajectoryFrom start omega (a + r) ∈ middle
    rw [← trajectoryFrom_shiftSteps_eq_from]
    exact hrfirst.1
  have htruncated : firstHitThrough s middle a horizon ≤ horizon := by
    apply (firstHitThrough_le_horizon_iff s middle a horizon).2
    refine ⟨a + r, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩,
      hhit⟩⟩
    · exact Nat.le_add_right a r
    · omega
  simpa only [returnExitTime,
    excursionStart_succ_eq_firstHitThrough_finish] using htruncated

/-- A literal exact-count/outer-endpoint atom canonically supplies a
well-formed return skeleton and its exact stopped-prefix reconstruction. -/
theorem boundaryExcursionExitAtom_extract_returnSkeleton
    {outer middle inner : Set Point} {start exit : Point}
    {omega : StepPath} {q : ℕ}
    (homega : omega ∈
      boundaryExcursionExitAtom outer middle inner start q exit)
    (hseparates : ∀ z ∈ inner,
      FirstHitSeparates middle outer z) :
    ∃ horizon,
      AbsoluteBoundaryFirstAt outer start omega horizon ∧
      boundaryExcursionCount middle inner start omega horizon = q ∧
      (extractTimedReturnSkeleton omega start middle inner horizon q).WellFormed ∧
      reconstructTerminalPacket
          (packetOfTimedSkeleton omega
            (extractTimedReturnSkeleton omega start middle inner horizon q)) =
        incrementSlice omega 0 horizon := by
  obtain ⟨horizon, hfirst, hcount, _hexit⟩ := Set.mem_iUnion.mp homega
  have hcomplete := returnExitTime_le_of_boundaryExcursionExitAtom
    hfirst hcount hseparates
  exact ⟨horizon, hfirst, hcount,
    extractTimedReturnSkeleton_wellFormed hcomplete,
    reconstruct_extractTimedReturnSkeleton hcomplete⟩

/-- Profile-boundary specialization of the literal renewal splitter.  The
only geometry is the standard nesting of the three consecutive radii. -/
theorem profileBoundaryExcursionExitAtom_extract_returnSkeleton
    {n k q : ℕ} {center start exit : Point} {omega : StepPath}
    (hInnerMiddle : scaleRadius n (k + 1) ≤ scaleRadius n k)
    (hMiddleOuter : scaleRadius n k + 1 ≤ scaleRadius n (k - 1))
    (homega : omega ∈ boundaryExcursionExitAtom
      (profileOuterBoundary n k center)
      (profileInnerBoundary n k center)
      (profileInnerBoundary n (k + 1) center) start q exit) :
    ∃ horizon,
      AbsoluteBoundaryFirstAt (profileOuterBoundary n k center)
          start omega horizon ∧
      boundaryExcursionCount
          (profileInnerBoundary n k center)
          (profileInnerBoundary n (k + 1) center)
          start omega horizon = q ∧
      (extractTimedReturnSkeleton omega start
          (profileInnerBoundary n k center)
          (profileInnerBoundary n (k + 1) center)
          horizon q).WellFormed ∧
      reconstructTerminalPacket
          (packetOfTimedSkeleton omega
            (extractTimedReturnSkeleton omega start
              (profileInnerBoundary n k center)
              (profileInnerBoundary n (k + 1) center)
              horizon q)) = incrementSlice omega 0 horizon := by
  apply boundaryExcursionExitAtom_extract_returnSkeleton homega
  intro z hz
  exact FirstHitSeparates.discBoundaries hz hInnerMiddle hMiddleOuter

/-- Transport an actual increment slice with an arbitrary spatial origin.
This is the small affine identity needed to certify the extracted return
word as a literal first-boundary word. -/
theorem trajectoryFrom_extendStoppedWord_incrementSlice_from
    (a : Point) (omega : StepPath) {start stop r : ℕ}
    (hstart : start ≤ stop) (hr : r ≤ stop - start) :
    PlanarPotential.trajectoryFrom
        (PlanarPotential.trajectoryFrom a omega start)
        (extendStoppedWord
          (TerminalVisitSpliceInvariance.stoppedWordOfList
            (incrementSlice omega start stop))) r =
      PlanarPotential.trajectoryFrom a omega (start + r) := by
  have hzero := trajectoryFrom_extendStoppedWord_incrementSlice
    omega hstart hr
  unfold PlanarPotential.trajectoryFrom at hzero ⊢
  simpa only [add_assoc] using congrArg (fun z ↦ a + z) hzero

/-- Any actual increment interval which first hits `boundary` at its right
endpoint gives the canonical prefix-free first-boundary code. -/
def incrementSliceBoundaryExitWordCode
    (a : Point) (omega : StepPath) (boundary : Set Point)
    {begin finish : ℕ} (hbegin : begin ≤ finish)
    (hend : PlanarPotential.trajectoryFrom a omega finish ∈ boundary)
    (havoid : ∀ r, begin ≤ r → r < finish →
      PlanarPotential.trajectoryFrom a omega r ∉ boundary) :
    MarkedBridgeFactorization.BoundaryExitWordCode boundary
      (PlanarPotential.trajectoryFrom a omega begin)
      (PlanarPotential.trajectoryFrom a omega finish) := by
  let w := TerminalVisitSpliceInvariance.stoppedWordOfList
    (incrementSlice omega begin finish)
  have hwlen : w.1 = finish - begin := by
    simp [w, TerminalVisitSpliceInvariance.stoppedWordOfList]
  refine ⟨w, ?_, ?_⟩
  · constructor
    · have htransport :=
        trajectoryFrom_extendStoppedWord_incrementSlice_from
          a omega hbegin (show finish - begin ≤ finish - begin from le_rfl)
      rw [hwlen, htransport, Nat.add_sub_of_le hbegin]
      exact hend
    · intro r hr
      have htransport :=
        trajectoryFrom_extendStoppedWord_incrementSlice_from
          a omega hbegin (by simpa only [hwlen] using hr.le)
      rw [htransport]
      apply havoid
      · exact Nat.le_add_right begin r
      · have : r < finish - begin := by
          simpa [w, TerminalVisitSpliceInvariance.stoppedWordOfList,
            incrementSlice_length] using hr
        omega
  · have htransport :=
      trajectoryFrom_extendStoppedWord_incrementSlice_from
        a omega hbegin (show finish - begin ≤ finish - begin from le_rfl)
    rw [hwlen]
    simpa only [Nat.add_sub_of_le hbegin] using htransport

/-- The finite word cut from each erased return interval is a canonical
inner-to-middle first-boundary word with both endpoints retained. -/
def extractedReturnBoundaryExitWordCode
    {omega : StepPath} {start : Point} {middle inner : Set Point}
    {horizon q : ℕ}
    (hcomplete : ∀ j : Fin q,
      excursionStart (PlanarPotential.trajectoryFrom start omega)
        middle inner horizon (j + 1) ≤ horizon)
    (j : Fin q) :
    MarkedBridgeFactorization.BoundaryExitWordCode middle
      (returnEntrancePoint omega start middle inner horizon j)
      (returnExitPoint omega start middle inner horizon j) := by
  let s := PlanarPotential.trajectoryFrom start omega
  let a := excursionFinish s middle inner horizon (j : ℕ)
  let b := excursionStart s middle inner horizon ((j : ℕ) + 1)
  have hab : a ≤ b := excursionFinish_le_next_start s middle inner horizon j
  have hb : b ≤ horizon := hcomplete j
  have hbfirst : b = firstHitThrough s middle a horizon := by
    exact excursionStart_succ_eq_firstHitThrough_finish
      s middle inner horizon j
  have hspec := firstHitThrough_spec_of_le s middle a horizon
    (hbfirst ▸ hb)
  have hbmem : s b ∈ middle := by
    rw [hbfirst]
    exact hspec.2.1
  apply incrementSliceBoundaryExitWordCode start omega middle hab hbmem
  intro r har hrb
  apply hspec.2.2 r
  · rw [← hbfirst]
    exact hrb
  · exact har

/-- The source return-code tuple, used as the reference of the compatible
subtype at the split level. -/
def extractedReturnCodes
    {omega : StepPath} {start : Point} {middle inner : Set Point}
    {horizon q : ℕ}
    (hcomplete : ∀ j : Fin q,
      excursionStart (PlanarPotential.trajectoryFrom start omega)
        middle inner horizon (j + 1) ≤ horizon) :
    (j : Fin q) → MarkedBridgeFactorization.BoundaryExitWordCode middle
      (returnEntrancePoint omega start middle inner horizon j)
      (returnExitPoint omega start middle inner horizon j) :=
  extractedReturnBoundaryExitWordCode hcomplete

/-- At the split level, the actual extracted return tuple is automatically
scanner-compatible with itself. -/
def extractedCompatibleReturnCodes
    {omega : StepPath} {start : Point} {middle inner : Set Point}
    {horizon q : ℕ}
    (scanOuter scanInner : Fin q → Set Point)
    (state : Fin q → BoundaryScanState)
    (hcomplete : ∀ j : Fin q,
      excursionStart (PlanarPotential.trajectoryFrom start omega)
        middle inner horizon (j + 1) ≤ horizon) :
    (j : Fin q) → CompatibleReturnWordCode
      (scanOuter j) (scanInner j) middle
      (returnEntrancePoint omega start middle inner horizon j)
      (returnExitPoint omega start middle inner horizon j) (state j)
      (extractedReturnCodes hcomplete j) :=
  fun j ↦ ⟨extractedReturnCodes hcomplete j, rfl⟩

/-- Erasing the proof fields of the extracted source return code gives
exactly the interval word stored by the timed skeleton. -/
def extractedReturnWords
    {omega : StepPath} {start : Point} {middle inner : Set Point}
    {horizon q : ℕ}
    (hcomplete : ∀ j : Fin q,
      excursionStart (PlanarPotential.trajectoryFrom start omega)
        middle inner horizon (j + 1) ≤ horizon) : TerminalSegmentWords q :=
  fun j ↦ List.ofFn (extractedReturnCodes hcomplete j).1.2

theorem extractedReturnCodes_toList
    {omega : StepPath} {start : Point} {middle inner : Set Point}
    {horizon q : ℕ}
    (hcomplete : ∀ j : Fin q,
      excursionStart (PlanarPotential.trajectoryFrom start omega)
        middle inner horizon (j + 1) ≤ horizon)
    (j : Fin q) :
    extractedReturnWords hcomplete j =
      intervalWords omega
        (extractTimedReturnSkeleton omega start middle inner horizon q).entrance
        (extractTimedReturnSkeleton omega start middle inner horizon q).exit j := by
  simp [extractedReturnWords, extractedReturnCodes,
    extractedReturnBoundaryExitWordCode,
    incrementSliceBoundaryExitWordCode, extractTimedReturnSkeleton,
    TerminalVisitSpliceInvariance.stoppedWordOfList,
    intervalWords]

end

end Erdos1165.AsymmetricSplitLevelSplice
