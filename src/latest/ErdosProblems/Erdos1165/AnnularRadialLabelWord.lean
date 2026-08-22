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

import ErdosProblems.Erdos1165.TerminalProfileBoundarySeparation
import ErdosProblems.Erdos1165.TerminalBoundaryScan
import ErdosProblems.Erdos1165.MarkedBoundaryVisitKernel
import ErdosProblems.Erdos1165.MarkedBridgeFactorization
import ErdosProblems.Erdos1165.AnnularOffspringRenewal

/-!
# Chronological radial-label words

This file gives the literal linear radial word used in HLOZ Appendix A.
Starting on profile level `1`, inspect all profile boundaries at every walk
time, erase unlabeled times and consecutive repetitions, and stop at the
first hit of level `0`.  A word of transition length `L` therefore stores
`L + 1` labels.  It begins at `1`, has nearest-neighbor successive labels,
contains no earlier `0`, and ends with the first transition `1 -> 0`.

The direction-word code is separate from the radial word: an arbitrary
number of lattice steps may occur between two successive radial labels.
The final level-zero first-hit certificate makes the direction codes
prefix-free.  Thus every physical time interval is represented exactly
once, unlike a recursively multiplied whole-gap kernel.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace Erdos1165.AnnularRadialLabelWord

open ThickPoint TerminalProfileBoundarySeparation
open TerminalSpliceProfileGeometry
open MarkedBoundaryVisitKernel MarkedBridgeFactorization
open PlanarPotential TerminalExcursionBridge TerminalSequentialVisitLaw
open TerminalBoundaryScan
open AnnularOffspringRenewal RealDiscFinite

noncomputable section

/-! ## Literal radial boundaries and observed labels -/

/-- The literal HLOZ boundary carrying radial label `k`. -/
def radialBoundary (n : ℕ) (center : Point) (k : Fin (n + 2)) : Set Point :=
  discBoundary center (scaleRadius n k)

/-- All radial labels carried by a lattice point.  The list is in the
canonical `Fin` order.  At separated HLOZ radii it has at most one entry;
keeping the definition as a finite filter avoids making arbitrary choices. -/
noncomputable def radialLabelsAt
    (n : ℕ) (center z : Point) : List (Fin (n + 2)) := by
  classical
  exact ((Finset.univ : Finset (Fin (n + 2))).filter
    (fun k ↦ z ∈ radialBoundary n center k)).toList

@[simp] theorem mem_radialLabelsAt
    {n : ℕ} {center z : Point} {k : Fin (n + 2)} :
    k ∈ radialLabelsAt n center z ↔ z ∈ radialBoundary n center k := by
  classical
  simp [radialLabelsAt]

/-- Distinct literal profile labels are carried by disjoint boundaries.
This is the all-level version of adjacent profile-boundary separation. -/
theorem radialBoundaries_disjoint_of_ne
    {n : ℕ} (hn : 2 ≤ n) (center : Point)
    {left right : Fin (n + 2)} (hne : left ≠ right) :
    Disjoint (radialBoundary n center left) (radialBoundary n center right) := by
  have separated_of_lt : ∀ {i j : Fin (n + 2)}, (i : ℕ) < (j : ℕ) →
      scaleRadius n j + 1 ≤ scaleRadius n i := by
    intro i j hij
    have hjpos : 0 < (j : ℕ) := by omega
    have hjbound : (j : ℕ) ≤ n + 1 := by omega
    have hadj := scaleRadius_add_one_le_previous hn hjpos hjbound
    have hmono : scaleRadius n ((j : ℕ) - 1) ≤ scaleRadius n i := by
      apply scaleRadius_antitone_of_le
      · omega
      · omega
    exact hadj.trans hmono
  rcases lt_or_gt_of_ne (fun h ↦ hne (Fin.ext h)) with hlt | hgt
  · exact (discBoundaries_disjoint_of_separated center
      (separated_of_lt hlt)).symm
  · exact discBoundaries_disjoint_of_separated center
      (separated_of_lt hgt)

/-- A point on a literal radial boundary has exactly that one label. -/
theorem radialLabelsAt_eq_singleton_of_mem
    {n : ℕ} (hn : 2 ≤ n) (center z : Point) (label : Fin (n + 2))
    (hz : z ∈ radialBoundary n center label) :
    radialLabelsAt n center z = [label] := by
  classical
  have hfilter : (Finset.univ : Finset (Fin (n + 2))).filter
      (fun k ↦ z ∈ radialBoundary n center k) = {label} := by
    ext other
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton]
    constructor
    · intro hother
      by_contra hne
      exact Set.disjoint_left.mp
        (radialBoundaries_disjoint_of_ne hn center hne) hother hz
    · rintro rfl
      exact hz
  change ((Finset.univ : Finset (Fin (n + 2))).filter
    (fun k ↦ z ∈ radialBoundary n center k)).toList = [label]
  rw [hfilter]
  simp

/-- Remove consecutive repetitions, remembering the previously emitted
label.  This is the deterministic compression in the definition of the
successive-different-boundary clock. -/
def compressLabelsFrom {Label : Type*} [DecidableEq Label] :
    Option Label → List Label → List Label
  | _, [] => []
  | previous, label :: tail =>
      if previous = some label then
        compressLabelsFrom previous tail
      else
        label :: compressLabelsFrom (some label) tail

/-- Remove consecutive repetitions from a finite label list. -/
def compressLabels {Label : Type*} [DecidableEq Label]
    (labels : List Label) : List Label :=
  compressLabelsFrom none labels

/-- Boundary labels observed through a finite inclusive path prefix, before
consecutive repetitions are erased. -/
noncomputable def observedRadialLabels
    (n : ℕ) (center : Point) (s : WalkPath) (horizon : ℕ) :
    List (Fin (n + 2)) :=
  (List.range (horizon + 1)).flatMap
    (fun t ↦ radialLabelsAt n center (s t))

/-- The chronological successive-different-boundary label scan. -/
noncomputable def chronologicalRadialLabels
    (n : ℕ) (center : Point) (s : WalkPath) (horizon : ℕ) :
    List (Fin (n + 2)) :=
  compressLabels (observedRadialLabels n center s horizon)

theorem chronologicalRadialLabels_congr
    {n horizon : ℕ} {center : Point} {s t : WalkPath}
    (hpath : ∀ q, q ≤ horizon → s q = t q) :
    chronologicalRadialLabels n center s horizon =
      chronologicalRadialLabels n center t horizon := by
  unfold chronologicalRadialLabels observedRadialLabels
  congr 1
  apply List.flatMap_congr
  intro q hq
  congr 1
  apply hpath q
  simp only [List.mem_range] at hq
  omega

private theorem trajectoryFrom_shiftSteps_eq_absolute
    (start : Point) (omega : StepPath) (t q : ℕ) :
    trajectoryFrom (trajectoryFrom start omega t) (shiftSteps t omega) q =
      trajectoryFrom start omega (t + q) := by
  unfold trajectoryFrom
  rw [← trajectory_add_sub_trajectory omega t q]
  abel

private theorem range_add_succ_eq_append_shift
    (t q : ℕ) :
    List.range (t + q + 1) =
      List.range t ++ List.map (fun r ↦ t + r) (List.range (q + 1)) := by
  have h := (List.range'_append
    (s := 0) (m := t) (n := q + 1) (step := 1)).symm
  simpa [List.range'_eq_map_range, Nat.add_assoc] using h

private theorem compressLabels_append_eq_cons_cons
    {Label : Type*} [DecidableEq Label]
    {source target : Label} {initial suffix : List Label}
    (hne : source ≠ target) (hnil : initial ≠ [])
    (hall : ∀ label ∈ initial, label = source) :
    compressLabels (initial ++ target :: suffix) =
      source :: target :: compressLabelsFrom (some target) suffix := by
  unfold compressLabels
  obtain ⟨head, tail, rfl⟩ := List.exists_cons_of_ne_nil hnil
  have hhead := hall head (by simp)
  subst head
  simp only [List.cons_append, compressLabelsFrom, reduceCtorEq, if_false]
  have htail : ∀ label ∈ tail, label = source := by
    intro label hlabel
    exact hall label (by simp [hlabel])
  induction tail with
  | nil => simp [compressLabelsFrom, hne]
  | cons label rest ih =>
      have hlabel := htail label (by simp)
      subst label
      change source ::
        (if some source = some source then
          compressLabelsFrom (some source) (rest ++ target :: suffix)
        else source :: compressLabelsFrom (some source)
          (rest ++ target :: suffix)) = _
      rw [if_pos rfl]
      apply ih (by simp)
      · intro other hother
        exact htail other (by simp [hother])
      · intro other hother
        exact htail other (by simp [hother])

private theorem mem_of_mem_compressLabelsFrom
    {Label : Type*} [DecidableEq Label] (previous : Option Label) :
    ∀ {labels : List Label} {label : Label},
      label ∈ compressLabelsFrom previous labels → label ∈ labels := by
  intro labels
  induction labels generalizing previous with
  | nil => simp [compressLabelsFrom]
  | cons head tail ih =>
      intro label hlabel
      rw [compressLabelsFrom] at hlabel
      split at hlabel
      · exact List.mem_cons_of_mem head (ih _ hlabel)
      · rcases List.mem_cons.mp hlabel with rfl | htail
        · simp
        · exact List.mem_cons_of_mem head (ih _ htail)

private theorem mem_of_mem_compressLabels
    {Label : Type*} [DecidableEq Label] {labels : List Label} {label : Label}
    (hlabel : label ∈ compressLabels labels) : label ∈ labels := by
  exact mem_of_mem_compressLabelsFrom none hlabel

/-! ## The radial-label excursion scan -/

/-- Process one radial label for the excursion from level `k-1` to level
`k`.  Level zero is deliberately excluded from the count theorems below. -/
def radialLabelVisit {n : ℕ} (k : ℕ) (state : BoundaryScanState)
    (label : Fin (n + 2)) : BoundaryScanState :=
  if state.seekingOuter then
    if (label : ℕ) = k - 1 then ⟨false, state.completed⟩ else state
  else if (label : ℕ) = k then
    ⟨true, state.completed + 1⟩ else state

/-- Fold the alternating excursion automaton through a finite radial-label
list. -/
def scanRadialLabels {n : ℕ} (k : ℕ)
    (labels : List (Fin (n + 2))) (state : BoundaryScanState := initialState) :
    BoundaryScanState :=
  labels.foldl (radialLabelVisit k) state

private lemma foldl_radialLabelVisit_seekingOuter_of_avoidsOuter
    {n k completed : ℕ} {labels : List (Fin (n + 2))}
    (havoid : ∀ label ∈ labels, (label : ℕ) ≠ k - 1) :
    labels.foldl (radialLabelVisit k) ⟨true, completed⟩ =
      ⟨true, completed⟩ := by
  induction labels generalizing completed with
  | nil => rfl
  | cons label tail ih =>
      rw [List.foldl_cons]
      simp only [radialLabelVisit, Bool.true_eq, if_true,
        if_neg (havoid label (by simp))]
      exact ih (fun x hx ↦ havoid x (by simp [hx]))

private lemma foldl_radialLabelVisit_seekingInner_of_avoidsInner
    {n k completed : ℕ} {labels : List (Fin (n + 2))}
    (havoid : ∀ label ∈ labels, (label : ℕ) ≠ k) :
    labels.foldl (radialLabelVisit k) ⟨false, completed⟩ =
      ⟨false, completed⟩ := by
  induction labels generalizing completed with
  | nil => rfl
  | cons label tail ih =>
      rw [List.foldl_cons]
      simp only [radialLabelVisit, Bool.false_eq_true, if_false,
        if_neg (havoid label (by simp))]
      exact ih (fun x hx ↦ havoid x (by simp [hx]))

private lemma foldl_radialLabelVisit_seekingOuter_of_hitsOuter_avoidsInner
    {n k completed : ℕ} {labels : List (Fin (n + 2))}
    (hhit : ∃ label ∈ labels, (label : ℕ) = k - 1)
    (havoid : ∀ label ∈ labels, (label : ℕ) ≠ k) :
    labels.foldl (radialLabelVisit k) ⟨true, completed⟩ =
      ⟨false, completed⟩ := by
  induction labels generalizing completed with
  | nil => simp at hhit
  | cons label tail ih =>
      rw [List.foldl_cons]
      by_cases hlabel : (label : ℕ) = k - 1
      · simp only [radialLabelVisit, Bool.true_eq, if_true, hlabel]
        apply foldl_radialLabelVisit_seekingInner_of_avoidsInner
        exact fun x hx ↦ havoid x (by simp [hx])
      · simp only [radialLabelVisit, Bool.true_eq, if_true,
          if_neg hlabel]
        apply ih
        · rcases hhit with ⟨x, hx, heq⟩
          have hxTail : x ∈ tail := by
            simp only [List.mem_cons] at hx
            rcases hx with hxl | hx
            · subst x
              exact (hlabel heq).elim
            · exact hx
          exact ⟨x, hxTail, heq⟩
        · exact fun x hx ↦ havoid x (by simp [hx])

private lemma foldl_radialLabelVisit_seekingInner_of_hitsInner_avoidsOuter
    {n k completed : ℕ} {labels : List (Fin (n + 2))}
    (hhit : ∃ label ∈ labels, (label : ℕ) = k)
    (havoid : ∀ label ∈ labels, (label : ℕ) ≠ k - 1) :
    labels.foldl (radialLabelVisit k) ⟨false, completed⟩ =
      ⟨true, completed + 1⟩ := by
  induction labels generalizing completed with
  | nil => simp at hhit
  | cons label tail ih =>
      rw [List.foldl_cons]
      by_cases hlabel : (label : ℕ) = k
      · simp only [radialLabelVisit, Bool.false_eq_true, if_false, hlabel,
          if_true]
        apply foldl_radialLabelVisit_seekingOuter_of_avoidsOuter
        exact fun x hx ↦ havoid x (by simp [hx])
      · simp only [radialLabelVisit, Bool.false_eq_true, if_false,
          if_neg hlabel]
        apply ih
        · rcases hhit with ⟨x, hx, heq⟩
          have hxTail : x ∈ tail := by
            simp only [List.mem_cons] at hx
            rcases hx with hxl | hx
            · subst x
              exact (hlabel heq).elim
            · exact hx
          exact ⟨x, hxTail, heq⟩
        · exact fun x hx ↦ havoid x (by simp [hx])

/-- The canonical point visit at adjacent profile boundaries. -/
noncomputable def radialPointVisit
    (n : ℕ) (center : Point) (k : ℕ)
    (state : BoundaryScanState) (z : Point) : BoundaryScanState := by
  classical
  exact visit (discBoundary center (scaleRadius n (k - 1)))
    (discBoundary center (scaleRadius n k)) state z

/-- Processing all labels carried by one lattice point is exactly the
two-boundary point visit. -/
theorem foldl_radialLabelsAt_eq_visit
    {n k : ℕ} (hn : 2 ≤ n) (hkpos : 0 < k) (hk : k < n + 2)
    (center z : Point) (state : BoundaryScanState) :
    (radialLabelsAt n center z).foldl (radialLabelVisit k) state =
      radialPointVisit n center k state z := by
  classical
  obtain ⟨seekingOuter, completed⟩ := state
  cases seekingOuter with
  | false =>
      by_cases hzInner : z ∈ discBoundary center (scaleRadius n k)
      · have hzOuter : z ∉ discBoundary center (scaleRadius n (k - 1)) := by
          intro hz
          exact Set.disjoint_left.1
            (profileBoundaries_disjoint_fin hn center ⟨k, hk⟩ hkpos.ne')
            hz hzInner
        rw [foldl_radialLabelVisit_seekingInner_of_hitsInner_avoidsOuter]
        · simp [radialPointVisit, visit, hzInner]
        · exact ⟨⟨k, hk⟩, mem_radialLabelsAt.mpr hzInner, rfl⟩
        · intro label hlabel heq
          have hmem := mem_radialLabelsAt.mp hlabel
          apply hzOuter
          have hlabelEq : label = ⟨k - 1, by omega⟩ := Fin.ext heq
          rw [hlabelEq] at hmem
          exact hmem
      · rw [foldl_radialLabelVisit_seekingInner_of_avoidsInner]
        · simp [radialPointVisit, visit, hzInner]
        · intro label hlabel heq
          apply hzInner
          have hmem := mem_radialLabelsAt.mp hlabel
          have hlabelEq : label = ⟨k, hk⟩ := Fin.ext heq
          rw [hlabelEq] at hmem
          exact hmem

  | true =>
      by_cases hzOuter : z ∈ discBoundary center (scaleRadius n (k - 1))
      · have hzInner : z ∉ discBoundary center (scaleRadius n k) := by
          intro hz
          exact Set.disjoint_left.1
            (profileBoundaries_disjoint_fin hn center ⟨k, hk⟩ hkpos.ne')
            hzOuter hz
        rw [foldl_radialLabelVisit_seekingOuter_of_hitsOuter_avoidsInner]
        · simp [radialPointVisit, visit, hzOuter]
        · exact ⟨⟨k - 1, by omega⟩, mem_radialLabelsAt.mpr hzOuter, by simp⟩
        · intro label hlabel heq
          apply hzInner
          have hmem := mem_radialLabelsAt.mp hlabel
          have hlabelEq : label = ⟨k, hk⟩ := Fin.ext heq
          rw [hlabelEq] at hmem
          exact hmem
      · rw [foldl_radialLabelVisit_seekingOuter_of_avoidsOuter]
        · simp [radialPointVisit, visit, hzOuter]
        · intro label hlabel heq
          apply hzOuter
          have hmem := mem_radialLabelsAt.mp hlabel
          have hlabelEq : label = ⟨k - 1, by omega⟩ := Fin.ext heq
          rw [hlabelEq] at hmem
          exact hmem

/-- The canonical inclusive path-prefix scan at adjacent profile
boundaries. -/
noncomputable def radialPointScanThrough
    (n : ℕ) (center : Point) (k : ℕ)
    (s : WalkPath) (horizon : ℕ) : BoundaryScanState := by
  classical
  exact scanThrough s
    (discBoundary center (scaleRadius n (k - 1)))
    (discBoundary center (scaleRadius n k)) horizon

/-- Folding the observed radial labels is exactly the pointwise path scan. -/
theorem scanRadialLabels_observed_eq_scanThrough
    {n k : ℕ} (hn : 2 ≤ n) (hkpos : 0 < k) (hk : k < n + 2)
    (center : Point) (s : WalkPath) (horizon : ℕ) :
    scanRadialLabels k (observedRadialLabels n center s horizon) =
      radialPointScanThrough n center k s horizon := by
  classical
  unfold scanRadialLabels observedRadialLabels radialPointScanThrough scanThrough
  have hgeneral : ∀ (length : ℕ) (state : BoundaryScanState),
      ((List.range length).flatMap
        (fun t ↦ radialLabelsAt n center (s t))).foldl
          (radialLabelVisit k) state =
        scanSegment s
          (discBoundary center (scaleRadius n (k - 1)))
          (discBoundary center (scaleRadius n k)) 0 length state := by
    intro length
    induction length with
    | zero => intro state; rfl
    | succ length ih =>
        intro state
        simp only [List.range_succ, List.flatMap_append,
          List.flatMap_singleton, List.foldl_append]
        rw [ih, foldl_radialLabelsAt_eq_visit hn hkpos hk]
        rw [scanSegment_succ]
        unfold radialPointVisit
        simp only [Nat.zero_add]
  exact hgeneral (horizon + 1) initialState

private theorem radialLabelVisit_idempotent
    {n k : ℕ} (hkpos : 0 < k)
    (state : BoundaryScanState) (label : Fin (n + 2)) :
    radialLabelVisit k (radialLabelVisit k state label) label =
      radialLabelVisit k state label := by
  have hne : k - 1 ≠ k := by omega
  obtain ⟨seekingOuter, completed⟩ := state
  cases seekingOuter <;>
    by_cases houter : (label : ℕ) = k - 1 <;>
    by_cases hinner : (label : ℕ) = k <;>
    simp [radialLabelVisit, houter, hinner, hne, Ne.symm hne]

private theorem foldl_compressLabelsFrom_eq
    {Label State : Type*} [DecidableEq Label]
    (step : State → Label → State)
    (hidempotent : ∀ state label,
      step (step state label) label = step state label)
    (previous : Option Label) (labels : List Label) (state : State)
    (hprevious : ∀ label, previous = some label →
      step state label = state) :
    (compressLabelsFrom previous labels).foldl step state =
      labels.foldl step state := by
  induction labels generalizing previous state with
  | nil => rfl
  | cons label tail ih =>
      rw [compressLabelsFrom]
      by_cases heq : previous = some label
      · rw [if_pos heq, List.foldl_cons, hprevious label heq]
        exact ih previous state hprevious
      · rw [if_neg heq, List.foldl_cons, List.foldl_cons]
        apply ih (some label) (step state label)
        intro next hnext
        have hlabel : next = label := by
          exact (Option.some.inj hnext).symm
        subst next
        exact hidempotent state label

/-- Consecutive-repeat compression preserves the radial excursion scan. -/
theorem scanRadialLabels_compressLabels
    {n k : ℕ} (hkpos : 0 < k)
    (labels : List (Fin (n + 2))) (state : BoundaryScanState) :
    scanRadialLabels k (compressLabels labels) state =
      scanRadialLabels k labels state := by
  unfold scanRadialLabels compressLabels
  apply foldl_compressLabelsFrom_eq
  · exact radialLabelVisit_idempotent hkpos
  · intro label hfalse
    simp at hfalse

/-- Canonical literal completed count at adjacent profile boundaries. -/
noncomputable def radialCompletedExcursionCount
    (n : ℕ) (center : Point) (k : ℕ)
    (s : WalkPath) (horizon : ℕ) : ℕ := by
  classical
  exact completedExcursionCount s
    (discBoundary center (scaleRadius n (k - 1)))
    (discBoundary center (scaleRadius n k)) horizon

/-- The chronological label scan computes the literal completed excursion
count at every positive profile level. -/
theorem chronologicalRadialLabels_completed_eq_completedExcursionCount
    {n k : ℕ} (hn : 2 ≤ n) (hkpos : 0 < k) (hk : k < n + 2)
    (center : Point) (s : WalkPath) (horizon : ℕ) :
    (scanRadialLabels k
      (chronologicalRadialLabels n center s horizon)).completed =
      radialCompletedExcursionCount n center k s horizon := by
  classical
  rw [chronologicalRadialLabels, scanRadialLabels_compressLabels hkpos,
    scanRadialLabels_observed_eq_scanThrough hn hkpos hk]
  unfold radialPointScanThrough radialCompletedExcursionCount
  exact scanThrough_completed_eq_completedExcursionCount _ _ _
    (profileBoundaries_disjoint_fin hn center ⟨k, hk⟩ hkpos.ne') horizon

/-! ## Finite admissible label words -/

/-- A source-exact stopped radial word with `L` adjacent-level transitions.
The stored vector includes both the initial level `1` and final level `0`. -/
structure RadialLabelWord (n L : ℕ) where
  level : Fin (L + 1) → Fin (n + 2)
  startsAtOne : level ⟨0, by omega⟩ = ⟨1, by omega⟩
  adjacent : ∀ j : Fin L,
    Nat.dist (level j.castSucc) (level j.succ) = 1
  beforeFinal_ne_zero : ∀ j : Fin L, (level j.castSucc : ℕ) ≠ 0
  endsAtZero : level (Fin.last L) = ⟨0, by omega⟩

@[ext] theorem RadialLabelWord.ext {n L : ℕ}
    {left right : RadialLabelWord n L}
    (hlevel : left.level = right.level) : left = right := by
  cases left
  cases right
  cases hlevel
  rfl

instance (n L : ℕ) : Finite (RadialLabelWord n L) :=
  Finite.of_injective (fun word : RadialLabelWord n L ↦ word.level)
    (fun _ _ ↦ RadialLabelWord.ext)

noncomputable instance (n L : ℕ) : Fintype (RadialLabelWord n L) :=
  Fintype.ofFinite _

/-- The list presentation used by the literal chronological scan. -/
def RadialLabelWord.toList {n L : ℕ}
    (word : RadialLabelWord n L) : List (Fin (n + 2)) :=
  List.ofFn word.level

@[simp] theorem RadialLabelWord.length_toList {n L : ℕ}
    (word : RadialLabelWord n L) : word.toList.length = L + 1 := by
  simp [RadialLabelWord.toList]

/-- Number of literal adjacent transitions `(k-1) -> k` in a label list. -/
def radialListUpcrossingCount {n : ℕ} (k : ℕ) :
    List (Fin (n + 2)) → ℕ
  | source :: target :: tail =>
      (if (source : ℕ) = k - 1 ∧ (target : ℕ) = k then 1 else 0) +
        radialListUpcrossingCount k (target :: tail)
  | _ => 0

/-- The number of inward crossings `(k-1) -> k` in a radial word. -/
def radialUpcrossingCount {n L : ℕ}
    (word : RadialLabelWord n L) (k : Fin (n + 2)) : ℕ :=
  if hk : (k : ℕ) = 0 then 0 else
    radialListUpcrossingCount (k : ℕ) word.toList

@[simp] theorem radialUpcrossingCount_zero {n L : ℕ}
    (word : RadialLabelWord n L) :
    radialUpcrossingCount word ⟨0, by omega⟩ = 0 := by
  simp [radialUpcrossingCount]

/-- The exact alternating-clock count carried by a finite radial word. -/
def radialWordCompletedCount {n L : ℕ}
    (word : RadialLabelWord n L) (k : ℕ) : ℕ :=
  (scanRadialLabels k word.toList).completed

private theorem radialLabelVisit_adjacent_step
    {n k : ℕ} (hk : 2 ≤ k)
    (current target : Fin (n + 2)) (state : BoundaryScanState)
    (hadjacent : Nat.dist (current : ℕ) (target : ℕ) = 1)
    (hcurrentOuter : (current : ℕ) = k - 1 →
      state.seekingOuter = false)
    (hcurrentInner : k ≤ (current : ℕ) →
      state.seekingOuter = true) :
    let nextState := radialLabelVisit k state target
    nextState.completed = state.completed +
        (if (current : ℕ) = k - 1 ∧ (target : ℕ) = k then 1 else 0) ∧
      ((target : ℕ) = k - 1 → nextState.seekingOuter = false) ∧
      (k ≤ (target : ℕ) → nextState.seekingOuter = true) := by
  unfold Nat.dist at hadjacent
  obtain ⟨seekingOuter, completed⟩ := state
  cases seekingOuter with
  | false =>
      have hcurrent_lt : (current : ℕ) < k := by
        by_contra hnot
        have hbad := hcurrentInner (by omega)
        simp at hbad
      simp only [radialLabelVisit, Bool.false_eq_true, if_false]
      by_cases htarget : (target : ℕ) = k
      · rw [if_pos htarget]
        have hcurrent : (current : ℕ) = k - 1 := by omega
        simp [hcurrent, htarget]
        omega
      · rw [if_neg htarget]
        simp [htarget]
        omega
  | true =>
      have hcurrent : (current : ℕ) ≠ k - 1 := by
        intro heq
        have hbad := hcurrentOuter heq
        simp at hbad
      simp only [radialLabelVisit, Bool.true_eq, if_true]
      by_cases htarget : (target : ℕ) = k - 1
      · rw [if_pos htarget]
        simp [hcurrent, htarget]
        omega
      · rw [if_neg htarget]
        simp [hcurrent, htarget]

private theorem foldl_radialLabelVisit_completed_eq_add_upcrossingCount
    {n k : ℕ} (hk : 2 ≤ k) :
    ∀ (current : Fin (n + 2)) (tail : List (Fin (n + 2)))
      (state : BoundaryScanState),
      List.IsChain
          (fun (left right : Fin (n + 2)) ↦
            Nat.dist left.val right.val = 1) (current :: tail) →
      ((current : ℕ) = k - 1 → state.seekingOuter = false) →
      (k ≤ (current : ℕ) → state.seekingOuter = true) →
      (tail.foldl (radialLabelVisit k) state).completed =
        state.completed + radialListUpcrossingCount k (current :: tail) := by
  intro current tail
  induction tail generalizing current with
  | nil =>
      intro state _ _ _
      simp [radialListUpcrossingCount]
  | cons target rest ih =>
      intro state hchain houter hinner
      have hchainParts := (List.isChain_cons_cons.mp hchain)
      have hstep := radialLabelVisit_adjacent_step hk current target state
        hchainParts.1 houter hinner
      rw [List.foldl_cons,
        ih target (radialLabelVisit k state target) hchainParts.2
          hstep.2.1 hstep.2.2,
        radialListUpcrossingCount, hstep.1]
      omega

/-- On an admissible nearest-neighbor radial word, the alternating clock
count is exactly the explicit number of `(k-1) -> k` transitions. -/
theorem radialWordCompletedCount_eq_radialUpcrossingCount
    {n L : ℕ} (word : RadialLabelWord n L) (k : Fin (n + 2))
    (hk : 2 ≤ (k : ℕ)) :
    radialWordCompletedCount word k = radialUpcrossingCount word k := by
  have hlist : word.toList =
      word.level ⟨0, by omega⟩ ::
        List.ofFn (fun j : Fin L ↦ word.level j.succ) := by
    simp [RadialLabelWord.toList, List.ofFn_succ]
  have hchain : List.IsChain
      (fun (left right : Fin (n + 2)) ↦ Nat.dist left.val right.val = 1)
      word.toList := by
    rw [RadialLabelWord.toList, List.isChain_ofFn]
    intro i hi
    exact word.adjacent ⟨i, by omega⟩
  let firstState := radialLabelVisit (k : ℕ) initialState
    (word.level ⟨0, by omega⟩)
  have hfirstVal : (word.level ⟨0, by omega⟩ : ℕ) = 1 :=
    congrArg Fin.val word.startsAtOne
  have hfirstOuter : (word.level ⟨0, by omega⟩ : ℕ) = (k : ℕ) - 1 →
      firstState.seekingOuter = false := by
    intro heq
    change (radialLabelVisit (k : ℕ) initialState
      (word.level ⟨0, by omega⟩)).seekingOuter = false
    simp only [radialLabelVisit, initialState, Bool.true_eq, if_true]
    rw [if_pos heq]
  have hfirstInner : (k : ℕ) ≤ (word.level ⟨0, by omega⟩ : ℕ) →
      firstState.seekingOuter = true := by
    intro hfalse
    exfalso
    omega
  have hfold := foldl_radialLabelVisit_completed_eq_add_upcrossingCount
    hk (word.level ⟨0, by omega⟩)
      (List.ofFn (fun j : Fin L ↦ word.level j.succ)) firstState
      (by simpa only [hlist] using hchain) hfirstOuter hfirstInner
  unfold radialWordCompletedCount radialUpcrossingCount scanRadialLabels
  rw [hlist, List.foldl_cons]
  rw [dif_neg (by omega : (k : ℕ) ≠ 0)]
  change _ = radialListUpcrossingCount (k : ℕ)
    (word.level ⟨0, by omega⟩ ::
      List.ofFn (fun j : Fin L ↦ word.level j.succ))
  rw [hfold]
  have hcompleted : firstState.completed = 0 := by
    unfold firstState
    simp only [radialLabelVisit, initialState, Bool.true_eq, if_true]
    split <;> rfl
  rw [hcompleted, Nat.zero_add]

/-- A chronological trace equality extracts the corresponding literal
profile coordinate exactly. -/
theorem radialWordCompletedCount_eq_excursionProfile_of_trace
    {n L horizon k : ℕ} (hn : 2 ≤ n) (hkpos : 0 < k)
    (hk : k < n + 2) (center : Point) (s : WalkPath)
    (word : RadialLabelWord n L)
    (htrace : chronologicalRadialLabels n center s horizon = word.toList) :
    radialWordCompletedCount word k =
      excursionProfile s n horizon center ⟨k, hk⟩ := by
  classical
  unfold radialWordCompletedCount
  rw [← htrace,
    chronologicalRadialLabels_completed_eq_completedExcursionCount
      hn hkpos hk]
  unfold radialCompletedExcursionCount excursionProfile
  simp only [dif_neg hkpos.ne']

/-! ## Literal stopped direction-word atoms -/

/-- Direction words whose first level-zero hit has precisely the prescribed
chronological radial label word. -/
abbrev RadialLabelStoppedWordCode
    (n L : ℕ) (center start : Point) (word : RadialLabelWord n L) :=
  {w : StoppedWord //
    AbsoluteBoundaryFirstAt (radialBoundary n center ⟨0, by omega⟩)
      start (extendStoppedWord w) w.1 ∧
    chronologicalRadialLabels n center
      (fun q ↦ trajectoryFrom start (extendStoppedWord w) q) w.1 = word.toList}

private theorem prefixFree_of_finalBoundaryFirstAt
    {Code : Type*} (codeWord : Code → StoppedWord)
    (hinjective : Function.Injective codeWord)
    (boundary : Set Point) (start : Point)
    (hfirst : ∀ c, AbsoluteBoundaryFirstAt boundary start
      (extendStoppedWord (codeWord c)) (codeWord c).1) :
    PrefixFree codeWord := by
  intro c d hcd
  rw [Set.disjoint_left]
  intro omega hc hd
  have hcfirst := absoluteBoundaryFirstAt_of_mem_stoppedWordCylinder
    hc (hfirst c)
  have hdfirst := absoluteBoundaryFirstAt_of_mem_stoppedWordCylinder
    hd (hfirst d)
  have hlength : (codeWord c).1 = (codeWord d).1 :=
    absoluteBoundaryFirstAt_unique hcfirst hdfirst
  apply hcd
  apply hinjective
  apply Sigma.ext hlength
  apply (Fin.heq_fun_iff hlength).2
  intro i
  change stepPrefix (codeWord c).1 omega = (codeWord c).2 at hc
  change stepPrefix (codeWord d).1 omega = (codeWord d).2 at hd
  have hci := congrFun hc i
  have hdi := congrFun hd ⟨(i : ℕ), hlength ▸ i.2⟩
  simpa only [stepPrefix] using hci.symm.trans hdi

/-- The stopped direction codes of a fixed radial word are prefix-free. -/
theorem prefixFree_radialLabelStoppedWordCode
    (n L : ℕ) (center start : Point) (word : RadialLabelWord n L) :
    PrefixFree (fun c : RadialLabelStoppedWordCode n L center start word ↦ c.1) := by
  apply prefixFree_of_finalBoundaryFirstAt
    (fun c : RadialLabelStoppedWordCode n L center start word ↦ c.1)
    Subtype.val_injective (radialBoundary n center ⟨0, by omega⟩) start
  exact fun c ↦ c.2.1

/-- Literal stopped event of one prescribed radial label word. -/
def radialLabelWordAtom
    (n L : ℕ) (center start : Point) (word : RadialLabelWord n L) :
    Set StepPath :=
  stoppedWordEvent
    (fun c : RadialLabelStoppedWordCode n L center start word ↦ c.1)

/-- Intrinsic path description of a fixed radial-word atom: the horizon is
the first level-zero hit and the chronological scan is the prescribed word. -/
theorem mem_radialLabelWordAtom_iff
    (n L : ℕ) (center start : Point) (word : RadialLabelWord n L)
    (omega : StepPath) :
    omega ∈ radialLabelWordAtom n L center start word ↔
      ∃ horizon : ℕ,
        AbsoluteBoundaryFirstAt (radialBoundary n center ⟨0, by omega⟩)
          start omega horizon ∧
        chronologicalRadialLabels n center
          (fun q ↦ trajectoryFrom start omega q) horizon = word.toList := by
  constructor
  · intro homega
    obtain ⟨code, hcode⟩ := Set.mem_iUnion.mp homega
    refine ⟨code.1.1,
      absoluteBoundaryFirstAt_of_mem_stoppedWordCylinder hcode code.2.1, ?_⟩
    rw [chronologicalRadialLabels_congr (fun q hq ↦
      trajectoryFrom_eq_extendStoppedWord_of_mem hcode start hq)]
    exact code.2.2
  · rintro ⟨horizon, hfirst, htrace⟩
    let stopped : StoppedWord := ⟨horizon, stepPrefix horizon omega⟩
    have hmem : omega ∈ stoppedWordCylinder stopped := by
      change stepPrefix horizon omega = stepPrefix horizon omega
      rfl
    have hfirstStopped : AbsoluteBoundaryFirstAt
        (radialBoundary n center ⟨0, by omega⟩) start
        (extendStoppedWord stopped) horizon := by
      constructor
      · rw [← trajectoryFrom_eq_extendStoppedWord_of_mem
          hmem start le_rfl]
        exact hfirst.1
      · intro q hq
        rw [← trajectoryFrom_eq_extendStoppedWord_of_mem
          hmem start hq.le]
        exact hfirst.2 q hq
    have htraceStopped : chronologicalRadialLabels n center
        (fun q ↦ trajectoryFrom start (extendStoppedWord stopped) q)
          horizon = word.toList := by
      rw [← chronologicalRadialLabels_congr (fun q hq ↦
        trajectoryFrom_eq_extendStoppedWord_of_mem hmem start hq)]
      exact htrace
    let code : RadialLabelStoppedWordCode n L center start word :=
      ⟨stopped, hfirstStopped, htraceStopped⟩
    exact Set.mem_iUnion.mpr ⟨code, hmem⟩

/-- Membership in a literal radial-word atom extracts every positive
`excursionProfile` coordinate from the finite label word. -/
theorem radialWordCompletedCount_eq_excursionProfile_of_mem
    {n L k : ℕ} (hn : 2 ≤ n) (hkpos : 0 < k) (hk : k < n + 2)
    (center start : Point) (word : RadialLabelWord n L) (omega : StepPath)
    (homega : omega ∈ radialLabelWordAtom n L center start word) :
    ∃ horizon : ℕ,
      AbsoluteBoundaryFirstAt (radialBoundary n center ⟨0, by omega⟩)
        start omega horizon ∧
      radialWordCompletedCount word k =
        excursionProfile (fun q ↦ trajectoryFrom start omega q)
          n horizon center ⟨k, hk⟩ := by
  obtain ⟨horizon, hfirst, htrace⟩ :=
    (mem_radialLabelWordAtom_iff n L center start word omega).mp homega
  exact ⟨horizon, hfirst,
    radialWordCompletedCount_eq_excursionProfile_of_trace
      hn hkpos hk center _ word htrace⟩

theorem measurableSet_radialLabelWordAtom
    (n L : ℕ) (center start : Point) (word : RadialLabelWord n L) :
    MeasurableSet (radialLabelWordAtom n L center start word) := by
  exact measurableSet_stoppedWordEvent _

/-- Exact mass of a radial-word atom as the sum of its prefix-free physical
direction cylinders. -/
theorem fairSteps_radialLabelWordAtom
    (n L : ℕ) (center start : Point) (word : RadialLabelWord n L) :
    fairSteps (radialLabelWordAtom n L center start word) =
      ∑' c : RadialLabelStoppedWordCode n L center start word,
        stoppedWordMass c.1 := by
  exact fairSteps_stoppedWordEvent
    (prefixFree_radialLabelStoppedWordCode n L center start word)

/-- Different radial words of the same transition length give disjoint
literal stopped events. -/
theorem pairwise_disjoint_radialLabelWordAtom
    (n L : ℕ) (center start : Point) :
    Pairwise fun left right : RadialLabelWord n L ↦
      Disjoint (radialLabelWordAtom n L center start left)
        (radialLabelWordAtom n L center start right) := by
  intro left right hne
  rw [Set.disjoint_left]
  intro omega hleft hright
  obtain ⟨leftCode, hleftCode⟩ := Set.mem_iUnion.mp hleft
  obtain ⟨rightCode, hrightCode⟩ := Set.mem_iUnion.mp hright
  have hleftFirst := absoluteBoundaryFirstAt_of_mem_stoppedWordCylinder
    hleftCode leftCode.2.1
  have hrightFirst := absoluteBoundaryFirstAt_of_mem_stoppedWordCylinder
    hrightCode rightCode.2.1
  have hlength : leftCode.1.1 = rightCode.1.1 :=
    absoluteBoundaryFirstAt_unique hleftFirst hrightFirst
  have htraceLeft : chronologicalRadialLabels n center
      (fun q ↦ trajectoryFrom start omega q) leftCode.1.1 = left.toList := by
    rw [chronologicalRadialLabels_congr (fun q hq ↦
      trajectoryFrom_eq_extendStoppedWord_of_mem hleftCode start hq)]
    exact leftCode.2.2
  have htraceRight : chronologicalRadialLabels n center
      (fun q ↦ trajectoryFrom start omega q) rightCode.1.1 = right.toList := by
    rw [chronologicalRadialLabels_congr (fun q hq ↦
      trajectoryFrom_eq_extendStoppedWord_of_mem hrightCode start hq)]
    exact rightCode.2.2
  apply hne
  apply RadialLabelWord.ext
  apply List.ofFn_injective
  have hlist : left.toList = right.toList := by
    rw [← htraceLeft, ← htraceRight, hlength]
  exact hlist

/-! ## Finite families of variable-length radial words -/

/-- All admissible radial words with at most `maxTransitions` transitions. -/
abbrev BoundedRadialLabelWord (n maxTransitions : ℕ) :=
  Σ L : Fin (maxTransitions + 1), RadialLabelWord n L

/-- Literal atom attached to a bounded variable-length radial word. -/
def boundedRadialLabelWordAtom
    (n maxTransitions : ℕ) (center start : Point)
    (word : BoundedRadialLabelWord n maxTransitions) : Set StepPath :=
  radialLabelWordAtom n word.1 center start word.2

/-- Bounded radial words of different transition lengths, as well as
different words of the same length, give disjoint literal events. -/
theorem pairwise_disjoint_boundedRadialLabelWordAtom
    (n maxTransitions : ℕ) (center start : Point) :
    Pairwise fun left right : BoundedRadialLabelWord n maxTransitions ↦
      Disjoint (boundedRadialLabelWordAtom n maxTransitions center start left)
        (boundedRadialLabelWordAtom n maxTransitions center start right) := by
  rintro ⟨leftLength, left⟩ ⟨rightLength, right⟩ hne
  rw [Set.disjoint_left]
  intro omega hleft hright
  obtain ⟨leftHorizon, leftFirst, leftTrace⟩ :=
    (mem_radialLabelWordAtom_iff n leftLength center start left omega).mp hleft
  obtain ⟨rightHorizon, rightFirst, rightTrace⟩ :=
    (mem_radialLabelWordAtom_iff n rightLength center start right omega).mp hright
  have hHorizon : leftHorizon = rightHorizon :=
    absoluteBoundaryFirstAt_unique leftFirst rightFirst
  have hlist : left.toList = right.toList := by
    rw [← leftTrace, ← rightTrace, hHorizon]
  have hLengthNat : (leftLength : ℕ) = (rightLength : ℕ) := by
    have h := congrArg List.length hlist
    simp only [RadialLabelWord.length_toList] at h
    omega
  have hLength : leftLength = rightLength := Fin.ext hLengthNat
  subst rightLength
  have hword : left = right := by
    apply RadialLabelWord.ext
    apply List.ofFn_injective
    exact hlist
  subst right
  exact hne rfl

/-- Union of a finite predicate-selected family of bounded radial words.
This is the fixed-profile/terminal-window summation surface. -/
def radialLabelWordFamilyAtom
    (n maxTransitions : ℕ) (center start : Point)
    (P : BoundedRadialLabelWord n maxTransitions → Prop) : Set StepPath :=
  ⋃ word : {word : BoundedRadialLabelWord n maxTransitions // P word},
    boundedRadialLabelWordAtom n maxTransitions center start word.1

noncomputable instance radialLabelWordFamilyFintype
    (n maxTransitions : ℕ)
    (P : BoundedRadialLabelWord n maxTransitions → Prop) :
    Fintype {word : BoundedRadialLabelWord n maxTransitions // P word} :=
  Fintype.ofFinite _

theorem measurableSet_radialLabelWordFamilyAtom
    (n maxTransitions : ℕ) (center start : Point)
    (P : BoundedRadialLabelWord n maxTransitions → Prop) :
    MeasurableSet
      (radialLabelWordFamilyAtom n maxTransitions center start P) := by
  apply MeasurableSet.iUnion
  intro word
  exact measurableSet_radialLabelWordAtom _ _ _ _ _

theorem mem_radialLabelWordFamilyAtom_iff
    (n maxTransitions : ℕ) (center start : Point)
    (P : BoundedRadialLabelWord n maxTransitions → Prop)
    (omega : StepPath) :
    omega ∈ radialLabelWordFamilyAtom n maxTransitions center start P ↔
      ∃ word : BoundedRadialLabelWord n maxTransitions,
        P word ∧
        omega ∈ boundedRadialLabelWordAtom
          n maxTransitions center start word := by
  simp only [radialLabelWordFamilyAtom, Set.mem_iUnion, Subtype.exists,
    exists_prop]

/-- Exact finite disjoint-union mass identity for any fixed-profile and
terminal-window predicate on bounded radial words. -/
theorem fairSteps_radialLabelWordFamilyAtom
    (n maxTransitions : ℕ) (center start : Point)
    (P : BoundedRadialLabelWord n maxTransitions → Prop) :
    fairSteps (radialLabelWordFamilyAtom n maxTransitions center start P) =
      ∑ word : {word : BoundedRadialLabelWord n maxTransitions // P word},
        fairSteps (boundedRadialLabelWordAtom
          n maxTransitions center start word.1) := by
  have hpair : Pairwise fun
      left right : {word : BoundedRadialLabelWord n maxTransitions // P word} ↦
      Disjoint
        (boundedRadialLabelWordAtom n maxTransitions center start left.1)
        (boundedRadialLabelWordAtom n maxTransitions center start right.1) := by
    intro left right hne
    exact pairwise_disjoint_boundedRadialLabelWordAtom
      n maxTransitions center start
      (fun heq ↦ hne (Subtype.ext heq))
  rw [radialLabelWordFamilyAtom, measure_iUnion hpair]
  · exact tsum_fintype _
  · intro word
    exact measurableSet_radialLabelWordAtom _ _ _ _ _

/-! ## Exact one-step transition atoms -/

/-- Union of all literal radial boundaries except the current label. -/
def otherRadialBoundaries
    (n : ℕ) (center : Point) (source : Fin (n + 2)) : Set Point :=
  ⋃ k : Fin (n + 2), if k = source then ∅ else radialBoundary n center k

/-- The next different radial-boundary hit has prescribed label `to`.
All spatial endpoints on that boundary are integrated. -/
def radialOneStepAtom
    (n : ℕ) (center : Point) (source target : Fin (n + 2))
    (start : Point) : Set StepPath :=
  boundaryExitMarkedSteps (otherRadialBoundaries n center source)
    (radialBoundary n center target) start

theorem measurableSet_radialOneStepAtom
    (n : ℕ) (center : Point) (source target : Fin (n + 2))
    (start : Point) :
    MeasurableSet (radialOneStepAtom n center source target start) := by
  exact measurableSet_boundaryExitMarkedSteps _ _ _

theorem mem_radialOneStepAtom_iff_exists_first
    (n : ℕ) (center : Point) (source target : Fin (n + 2))
    (start : Point) (omega : StepPath) :
    omega ∈ radialOneStepAtom n center source target start ↔
      ∃ horizon : ℕ,
        AbsoluteBoundaryFirstAt (otherRadialBoundaries n center source)
          start omega horizon ∧
        trajectoryFrom start omega horizon ∈ radialBoundary n center target := by
  exact mem_boundaryExitMarkedSteps_iff_exists_first _ _ _ _

private theorem chronologicalRadialLabels_splice_firstDifferent
    {n t q : ℕ} (hn : 2 ≤ n) (center start : Point)
    (source target : Fin (n + 2)) (omega : StepPath)
    (tail : List (Fin (n + 2)))
    (hne : source ≠ target)
    (hstart : start ∈ radialBoundary n center source)
    (hfirst : AbsoluteBoundaryFirstAt
      (otherRadialBoundaries n center source) start omega t)
    (htarget : trajectoryFrom start omega t ∈
      radialBoundary n center target)
    (htail : chronologicalRadialLabels n center
      (fun r ↦ trajectoryFrom (trajectoryFrom start omega t)
        (shiftSteps t omega) r) q = target :: tail) :
    chronologicalRadialLabels n center
      (fun r ↦ trajectoryFrom start omega r) (t + q) =
        source :: target :: tail := by
  classical
  have htpos : 0 < t := by
    by_contra hnot
    have htzero : t = 0 := by omega
    subst t
    have htarget0 : start ∈ radialBoundary n center target := by
      simpa using htarget
    exact Set.disjoint_left.mp
      (radialBoundaries_disjoint_of_ne hn center hne) hstart htarget0
  let rawPrefix : List (Fin (n + 2)) :=
    (List.range t).flatMap (fun r ↦
      radialLabelsAt n center (trajectoryFrom start omega r))
  have hprefixNonempty : rawPrefix ≠ [] := by
    apply List.ne_nil_of_mem (a := source)
    change source ∈ (List.range t).flatMap (fun r ↦
      radialLabelsAt n center (trajectoryFrom start omega r))
    rw [List.mem_flatMap]
    refine ⟨0, by simp [htpos], ?_⟩
    apply (mem_radialLabelsAt).2
    simpa using hstart
  have hprefixOnly : ∀ label ∈ rawPrefix, label = source := by
    intro label hlabel
    change label ∈ (List.range t).flatMap (fun r ↦
      radialLabelsAt n center (trajectoryFrom start omega r)) at hlabel
    rw [List.mem_flatMap] at hlabel
    obtain ⟨r, hr, hrlabel⟩ := hlabel
    have hrlt : r < t := by simpa using hr
    by_contra hlabelNe
    apply hfirst.2 r hrlt
    rw [otherRadialBoundaries]
    refine Set.mem_iUnion.mpr ⟨label, ?_⟩
    rw [if_neg hlabelNe]
    exact (mem_radialLabelsAt).1 hrlabel
  let shifted : WalkPath := fun r ↦
    trajectoryFrom (trajectoryFrom start omega t) (shiftSteps t omega) r
  let suffixRest : List (Fin (n + 2)) :=
    (List.map Nat.succ (List.range q)).flatMap
      (fun r ↦ radialLabelsAt n center (shifted r))
  have hsuffixRaw : observedRadialLabels n center shifted q =
      target :: suffixRest := by
    unfold observedRadialLabels suffixRest
    rw [List.range_succ_eq_map]
    simp only [List.flatMap_cons, List.flatMap_map]
    rw [radialLabelsAt_eq_singleton_of_mem hn center _ target]
    · rfl
    · dsimp [shifted]
      simpa using htarget
  have htailRest : compressLabelsFrom (some target) suffixRest = tail := by
    change compressLabels (observedRadialLabels n center shifted q) =
      target :: tail at htail
    rw [hsuffixRaw] at htail
    unfold compressLabels at htail
    simp only [compressLabelsFrom, reduceCtorEq, if_false] at htail
    exact List.cons.inj htail |>.2
  have hraw : observedRadialLabels n center
      (fun r ↦ trajectoryFrom start omega r) (t + q) =
        rawPrefix ++ target :: suffixRest := by
    unfold observedRadialLabels rawPrefix
    rw [range_add_succ_eq_append_shift, List.flatMap_append,
      List.flatMap_map]
    congr 1
    calc
      List.flatMap
          (fun r ↦ radialLabelsAt n center
            (trajectoryFrom start omega (t + r))) (List.range (q + 1)) =
          List.flatMap
            (fun r ↦ radialLabelsAt n center (shifted r))
              (List.range (q + 1)) := by
            apply List.flatMap_congr
            intro r _
            apply congrArg (radialLabelsAt n center)
            dsimp [shifted]
            exact (trajectoryFrom_shiftSteps_eq_absolute start omega t r).symm
      _ = target :: suffixRest := hsuffixRaw
  unfold chronologicalRadialLabels
  rw [hraw, compressLabels_append_eq_cons_cons hne
    hprefixNonempty hprefixOnly, htailRest]

theorem chronologicalRadialLabels_unsplice_firstDifferent
    {n horizon : ℕ} (hn : 2 ≤ n) (center start : Point)
    (source target : Fin (n + 2)) (omega : StepPath)
    (tail : List (Fin (n + 2)))
    (hne : source ≠ target)
    (hstart : start ∈ radialBoundary n center source)
    (htrace : chronologicalRadialLabels n center
      (fun r ↦ trajectoryFrom start omega r) horizon =
        source :: target :: tail) :
    ∃ t : ℕ,
      t ≤ horizon ∧
      AbsoluteBoundaryFirstAt (otherRadialBoundaries n center source)
        start omega t ∧
      trajectoryFrom start omega t ∈ radialBoundary n center target ∧
      chronologicalRadialLabels n center
        (fun r ↦ trajectoryFrom (trajectoryFrom start omega t)
          (shiftSteps t omega) r) (horizon - t) = target :: tail := by
  classical
  have htargetChronological : target ∈ chronologicalRadialLabels n center
      (fun r ↦ trajectoryFrom start omega r) horizon := by
    rw [htrace]
    simp
  have htargetObserved : target ∈ observedRadialLabels n center
      (fun r ↦ trajectoryFrom start omega r) horizon :=
    mem_of_mem_compressLabels htargetChronological
  rw [observedRadialLabels, List.mem_flatMap] at htargetObserved
  obtain ⟨r, hrRange, hrLabel⟩ := htargetObserved
  have hrle : r ≤ horizon := by
    simp only [List.mem_range] at hrRange
    omega
  have hrOther : trajectoryFrom start omega r ∈
      otherRadialBoundaries n center source := by
    rw [otherRadialBoundaries]
    refine Set.mem_iUnion.mpr ⟨target, ?_⟩
    rw [if_neg hne.symm]
    exact (mem_radialLabelsAt).1 hrLabel
  let candidate : ℕ → Prop := fun q ↦
    q ≤ horizon ∧ trajectoryFrom start omega q ∈
      otherRadialBoundaries n center source
  have hexists : ∃ q, candidate q := ⟨r, hrle, hrOther⟩
  let t : ℕ := Nat.find hexists
  have htspec : candidate t := Nat.find_spec hexists
  have htmin : ∀ q < t,
      trajectoryFrom start omega q ∉ otherRadialBoundaries n center source := by
    intro q hqt hqOther
    have hqle : q ≤ horizon := hqt.le.trans htspec.1
    have := Nat.find_min' hexists (show candidate q from ⟨hqle, hqOther⟩)
    omega
  have hfirst : AbsoluteBoundaryFirstAt
      (otherRadialBoundaries n center source) start omega t :=
    ⟨htspec.2, htmin⟩
  have htOther := htspec.2
  unfold otherRadialBoundaries at htOther
  obtain ⟨exitLabel, hExit⟩ := Set.mem_iUnion.mp htOther
  have hExitNe : exitLabel ≠ source := by
    intro heq
    subst exitLabel
    simpa using hExit
  have hExitBoundary : trajectoryFrom start omega t ∈
      radialBoundary n center exitLabel := by
    simpa only [if_neg hExitNe] using hExit
  have htpos : 0 < t := by
    by_contra hnot
    have htzero : t = 0 := by omega
    have hExitStart : start ∈ radialBoundary n center exitLabel := by
      rw [htzero] at hExitBoundary
      change (start.1 + 0, start.2 + 0) ∈
        radialBoundary n center exitLabel at hExitBoundary
      simpa using hExitBoundary
    exact Set.disjoint_left.mp
      (radialBoundaries_disjoint_of_ne hn center hExitNe.symm)
        hstart hExitStart
  let rawPrefix : List (Fin (n + 2)) :=
    (List.range t).flatMap (fun q ↦
      radialLabelsAt n center (trajectoryFrom start omega q))
  have hprefixNonempty : rawPrefix ≠ [] := by
    apply List.ne_nil_of_mem (a := source)
    change source ∈ (List.range t).flatMap (fun q ↦
      radialLabelsAt n center (trajectoryFrom start omega q))
    rw [List.mem_flatMap]
    refine ⟨0, by simp [htpos], ?_⟩
    apply (mem_radialLabelsAt).2
    simpa using hstart
  have hprefixOnly : ∀ label ∈ rawPrefix, label = source := by
    intro label hlabel
    change label ∈ (List.range t).flatMap (fun q ↦
      radialLabelsAt n center (trajectoryFrom start omega q)) at hlabel
    rw [List.mem_flatMap] at hlabel
    obtain ⟨q, hq, hqLabel⟩ := hlabel
    by_contra hlabelNe
    apply htmin q (by simpa using hq)
    rw [otherRadialBoundaries]
    refine Set.mem_iUnion.mpr ⟨label, ?_⟩
    rw [if_neg hlabelNe]
    exact (mem_radialLabelsAt).1 hqLabel
  let remaining : ℕ := horizon - t
  have htadd : t + remaining = horizon := Nat.add_sub_of_le htspec.1
  let shifted : WalkPath := fun q ↦
    trajectoryFrom (trajectoryFrom start omega t) (shiftSteps t omega) q
  let suffixRest : List (Fin (n + 2)) :=
    (List.map Nat.succ (List.range remaining)).flatMap
      (fun q ↦ radialLabelsAt n center (shifted q))
  have hsuffixRaw : observedRadialLabels n center shifted remaining =
      exitLabel :: suffixRest := by
    unfold observedRadialLabels suffixRest
    rw [List.range_succ_eq_map]
    simp only [List.flatMap_cons, List.flatMap_map]
    rw [radialLabelsAt_eq_singleton_of_mem hn center _ exitLabel]
    · rfl
    · dsimp [shifted]
      simpa using hExitBoundary
  have hraw : observedRadialLabels n center
      (fun q ↦ trajectoryFrom start omega q) horizon =
        rawPrefix ++ exitLabel :: suffixRest := by
    rw [← htadd]
    unfold observedRadialLabels rawPrefix
    rw [range_add_succ_eq_append_shift, List.flatMap_append,
      List.flatMap_map]
    congr 1
    calc
      List.flatMap
          (fun q ↦ radialLabelsAt n center
            (trajectoryFrom start omega (t + q)))
          (List.range (remaining + 1)) =
          List.flatMap (fun q ↦ radialLabelsAt n center (shifted q))
            (List.range (remaining + 1)) := by
              apply List.flatMap_congr
              intro q _
              apply congrArg (radialLabelsAt n center)
              dsimp [shifted]
              exact (trajectoryFrom_shiftSteps_eq_absolute
                start omega t q).symm
      _ = exitLabel :: suffixRest := hsuffixRaw
  change compressLabels (observedRadialLabels n center
    (fun r ↦ trajectoryFrom start omega r) horizon) =
      source :: target :: tail at htrace
  rw [hraw, compressLabels_append_eq_cons_cons
    (source := source) (target := exitLabel) hExitNe.symm
      hprefixNonempty hprefixOnly] at htrace
  have hsecond := (List.cons.inj htrace).2
  have hExitEq : exitLabel = target := (List.cons.inj hsecond).1
  have htailRest : compressLabelsFrom (some exitLabel) suffixRest = tail :=
    (List.cons.inj hsecond).2
  subst exitLabel
  refine ⟨t, htspec.1, hfirst, ?_, ?_⟩
  · exact hExitBoundary
  · change compressLabels (observedRadialLabels n center shifted remaining) =
      target :: tail
    rw [hsuffixRaw]
    unfold compressLabels
    simp only [compressLabelsFrom, reduceCtorEq, if_false]
    rw [htailRest]

/-- Endpoint-integrated mass of one chronological radial transition. -/
def radialOneStepKernelENNReal
    (n : ℕ) (center : Point) (source target : Fin (n + 2))
    (start : Point) : ℝ≥0∞ :=
  fairSteps (radialOneStepAtom n center source target start)

/-! ## Chronological endpoint-chain factorization -/

/-- Finite literal endpoint type on one radial boundary. -/
abbrev RadialBoundaryPoint
    (n : ℕ) (center : Point) (label : Fin (n + 2)) :=
  DiscBoundaryPoint center (scaleRadius n label)

/-- Recursive chronological event for a list of next radial labels.  Each
physical interval is a first hit of a different radial boundary, and the
fresh tail starts at its actual random endpoint. -/
def radialChainAtom (n : ℕ) (center : Point) :
    Fin (n + 2) → List (Fin (n + 2)) → Point → Set StepPath
  | _, [], _ => Set.univ
  | source, target :: tail, start =>
      ⋃ endpoint : RadialBoundaryPoint n center target,
        boundaryExitMarkedSteps (otherRadialBoundaries n center source)
            {endpoint.1} start ∩
          postWithTopStoppingSteps
              (boundaryExitTime (otherRadialBoundaries n center source) start) ⁻¹'
            radialChainAtom n center target tail endpoint.1

/-- Endpoint-summed kernel of the chronological radial chain. -/
def radialChainKernelENNReal (n : ℕ) (center : Point) :
    Fin (n + 2) → List (Fin (n + 2)) → Point → ℝ≥0∞
  | _, [], _ => 1
  | source, target :: tail, start =>
      ∑ endpoint : RadialBoundaryPoint n center target,
        skeletonExitKernel (otherRadialBoundaries n center source)
            start endpoint.1 *
          radialChainKernelENNReal n center target tail endpoint.1

private theorem radialChainAtom_exists_chronologicalTrace_of_mem
    (n : ℕ) (hn : 2 ≤ n) (center : Point) :
    ∀ (source : Fin (n + 2)) (targets : List (Fin (n + 2)))
      (start : Point) (omega : StepPath),
      List.IsChain (fun left right : Fin (n + 2) ↦ left ≠ right)
        (source :: targets) →
      start ∈ radialBoundary n center source →
      omega ∈ radialChainAtom n center source targets start →
      ∃ horizon : ℕ,
        chronologicalRadialLabels n center
          (fun r ↦ trajectoryFrom start omega r) horizon = source :: targets := by
  intro source targets
  induction targets generalizing source with
  | nil =>
      intro start omega _ hstart _
      refine ⟨0, ?_⟩
      unfold chronologicalRadialLabels observedRadialLabels
      simp only [zero_add, List.range_one, List.flatMap_cons,
        List.flatMap_nil, List.append_nil]
      rw [show trajectoryFrom start omega 0 = start by
        simp [trajectoryFrom]]
      rw [radialLabelsAt_eq_singleton_of_mem hn center _ source]
      · rfl
      · simpa using hstart
  | cons target tail ih =>
      intro start omega hlabels hstart homega
      have hlabelParts := List.isChain_cons_cons.mp hlabels
      rw [radialChainAtom] at homega
      obtain ⟨endpoint, hstep, htail⟩ := Set.mem_iUnion.mp homega
      obtain ⟨t, hfirst, hpoint⟩ :=
        (mem_boundaryExitMarkedSteps_iff_exists_first _ _ _ _).1 hstep
      have hpointEq : trajectoryFrom start omega t = endpoint.1 := by
        simpa only [Set.mem_singleton_iff] using hpoint
      have htime := boundaryExitTime_eq_of_absoluteBoundaryFirstAt hfirst
      have hpost := postWithTopStoppingSteps_eq_shiftSteps_of_eq htime
      change postWithTopStoppingSteps
        (boundaryExitTime (otherRadialBoundaries n center source) start)
          omega ∈ radialChainAtom n center target tail endpoint.1 at htail
      rw [hpost] at htail
      obtain ⟨q, htrace⟩ := ih target endpoint.1 (shiftSteps t omega)
        hlabelParts.2 endpoint.2 htail
      refine ⟨t + q, chronologicalRadialLabels_splice_firstDifferent
        hn center start source target omega tail hlabelParts.1 hstart
        hfirst ?_ ?_⟩
      · rw [hpointEq]
        exact endpoint.2
      · simpa only [hpointEq] using htrace

private theorem absoluteBoundaryFirstAt_concat_shift
    {boundary : Set Point} {start point : Point} {omega : StepPath}
    {t q : ℕ} (hbefore : ∀ r < t,
      trajectoryFrom start omega r ∉ boundary)
    (hpoint : trajectoryFrom start omega t = point)
    (htail : AbsoluteBoundaryFirstAt boundary point
      (shiftSteps t omega) q) :
    AbsoluteBoundaryFirstAt boundary start omega (t + q) := by
  constructor
  · rw [← trajectoryFrom_shiftSteps_eq_absolute start omega t q, hpoint]
    exact htail.1
  · intro r hr
    by_cases hrt : r < t
    · exact hbefore r hrt
    · have htr : t ≤ r := Nat.le_of_not_gt hrt
      rw [← Nat.add_sub_of_le htr,
        ← trajectoryFrom_shiftSteps_eq_absolute, hpoint]
      exact htail.2 (r - t) (by omega)

private theorem radialChainAtom_exists_firstZero_of_mem
    (n : ℕ) (center : Point) :
    ∀ (initial : Fin (n + 2)) (beforeZero : List (Fin (n + 2)))
      (start : Point) (omega : StepPath),
      (⟨0, by omega⟩ : Fin (n + 2)) ∉ initial :: beforeZero →
      omega ∈ radialChainAtom n center initial
        (beforeZero ++ [⟨0, by omega⟩]) start →
      ∃ horizon : ℕ,
        AbsoluteBoundaryFirstAt
          (radialBoundary n center ⟨0, by omega⟩) start omega horizon := by
  intro initial beforeZero
  induction beforeZero generalizing initial with
  | nil =>
      intro start omega hnozero homega
      change omega ∈ radialChainAtom n center initial
        [⟨0, by omega⟩] start at homega
      rw [radialChainAtom.eq_def] at homega
      obtain ⟨endpoint, hstep, _⟩ := Set.mem_iUnion.mp homega
      obtain ⟨t, hfirst, hpoint⟩ :=
        (mem_boundaryExitMarkedSteps_iff_exists_first _ _ _ _).1 hstep
      have hpointEq : trajectoryFrom start omega t = endpoint.1 := by
        simpa only [Set.mem_singleton_iff] using hpoint
      refine ⟨t, ?_⟩
      constructor
      · rw [hpointEq]
        exact endpoint.2
      · intro r hr
        intro hzero
        apply hfirst.2 r hr
        rw [otherRadialBoundaries]
        refine Set.mem_iUnion.mpr ⟨⟨0, by omega⟩, ?_⟩
        rw [if_neg]
        · exact hzero
        · simpa using hnozero
  | cons target tail ih =>
      intro start omega hnozero homega
      change omega ∈ radialChainAtom n center initial
        (target :: (tail ++ [⟨0, by omega⟩])) start at homega
      rw [radialChainAtom.eq_def] at homega
      obtain ⟨endpoint, hstep, htail⟩ := Set.mem_iUnion.mp homega
      obtain ⟨t, hfirst, hpoint⟩ :=
        (mem_boundaryExitMarkedSteps_iff_exists_first _ _ _ _).1 hstep
      have hpointEq : trajectoryFrom start omega t = endpoint.1 := by
        simpa only [Set.mem_singleton_iff] using hpoint
      have htime := boundaryExitTime_eq_of_absoluteBoundaryFirstAt hfirst
      have hpost := postWithTopStoppingSteps_eq_shiftSteps_of_eq htime
      change postWithTopStoppingSteps
        (boundaryExitTime (otherRadialBoundaries n center initial) start)
          omega ∈ radialChainAtom n center target
            (tail ++ [⟨0, by omega⟩]) endpoint.1 at htail
      rw [hpost] at htail
      have hnozeroParts :
          (⟨0, by omega⟩ : Fin (n + 2)) ≠ initial ∧
          (⟨0, by omega⟩ : Fin (n + 2)) ≠ target ∧
          (⟨0, by omega⟩ : Fin (n + 2)) ∉ tail := by
        simpa using hnozero
      have htailNoZero : (⟨0, by omega⟩ : Fin (n + 2)) ∉ target :: tail := by
        simpa using hnozeroParts.2
      obtain ⟨q, htailFirst⟩ := ih target endpoint.1
        (shiftSteps t omega) htailNoZero htail
      refine ⟨t + q, absoluteBoundaryFirstAt_concat_shift ?_
        hpointEq htailFirst⟩
      intro r hr hzero
      apply hfirst.2 r hr
      rw [otherRadialBoundaries]
      refine Set.mem_iUnion.mpr ⟨⟨0, by omega⟩, ?_⟩
      rw [if_neg]
      · exact hzero
      · exact hnozeroParts.1

private theorem radialChainAtom_exists_firstZero_and_trace_of_mem
    (n : ℕ) (hn : 2 ≤ n) (center : Point) :
    ∀ (initial : Fin (n + 2)) (beforeZero : List (Fin (n + 2)))
      (start : Point) (omega : StepPath),
      List.IsChain (fun left right : Fin (n + 2) ↦ left ≠ right)
        (initial :: beforeZero ++ [⟨0, by omega⟩]) →
      (⟨0, by omega⟩ : Fin (n + 2)) ∉ initial :: beforeZero →
      start ∈ radialBoundary n center initial →
      omega ∈ radialChainAtom n center initial
        (beforeZero ++ [⟨0, by omega⟩]) start →
      ∃ horizon : ℕ,
        AbsoluteBoundaryFirstAt
          (radialBoundary n center ⟨0, by omega⟩) start omega horizon ∧
        chronologicalRadialLabels n center
          (fun r ↦ trajectoryFrom start omega r) horizon =
            initial :: beforeZero ++ [⟨0, by omega⟩] := by
  intro initial beforeZero
  induction beforeZero generalizing initial with
  | nil =>
      intro start omega hlabels hnozero hstart homega
      have hlabelParts := List.isChain_cons_cons.mp hlabels
      change omega ∈ radialChainAtom n center initial
        [⟨0, by omega⟩] start at homega
      rw [radialChainAtom.eq_def] at homega
      obtain ⟨endpoint, hstep, _⟩ := Set.mem_iUnion.mp homega
      obtain ⟨t, hfirst, hpoint⟩ :=
        (mem_boundaryExitMarkedSteps_iff_exists_first _ _ _ _).1 hstep
      have hpointEq : trajectoryFrom start omega t = endpoint.1 := by
        simpa only [Set.mem_singleton_iff] using hpoint
      have hzeroTrace : chronologicalRadialLabels n center
          (fun r ↦ trajectoryFrom endpoint.1 (shiftSteps t omega) r) 0 =
            [⟨0, by omega⟩] := by
        unfold chronologicalRadialLabels observedRadialLabels
        simp only [zero_add, List.range_one, List.flatMap_cons,
          List.flatMap_nil, List.append_nil]
        rw [show trajectoryFrom endpoint.1 (shiftSteps t omega) 0 = endpoint.1 by
          simp [trajectoryFrom]]
        rw [radialLabelsAt_eq_singleton_of_mem hn center _ _ endpoint.2]
        rfl
      refine ⟨t, ?_, ?_⟩
      · constructor
        · rw [hpointEq]
          exact endpoint.2
        · intro r hr hzero
          apply hfirst.2 r hr
          rw [otherRadialBoundaries]
          refine Set.mem_iUnion.mpr ⟨⟨0, by omega⟩, ?_⟩
          rw [if_neg]
          · exact hzero
          · simpa using hnozero
      · exact chronologicalRadialLabels_splice_firstDifferent
          hn center start initial ⟨0, by omega⟩ omega []
            hlabelParts.1 hstart hfirst
            (by
              rw [hpointEq]
              change endpoint.1 ∈ discBoundary center (scaleRadius n 0)
              exact endpoint.2)
            (by
              rw [hpointEq]
              convert hzeroTrace using 1)
  | cons target tail ih =>
      intro start omega hlabels hnozero hstart homega
      have hlabelParts := List.isChain_cons_cons.mp hlabels
      change omega ∈ radialChainAtom n center initial
        (target :: (tail ++ [⟨0, by omega⟩])) start at homega
      rw [radialChainAtom.eq_def] at homega
      obtain ⟨endpoint, hstep, htail⟩ := Set.mem_iUnion.mp homega
      obtain ⟨t, hfirst, hpoint⟩ :=
        (mem_boundaryExitMarkedSteps_iff_exists_first _ _ _ _).1 hstep
      have hpointEq : trajectoryFrom start omega t = endpoint.1 := by
        simpa only [Set.mem_singleton_iff] using hpoint
      have htime := boundaryExitTime_eq_of_absoluteBoundaryFirstAt hfirst
      have hpost := postWithTopStoppingSteps_eq_shiftSteps_of_eq htime
      change postWithTopStoppingSteps
        (boundaryExitTime (otherRadialBoundaries n center initial) start)
          omega ∈ radialChainAtom n center target
            (tail ++ [⟨0, by omega⟩]) endpoint.1 at htail
      rw [hpost] at htail
      have hnozeroParts :
          (⟨0, by omega⟩ : Fin (n + 2)) ≠ initial ∧
          (⟨0, by omega⟩ : Fin (n + 2)) ≠ target ∧
          (⟨0, by omega⟩ : Fin (n + 2)) ∉ tail := by
        simpa using hnozero
      have htailNoZero : (⟨0, by omega⟩ : Fin (n + 2)) ∉ target :: tail := by
        simpa using hnozeroParts.2
      obtain ⟨q, htailFirst, htailTrace⟩ := ih target endpoint.1
        (shiftSteps t omega) hlabelParts.2 htailNoZero endpoint.2 htail
      refine ⟨t + q, absoluteBoundaryFirstAt_concat_shift ?_
        hpointEq htailFirst, ?_⟩
      · intro r hr hzero
        apply hfirst.2 r hr
        rw [otherRadialBoundaries]
        refine Set.mem_iUnion.mpr ⟨⟨0, by omega⟩, ?_⟩
        rw [if_neg]
        · exact hzero
        · exact hnozeroParts.1
      · exact chronologicalRadialLabels_splice_firstDifferent
          hn center start initial target omega
            (tail ++ [⟨0, by omega⟩]) hlabelParts.1 hstart hfirst
            (by
              rw [hpointEq]
              change endpoint.1 ∈ discBoundary center (scaleRadius n target)
              exact endpoint.2)
            (by
              rw [hpointEq]
              convert htailTrace using 1 <;> simp only [List.cons_append])

private theorem mem_radialChainAtom_of_chronologicalTrace
    (n : ℕ) (hn : 2 ≤ n) (center : Point) :
    ∀ (source : Fin (n + 2)) (targets : List (Fin (n + 2)))
      (start : Point) (omega : StepPath) (horizon : ℕ),
      List.IsChain (fun left right : Fin (n + 2) ↦ left ≠ right)
        (source :: targets) →
      start ∈ radialBoundary n center source →
      chronologicalRadialLabels n center
        (fun r ↦ trajectoryFrom start omega r) horizon = source :: targets →
      omega ∈ radialChainAtom n center source targets start := by
  intro source targets
  induction targets generalizing source with
  | nil =>
      intro start omega horizon _ _ _
      simp [radialChainAtom]
  | cons target tail ih =>
      intro start omega horizon hlabels hstart htrace
      have hlabelParts := List.isChain_cons_cons.mp hlabels
      obtain ⟨t, htle, hfirst, htarget, htailTrace⟩ :=
        chronologicalRadialLabels_unsplice_firstDifferent
          hn center start source target omega tail hlabelParts.1 hstart htrace
      let endpoint : RadialBoundaryPoint n center target :=
        ⟨trajectoryFrom start omega t, htarget⟩
      have hstep : omega ∈ boundaryExitMarkedSteps
          (otherRadialBoundaries n center source) {endpoint.1} start := by
        apply (mem_boundaryExitMarkedSteps_iff_of_absoluteBoundaryFirstAt
          hfirst).2
        simp [endpoint]
      have htail : shiftSteps t omega ∈
          radialChainAtom n center target tail endpoint.1 := by
        apply ih target endpoint.1 (shiftSteps t omega) (horizon - t)
          hlabelParts.2 endpoint.2
        simpa only [endpoint] using htailTrace
      have htime := boundaryExitTime_eq_of_absoluteBoundaryFirstAt hfirst
      have hpost := postWithTopStoppingSteps_eq_shiftSteps_of_eq htime
      rw [radialChainAtom.eq_def]
      refine Set.mem_iUnion.mpr ⟨endpoint, hstep, ?_⟩
      change postWithTopStoppingSteps
        (boundaryExitTime (otherRadialBoundaries n center source) start)
          omega ∈ radialChainAtom n center target tail endpoint.1
      rw [hpost]
      exact htail

/-- Generic arbitrary-source form of the source-correct stopped-trace
factorization.  It is the reusable core for truncated post-separation
radial words. -/
theorem radialChainAtom_eq_firstZeroTraceEvent
    {n : ℕ} (hn : 2 ≤ n) (center start : Point)
    (source : Fin (n + 2)) (beforeZero : List (Fin (n + 2)))
    (hchain : List.IsChain
      (fun left right : Fin (n + 2) ↦ left ≠ right)
      (source :: beforeZero ++ [⟨0, by omega⟩]))
    (hnozero : (⟨0, by omega⟩ : Fin (n + 2)) ∉ source :: beforeZero)
    (hstart : start ∈ radialBoundary n center source) :
    radialChainAtom n center source
        (beforeZero ++ [⟨0, by omega⟩]) start =
      {omega | ∃ horizon : ℕ,
        AbsoluteBoundaryFirstAt
          (radialBoundary n center ⟨0, by omega⟩) start omega horizon ∧
        chronologicalRadialLabels n center
          (fun r ↦ trajectoryFrom start omega r) horizon =
            source :: beforeZero ++ [⟨0, by omega⟩]} := by
  ext omega
  constructor
  · intro homega
    exact radialChainAtom_exists_firstZero_and_trace_of_mem
      n hn center source beforeZero start omega hchain hnozero hstart homega
  · rintro ⟨horizon, _, htrace⟩
    have hchain' : List.IsChain
        (fun left right : Fin (n + 2) ↦ left ≠ right)
        (source :: (beforeZero ++ [⟨0, by omega⟩])) := by
      simpa only [List.cons_append] using hchain
    exact mem_radialChainAtom_of_chronologicalTrace
      n hn center source
        (beforeZero ++ [⟨0, Nat.zero_lt_succ (n + 1)⟩])
        start omega horizon hchain' hstart
        (by simpa only [List.cons_append] using htrace)

theorem measurableSet_radialChainAtom (n : ℕ) (center : Point) :
    ∀ (source : Fin (n + 2)) (targets : List (Fin (n + 2))) (start : Point),
      MeasurableSet (radialChainAtom n center source targets start) := by
  intro source targets
  induction targets generalizing source with
  | nil =>
      intro start
      exact MeasurableSet.univ
  | cons target tail ih =>
      intro start
      apply MeasurableSet.iUnion
      intro endpoint
      exact (measurableSet_boundaryExitMarkedSteps _ _ _).inter
        ((ih target endpoint.1).preimage
          (measurable_postWithTopStoppingSteps
            (isStoppingTime_boundaryExitTime
              (otherRadialBoundaries n center source) start)))

private theorem disjoint_boundaryExitMarkedSteps_singletons
    (boundary : Set Point) (start left right : Point) (hne : left ≠ right) :
    Disjoint (boundaryExitMarkedSteps boundary {left} start)
      (boundaryExitMarkedSteps boundary {right} start) := by
  rw [Set.disjoint_left]
  intro omega hleft hright
  apply hne
  simpa only [Set.mem_singleton_iff] using hleft.2.symm.trans hright.2

private theorem radialChainAtom_endpoint_pairwise
    (n : ℕ) (center : Point) (source target : Fin (n + 2))
    (tail : List (Fin (n + 2))) (start : Point) :
    Pairwise fun left right : RadialBoundaryPoint n center target ↦
      Disjoint
        (boundaryExitMarkedSteps (otherRadialBoundaries n center source)
              {left.1} start ∩
            postWithTopStoppingSteps
                (boundaryExitTime (otherRadialBoundaries n center source) start) ⁻¹'
              radialChainAtom n center target tail left.1)
        (boundaryExitMarkedSteps (otherRadialBoundaries n center source)
              {right.1} start ∩
            postWithTopStoppingSteps
                (boundaryExitTime (otherRadialBoundaries n center source) start) ⁻¹'
              radialChainAtom n center target tail right.1) := by
  intro left right hne
  exact (disjoint_boundaryExitMarkedSteps_singletons
    (otherRadialBoundaries n center source) start left.1 right.1
    (fun heq ↦ hne (Subtype.ext heq))).mono inter_subset_left inter_subset_left

private theorem fairSteps_boundaryExitMarkedSteps_inter_post
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
    exact ⟨homega, homega.1⟩
  rw [hfinite] at hmarkov
  exact hmarkov

/-- Exact finite strong-Markov factorization of a chronological radial
chain, with the random endpoint passed to the next transition. -/
theorem fairSteps_radialChainAtom (n : ℕ) (center : Point) :
    ∀ (source : Fin (n + 2)) (targets : List (Fin (n + 2))) (start : Point),
      fairSteps (radialChainAtom n center source targets start) =
        radialChainKernelENNReal n center source targets start := by
  intro source targets
  induction targets generalizing source with
  | nil =>
      intro start
      simp [radialChainAtom, radialChainKernelENNReal]
  | cons target tail ih =>
      intro start
      rw [radialChainAtom, measure_iUnion
        (radialChainAtom_endpoint_pairwise n center source target tail start)]
      · rw [radialChainKernelENNReal, tsum_fintype]
        apply Finset.sum_congr rfl
        intro endpoint _
        rw [fairSteps_boundaryExitMarkedSteps_inter_post,
          ih target endpoint.1]
        rfl
        exact measurableSet_radialChainAtom n center target tail endpoint.1
      · intro endpoint
        exact (measurableSet_boundaryExitMarkedSteps _ _ _).inter
          ((measurableSet_radialChainAtom n center target tail endpoint.1).preimage
            (measurable_postWithTopStoppingSteps
              (isStoppingTime_boundaryExitTime
                (otherRadialBoundaries n center source) start)))

/-- Recursive chronological event associated with a finite admissible radial
word. -/
def radialWordChainAtom {n L : ℕ} (center start : Point)
    (word : RadialLabelWord n L) : Set StepPath :=
  radialChainAtom n center (word.level ⟨0, by omega⟩) word.toList.tail start

/-- Endpoint-summed chronological kernel associated with a radial word. -/
def radialWordChainKernelENNReal {n L : ℕ} (center start : Point)
    (word : RadialLabelWord n L) : ℝ≥0∞ :=
  radialChainKernelENNReal n center
    (word.level ⟨0, by omega⟩) word.toList.tail start

/-- Every recursive chronological endpoint-chain realization of an
admissible word is a realization of its literal stopped radial-word atom.
The first level-zero certificate and the compressed trace are produced at
the same recursive stopping horizon. -/
theorem radialWordChainAtom_subset_radialLabelWordAtom
    {n L : ℕ} (hn : 2 ≤ n) (center start : Point)
    (word : RadialLabelWord n L)
    (hstart : start ∈ radialBoundary n center ⟨1, by omega⟩) :
    radialWordChainAtom center start word ⊆
      radialLabelWordAtom n L center start word := by
  classical
  intro omega homega
  have hLpos : 0 < L := by
    by_contra hnot
    have hLzero : L = 0 := by omega
    subst L
    have hindex : (⟨0, by omega⟩ : Fin (0 + 1)) = Fin.last 0 := by
      apply Fin.ext
      rfl
    have hlevel := congrArg word.level hindex
    have hone := word.startsAtOne
    have hzero := word.endsAtZero
    have : (⟨1, by omega⟩ : Fin (n + 2)) = ⟨0, by omega⟩ := by
      rw [← hone, hlevel, hzero]
    have hval := congrArg Fin.val this
    norm_num at hval
  let source : Fin (n + 2) := word.level ⟨0, by omega⟩
  let targets : List (Fin (n + 2)) := word.toList.tail
  have hlist : word.toList = source ::
      List.ofFn (fun j : Fin L ↦ word.level j.succ) := by
    simp [RadialLabelWord.toList, List.ofFn_succ, source]
  have htargets : targets =
      List.ofFn (fun j : Fin L ↦ word.level j.succ) := by
    change word.toList.tail =
      List.ofFn (fun j : Fin L ↦ word.level j.succ)
    rw [hlist]
    rfl
  have hlistTargets : word.toList = source :: targets :=
    hlist.trans (congrArg (source :: ·) htargets.symm)
  have htargetsNe : targets ≠ [] := by
    intro hnil
    have hlength := congrArg List.length htargets
    rw [hnil] at hlength
    simp only [List.length_nil, List.length_ofFn] at hlength
    omega
  have hlast : targets.getLast htargetsNe = ⟨0, by omega⟩ := by
    have hfnNe : List.ofFn (fun j : Fin L ↦ word.level j.succ) ≠ [] := by
      intro hnil
      have hlength := congrArg List.length hnil
      simp only [List.length_ofFn, List.length_nil] at hlength
      omega
    calc
      targets.getLast htargetsNe =
          (List.ofFn (fun j : Fin L ↦ word.level j.succ)).getLast hfnNe :=
        List.getLast_congr htargetsNe hfnNe htargets
      _ = ⟨0, by omega⟩ := by
        rw [List.getLast_ofFn]
        have hindex : (⟨L - 1, by omega⟩ : Fin L).succ = Fin.last L := by
          apply Fin.ext
          simp only [Fin.succ_mk, Fin.val_last]
          omega
        rw [hindex]
        exact word.endsAtZero
  have hsplit : targets.dropLast ++ [⟨0, by omega⟩] = targets := by
    have h := List.dropLast_append_getLast htargetsNe
    rwa [hlast] at h
  have hadjacent : List.IsChain
      (fun left right : Fin (n + 2) ↦ Nat.dist left.val right.val = 1)
      word.toList := by
    rw [RadialLabelWord.toList, List.isChain_ofFn]
    intro i hi
    exact word.adjacent ⟨i, by omega⟩
  have hdifferent : List.IsChain
      (fun left right : Fin (n + 2) ↦ left ≠ right) word.toList := by
    exact hadjacent.imp (by
      intro left right hdist heq
      subst right
      simp at hdist)
  have hchain : List.IsChain
      (fun left right : Fin (n + 2) ↦ left ≠ right)
      (source :: targets.dropLast ++ [⟨0, by omega⟩]) := by
    simpa only [List.cons_append, hsplit, ← hlistTargets] using hdifferent
  have hdrop : source :: targets.dropLast = word.toList.dropLast := by
    rw [hlistTargets, List.dropLast_cons_of_ne_nil htargetsNe]
  have hnozero : (⟨0, by omega⟩ : Fin (n + 2)) ∉
      source :: targets.dropLast := by
    rw [hdrop]
    intro hmem
    obtain ⟨i, hi⟩ := List.get_of_mem hmem
    have hiLt : i.val < word.toList.dropLast.length := i.isLt
    have hiWord : word.toList[i.val] = (⟨0, by omega⟩ : Fin (n + 2)) := by
      rw [← List.getElem_dropLast hiLt]
      exact hi
    have hiBound : i.val < L := by
      have hdropLength : word.toList.dropLast.length = L := by
        rw [List.length_dropLast, RadialLabelWord.length_toList]
        omega
      omega
    have hiLevel : word.level ⟨i.val, by omega⟩ =
        (⟨0, by omega⟩ : Fin (n + 2)) := by
      change (List.ofFn word.level)[i.val] =
        (⟨0, by omega⟩ : Fin (n + 2)) at hiWord
      rw [List.getElem_ofFn] at hiWord
      exact hiWord
    exact word.beforeFinal_ne_zero ⟨i.val, hiBound⟩
      (congrArg Fin.val hiLevel)
  have hsource : source = ⟨1, by omega⟩ := word.startsAtOne
  have hstartSource : start ∈ radialBoundary n center source := by
    rw [hsource]
    exact hstart
  change omega ∈ radialChainAtom n center source targets start at homega
  have homegaSplit : omega ∈ radialChainAtom n center source
      (targets.dropLast ++ [⟨0, by omega⟩]) start := by
    rwa [hsplit]
  obtain ⟨horizon, hfirst, htrace⟩ :=
    radialChainAtom_exists_firstZero_and_trace_of_mem
      n hn center source targets.dropLast start omega hchain hnozero
        hstartSource homegaSplit
  apply (mem_radialLabelWordAtom_iff n L center start word omega).2
  refine ⟨horizon, hfirst, ?_⟩
  simpa only [List.cons_append, hsplit, ← hlistTargets] using htrace

/-- Conversely, a literal stopped path with the prescribed compressed
radial trace belongs to the recursive random-endpoint chain event. -/
theorem radialLabelWordAtom_subset_radialWordChainAtom
    {n L : ℕ} (hn : 2 ≤ n) (center start : Point)
    (word : RadialLabelWord n L)
    (hstart : start ∈ radialBoundary n center ⟨1, by omega⟩) :
    radialLabelWordAtom n L center start word ⊆
      radialWordChainAtom center start word := by
  classical
  intro omega homega
  obtain ⟨horizon, _, htrace⟩ :=
    (mem_radialLabelWordAtom_iff n L center start word omega).1 homega
  let source : Fin (n + 2) := word.level ⟨0, by omega⟩
  let targets : List (Fin (n + 2)) := word.toList.tail
  have hlist : word.toList = source ::
      List.ofFn (fun j : Fin L ↦ word.level j.succ) := by
    simp [RadialLabelWord.toList, List.ofFn_succ, source]
  have htargets : targets =
      List.ofFn (fun j : Fin L ↦ word.level j.succ) := by
    change word.toList.tail =
      List.ofFn (fun j : Fin L ↦ word.level j.succ)
    rw [hlist]
    rfl
  have hlistTargets : word.toList = source :: targets :=
    hlist.trans (congrArg (source :: ·) htargets.symm)
  have hadjacent : List.IsChain
      (fun left right : Fin (n + 2) ↦ Nat.dist left.val right.val = 1)
      word.toList := by
    rw [RadialLabelWord.toList, List.isChain_ofFn]
    intro i hi
    exact word.adjacent ⟨i, by omega⟩
  have hdifferent : List.IsChain
      (fun left right : Fin (n + 2) ↦ left ≠ right)
      (source :: targets) := by
    rw [← hlistTargets]
    exact hadjacent.imp (by
      intro left right hdist heq
      subst right
      simp at hdist)
  have hsource : source = ⟨1, by omega⟩ := word.startsAtOne
  have hstartSource : start ∈ radialBoundary n center source := by
    rw [hsource]
    exact hstart
  change omega ∈ radialChainAtom n center source targets start
  apply mem_radialChainAtom_of_chronologicalTrace n hn center source targets
    start omega horizon hdifferent hstartSource
  simpa only [← hlistTargets] using htrace

/-- Exact pathwise identification of the literal stopped radial word and
its source-correct chronological random-endpoint chain. -/
theorem radialWordChainAtom_eq_radialLabelWordAtom
    {n L : ℕ} (hn : 2 ≤ n) (center start : Point)
    (word : RadialLabelWord n L)
    (hstart : start ∈ radialBoundary n center ⟨1, by omega⟩) :
    radialWordChainAtom center start word =
      radialLabelWordAtom n L center start word := by
  apply Set.Subset.antisymm
  · exact radialWordChainAtom_subset_radialLabelWordAtom
      hn center start word hstart
  · exact radialLabelWordAtom_subset_radialWordChainAtom
      hn center start word hstart

/-- Whole-word probability is the sum over spatial endpoint sequences of
the product of the one-step endpoint kernels, with no interval repeated. -/
theorem fairSteps_radialWordChainAtom {n L : ℕ} (center start : Point)
    (word : RadialLabelWord n L) :
    fairSteps (radialWordChainAtom center start word) =
      radialWordChainKernelENNReal center start word := by
  exact fairSteps_radialChainAtom n center _ _ start

/-- The literal stopped-word probability is exactly the chronological
finite Strong-Markov endpoint-chain kernel. -/
theorem fairSteps_radialLabelWordAtom_eq_radialWordChainKernelENNReal
    {n L : ℕ} (hn : 2 ≤ n) (center start : Point)
    (word : RadialLabelWord n L)
    (hstart : start ∈ radialBoundary n center ⟨1, by omega⟩) :
    fairSteps (radialLabelWordAtom n L center start word) =
      radialWordChainKernelENNReal center start word := by
  rw [← radialWordChainAtom_eq_radialLabelWordAtom hn center start word hstart]
  exact fairSteps_radialWordChainAtom center start word

end

end Erdos1165.AnnularRadialLabelWord
