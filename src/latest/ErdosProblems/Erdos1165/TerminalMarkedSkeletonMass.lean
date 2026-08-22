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

import ErdosProblems.Erdos1165.TerminalMarkedSkeletonDecomposition
import ErdosProblems.Erdos1165.TerminalSkeletonInsertionInvariance

/-!
# Exact masses of the literal terminal skeleton atoms

The weight below is the mass of the complete retained stopped word, including
the arbitrary increment prefix before `start`.  It is zero for a compressed
code which is not the skeleton of any stopped successful path.  Both the
unmarked and marked atoms use this same weight; all future/profile data stays
inside it.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace Erdos1165.TerminalMarkedSkeletonMass

open ThickPoint Proposition13Measurability TerminalExcursionPathwise
open MarkedBridgeFactorization MarkedTerminalDisintegration
open MarkedBoundaryVisitKernel
open TerminalSkeletonWords TerminalSkeletonInvariance
open TerminalSkeletonFactorization TerminalMarkedSkeletonDecomposition
open TerminalSkeletonInsertionInvariance

noncomputable section

/-- The raw compressed code underlying boundary-supported skeleton data. -/
def rawSupportedTerminalCode
    {scale : ℕ} {profileDelta : ℝ} {x : Point}
    (data : TerminalSkeletonData (terminalCount scale profileDelta))
    (entrance : Fin (terminalCount scale profileDelta) →
      TerminalEntrance scale x)
    (exit : Fin (terminalCount scale profileDelta) →
      TerminalExit scale x) :
    TerminalSkeletonCode (terminalCount scale profileDelta) :=
  eraseSupportedSkeletonIndex (data, (entrance, exit))

/-- A nonempty raw successful skeleton atom witnesses validity of its code. -/
theorem validTerminalSkeleton_of_mem_stoppedTerminalSkeletonAtom
    {start scale : ℕ} {profileDelta : ℝ} {x : Point}
    {code : TerminalSkeletonCode (terminalCount scale profileDelta)}
    {omega : StepPath}
    (homega : omega ∈
      stoppedTerminalSkeletonAtom start scale profileDelta x code) :
    ValidTerminalSkeleton scale profileDelta x code := by
  obtain ⟨horizon, hsuccessful, hcode⟩ := Set.mem_iUnion.mp homega
  exact ⟨horizon, shiftSteps start omega,
    hsuccessful.1, hsuccessful.2, hcode⟩

/-- Invalid raw compressed codes have empty successful skeleton fibres. -/
theorem stoppedTerminalSkeletonAtom_eq_empty_of_not_valid
    {start scale : ℕ} {profileDelta : ℝ} {x : Point}
    {code : TerminalSkeletonCode (terminalCount scale profileDelta)}
    (hinvalid : ¬ ValidTerminalSkeleton scale profileDelta x code) :
    stoppedTerminalSkeletonAtom start scale profileDelta x code = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro omega homega
  exact hinvalid
    (validTerminalSkeleton_of_mem_stoppedTerminalSkeletonAtom homega)

/-- Forget the visit vector in a raw marked compressed code. -/
def forgetTerminalVisits
    {Data Entrance Exit : Type*} {m : ℕ}
    (code : MarkedSkeletonPartition.MarkedIndex Data Entrance Exit m) :
    MarkedSkeletonPartition.SkeletonIndex Data Entrance Exit m :=
  (code.1, (code.2.1, code.2.2.1))

@[simp] theorem forgetTerminalVisits_extractMarkedTerminalCode
    (scale horizon : ℕ) (profileDelta : ℝ) (x : Point) (omega : StepPath) :
    forgetTerminalVisits
        (extractMarkedTerminalCode scale horizon profileDelta x omega) =
      extractTerminalSkeletonCode scale horizon profileDelta x omega := by
  rfl

/-- Every marked skeleton fibre is contained in the corresponding unmarked
fibre obtained by forgetting its terminal visit vector. -/
theorem stoppedMarkedTerminalAtom_subset_stoppedTerminalSkeletonAtom
    {start scale : ℕ} {profileDelta : ℝ} {x : Point}
    {code : MarkedSkeletonPartition.MarkedIndex
      (TerminalSkeletonData (terminalCount scale profileDelta)) Point Point
      (terminalCount scale profileDelta)} :
    stoppedMarkedTerminalAtom start scale profileDelta x code ⊆
      stoppedTerminalSkeletonAtom start scale profileDelta x
        (forgetTerminalVisits code) := by
  intro omega homega
  obtain ⟨horizon, hsuccessful, hcode⟩ := Set.mem_iUnion.mp homega
  apply Set.mem_iUnion.mpr
  refine ⟨horizon, hsuccessful, ?_⟩
  calc
    extractTerminalSkeletonCode scale horizon profileDelta x
        (shiftSteps start omega) =
        forgetTerminalVisits
          (extractMarkedTerminalCode scale horizon profileDelta x
            (shiftSteps start omega)) := by rw [forgetTerminalVisits_extractMarkedTerminalCode]
    _ = forgetTerminalVisits code := congrArg forgetTerminalVisits hcode

/-- A marked fibre is empty whenever its underlying compressed code is
invalid. -/
theorem stoppedMarkedTerminalAtom_eq_empty_of_not_valid
    {start scale : ℕ} {profileDelta : ℝ} {x : Point}
    {code : MarkedSkeletonPartition.MarkedIndex
      (TerminalSkeletonData (terminalCount scale profileDelta)) Point Point
      (terminalCount scale profileDelta)}
    (hinvalid : ¬ ValidTerminalSkeleton scale profileDelta x
      (forgetTerminalVisits code)) :
    stoppedMarkedTerminalAtom start scale profileDelta x code = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro omega homega
  exact hinvalid (validTerminalSkeleton_of_mem_stoppedTerminalSkeletonAtom
    (stoppedMarkedTerminalAtom_subset_stoppedTerminalSkeletonAtom homega))

/-- Retained complementary-word mass, extended by zero to invalid supported
codes.  No bridge duration, visit count, or absolute horizon occurs here. -/
def terminalSkeletonWeight
    (start scale : ℕ) (profileDelta : ℝ) (x : Point) (hscale : 1 ≤ scale)
    (data : TerminalSkeletonData (terminalCount scale profileDelta))
    (entrance : Fin (terminalCount scale profileDelta) →
      TerminalEntrance scale x)
    (exit : Fin (terminalCount scale profileDelta) →
      TerminalExit scale x) : ℝ≥0∞ := by
  classical
  exact if hvalid : ValidTerminalSkeleton scale profileDelta x
      (rawSupportedTerminalCode data entrance exit) then
    (validUnmarkedComplementarySkeletonAtom (start := start)
      (rawSupportedTerminalCode data entrance exit) hscale hvalid).weight
  else 0

/-- Exact unmarked mass factorization once pathwise insertion invariance has
identified the raw stopped skeleton atom with the insertion event. -/
theorem fairSteps_stoppedTerminalSkeletonAtom_eq_weight_mul
    {start scale : ℕ} {profileDelta : ℝ} {x : Point}
    (code : TerminalSkeletonCode (terminalCount scale profileDelta))
    (hscale : 1 ≤ scale)
    (hvalid : ValidTerminalSkeleton scale profileDelta x code)
    (hevent : stoppedTerminalSkeletonAtom start scale profileDelta x code =
      unmarkedTerminalInsertionEvent (start := start) (scale := scale)
        (x := x) code) :
    fairSteps (stoppedTerminalSkeletonAtom start scale profileDelta x code) =
      (validUnmarkedComplementarySkeletonAtom (start := start)
        code hscale hvalid).weight *
        ∏ j, terminalSkeletonKernel (terminalOuterBoundary scale x)
          (code.2.1 j) (code.2.2 j) := by
  rw [hevent, ← validUnmarkedComplementarySkeletonAtom_event
    (start := start) code hscale hvalid]
  exact fairSteps_event_eq_weight_mul_canonical_unmarkedKernel
    (fun _ ↦ terminalOuterBoundary scale x) code.2.1 code.2.2
    (validUnmarkedComplementarySkeletonAtom (start := start)
      code hscale hvalid)
    (validUnmarkedComplementarySkeletonAtom_bridgeWord code hscale hvalid)

/-- The target centre is not on its terminal outer boundary once the scale
is at least two. -/
theorem center_not_mem_terminalOuterBoundary
    (scale : ℕ) (x : Point) (hscale : 2 ≤ scale) :
    x ∉ terminalOuterBoundary scale x := by
  intro hx
  have hzero : (0 : Point) ∈
      ThickPoint.discBoundary 0 ((scale ^ 9 : ℕ) : ℝ) := by
    simpa only [sub_self] using
      (BoundaryStoppedHarnack.mem_discBoundary_translate
        x ((scale ^ 9 : ℕ) : ℝ) x).mp
        (by simpa [terminalOuterBoundary, ThickPoint.scaleRadius_of_le,
          ThickPoint.regularRadius_self] using hx)
  have hlower :=
    (BoundaryStoppedHarnack.discBoundary_zero_euclideanRadius_bounds_nat
      (Nat.one_le_pow 9 scale (by omega)) hzero).1
  have hradius : PotentialEuclideanGeometry.euclideanRadius (0 : Point) = 0 := by
    simp [PotentialEuclideanGeometry.euclideanRadius,
      PotentialEuclideanGeometry.euclideanRadiusSq]
  rw [hradius] at hlower
  have hnonneg : (0 : ℝ) ≤ (scale ^ 9 - 1 : ℕ) := by positivity
  linarith

/-- Exact fixed-visit marked mass factorization, retaining the prescribed
outer endpoint at every coordinate. -/
theorem fairSteps_stoppedMarkedTerminalAtom_eq_weight_mul
    {start scale : ℕ} {profileDelta : ℝ} {x : Point}
    (code : TerminalSkeletonCode (terminalCount scale profileDelta))
    (visits : Fin (terminalCount scale profileDelta) → ℕ)
    (hscale : 2 ≤ scale)
    (hvalid : ValidTerminalSkeleton scale profileDelta x code)
    (hevent : stoppedMarkedTerminalAtom start scale profileDelta x
        (code.1, (code.2.1, (code.2.2, visits))) =
      markedTerminalInsertionEvent (start := start) (scale := scale)
        (x := x) code visits) :
    fairSteps (stoppedMarkedTerminalAtom start scale profileDelta x
        (code.1, (code.2.1, (code.2.2, visits)))) =
      (validUnmarkedComplementarySkeletonAtom (start := start)
        code (by omega : 1 ≤ scale) hvalid).weight *
        ∏ j, terminalMarkedKernel (terminalOuterBoundary scale x) x
          (code.2.1 j) (visits j) (code.2.2 j) := by
  rw [hevent, ← validMarkedComplementarySkeletonAtom_event
    (start := start) code (by omega) hvalid visits]
  rw [fairSteps_event_eq_weight_mul_canonical_markedKernel
    (fun _ ↦ terminalOuterBoundary scale x) (fun _ ↦ x)
    code.2.1 code.2.2 visits
    (fun _ ↦ center_not_mem_terminalOuterBoundary scale x hscale)
    (validMarkedComplementarySkeletonAtom (start := start)
      code (by omega) hvalid visits)
    (validMarkedComplementarySkeletonAtom_bridgeWord
      code (by omega) hvalid visits)]
  rw [validMarkedComplementarySkeletonAtom_weight_eq_unmarked]
  rfl

/-- Supported unmarked atom mass, with the invalid-code branch discharged
internally. -/
theorem fairSteps_terminalSkeletonAtom_eq_weight_mul
    {start scale : ℕ} {profileDelta : ℝ} {x : Point}
    (hscale : 1 ≤ scale)
    (data : TerminalSkeletonData (terminalCount scale profileDelta))
    (entrance : Fin (terminalCount scale profileDelta) →
      TerminalEntrance scale x)
    (exit : Fin (terminalCount scale profileDelta) →
      TerminalExit scale x)
    (hevent : ∀ hvalid : ValidTerminalSkeleton scale profileDelta x
        (rawSupportedTerminalCode data entrance exit),
      stoppedTerminalSkeletonAtom start scale profileDelta x
          (rawSupportedTerminalCode data entrance exit) =
        unmarkedTerminalInsertionEvent (start := start) (scale := scale)
          (x := x) (rawSupportedTerminalCode data entrance exit)) :
    fairSteps (terminalSkeletonAtom start scale profileDelta x
        data entrance exit) =
      terminalSkeletonWeight start scale profileDelta x hscale
          data entrance exit *
        skeletonProduct
          (supportedTerminalSkeletonKernel
            (profileDelta := profileDelta) scale x) entrance exit := by
  let code := rawSupportedTerminalCode data entrance exit
  by_cases hvalid : ValidTerminalSkeleton scale profileDelta x code
  · have hmass := fairSteps_stoppedTerminalSkeletonAtom_eq_weight_mul
      code hscale hvalid (hevent hvalid)
    change fairSteps (stoppedTerminalSkeletonAtom start scale profileDelta x code) = _
    rw [terminalSkeletonWeight, dif_pos hvalid]
    simpa [skeletonProduct, supportedTerminalSkeletonKernel,
      terminalSkeletonKernel, code, rawSupportedTerminalCode,
      eraseSupportedSkeletonIndex] using hmass
  · have hempty := stoppedTerminalSkeletonAtom_eq_empty_of_not_valid
      (start := start) (scale := scale) (profileDelta := profileDelta)
      (x := x) hvalid
    change fairSteps (stoppedTerminalSkeletonAtom start scale profileDelta x code) = _
    rw [hempty]
    simp [terminalSkeletonWeight, code, hvalid]

/-- Supported marked atom mass with the same retained weight as the unmarked
atom, again including the invalid-code branch. -/
theorem fairSteps_terminalMarkedAtom_eq_weight_mul
    {start scale : ℕ} {profileDelta : ℝ} {x : Point}
    (hscale : 2 ≤ scale)
    (data : TerminalSkeletonData (terminalCount scale profileDelta))
    (entrance : Fin (terminalCount scale profileDelta) →
      TerminalEntrance scale x)
    (exit : Fin (terminalCount scale profileDelta) →
      TerminalExit scale x)
    (visits : Fin (terminalCount scale profileDelta) → ℕ)
    (hevent : ∀ hvalid : ValidTerminalSkeleton scale profileDelta x
        (rawSupportedTerminalCode data entrance exit),
      stoppedMarkedTerminalAtom start scale profileDelta x
          ((rawSupportedTerminalCode data entrance exit).1,
            ((rawSupportedTerminalCode data entrance exit).2.1,
              ((rawSupportedTerminalCode data entrance exit).2.2, visits))) =
        markedTerminalInsertionEvent (start := start) (scale := scale)
          (x := x) (rawSupportedTerminalCode data entrance exit) visits) :
    fairSteps (terminalMarkedAtom start scale profileDelta x
        data entrance exit visits) =
      terminalSkeletonWeight start scale profileDelta x (by omega)
          data entrance exit *
        markedProduct
          (supportedTerminalMarkedKernel
            (profileDelta := profileDelta) scale x) entrance exit visits := by
  let code := rawSupportedTerminalCode data entrance exit
  by_cases hvalid : ValidTerminalSkeleton scale profileDelta x code
  · have hmass := fairSteps_stoppedMarkedTerminalAtom_eq_weight_mul
      code visits hscale hvalid (hevent hvalid)
    have hentrance : code.2.1 = fun j ↦ (entrance j).1 := by
      rfl
    have hexit : code.2.2 = fun j ↦ (exit j).1 := by
      rfl
    rw [hentrance, hexit] at hmass
    change fairSteps (stoppedMarkedTerminalAtom start scale profileDelta x
      (code.1, (code.2.1, (code.2.2, visits)))) = _
    rw [hentrance, hexit]
    rw [terminalSkeletonWeight, dif_pos hvalid]
    simpa [markedProduct, supportedTerminalMarkedKernel,
      terminalMarkedKernel, code, rawSupportedTerminalCode,
      eraseSupportedMarkedIndex] using hmass
  · have hempty := stoppedMarkedTerminalAtom_eq_empty_of_not_valid
      (start := start) (scale := scale) (profileDelta := profileDelta)
      (x := x)
      (code := (code.1, (code.2.1, (code.2.2, visits))))
      (by simpa only [forgetTerminalVisits] using hvalid)
    change fairSteps (stoppedMarkedTerminalAtom start scale profileDelta x
      (code.1, (code.2.1, (code.2.2, visits)))) = _
    rw [hempty]
    simp [terminalSkeletonWeight, code, hvalid]

/-- Assemble the two literal insertion-event identifications into the exact
stopped-data decomposition.  This theorem is deliberately event-level: the
only premises are pathwise equalities, not assumed measure products. -/
theorem markedStoppedDataLowerDecomposition_of_terminal_insertion_events
    (start scale : ℕ) (profileDelta thickDelta : ℝ) (x : Point)
    (hscale : 2 ≤ scale)
    (hunmarked : ∀
      (data : TerminalSkeletonData (terminalCount scale profileDelta))
      (entrance : Fin (terminalCount scale profileDelta) →
        TerminalEntrance scale x)
      (exit : Fin (terminalCount scale profileDelta) →
        TerminalExit scale x)
      (hvalid : ValidTerminalSkeleton scale profileDelta x
        (rawSupportedTerminalCode data entrance exit)),
      stoppedTerminalSkeletonAtom start scale profileDelta x
          (rawSupportedTerminalCode data entrance exit) =
        unmarkedTerminalInsertionEvent (start := start) (scale := scale)
          (x := x) (rawSupportedTerminalCode data entrance exit))
    (hmarked : ∀
      (data : TerminalSkeletonData (terminalCount scale profileDelta))
      (entrance : Fin (terminalCount scale profileDelta) →
        TerminalEntrance scale x)
      (exit : Fin (terminalCount scale profileDelta) →
        TerminalExit scale x)
      (visits : Fin (terminalCount scale profileDelta) → ℕ)
      (hvalid : ValidTerminalSkeleton scale profileDelta x
        (rawSupportedTerminalCode data entrance exit)),
      stoppedMarkedTerminalAtom start scale profileDelta x
          ((rawSupportedTerminalCode data entrance exit).1,
            ((rawSupportedTerminalCode data entrance exit).2.1,
              ((rawSupportedTerminalCode data entrance exit).2.2, visits))) =
        markedTerminalInsertionEvent (start := start) (scale := scale)
          (x := x) (rawSupportedTerminalCode data entrance exit) visits) :
    MarkedStoppedDataLowerDecomposition fairSteps
      (stoppedSuccessfulPointEvent start scale profileDelta x)
      (stoppedThickPointEvent start scale profileDelta thickDelta x)
      (terminalSkeletonWeight start scale profileDelta x (by omega))
      (supportedTerminalSkeletonKernel (profileDelta := profileDelta) scale x)
      (supportedTerminalMarkedKernel (profileDelta := profileDelta) scale x)
      (terminalVisitEvent scale thickDelta (terminalCount scale profileDelta)) := by
  apply markedStoppedDataLowerDecomposition_of_terminal_atom_masses
    start scale profileDelta thickDelta x (by omega)
    (terminalSkeletonWeight start scale profileDelta x (by omega))
  · intro data entrance exit
    exact fairSteps_terminalSkeletonAtom_eq_weight_mul
      (by omega) data entrance exit (hunmarked data entrance exit)
  · intro data entrance exit visits
    exact fairSteps_terminalMarkedAtom_eq_weight_mul hscale
      data entrance exit visits (hmarked data entrance exit visits)

/-- The literal stopped successful/thick events have the canonical marked
full-skeleton disintegration.  The witness retains the complete complementary
word (including the pre-`start` prefix), while the deleted terminal pieces are
represented by their joint entrance/visit/exit kernels. -/
theorem exists_terminalMarkedStoppedDataLowerDecomposition
    (start scale : ℕ) (profileDelta thickDelta : ℝ) (x : Point)
    (hscale : 2 ≤ scale) :
    ∃ skeletonWeight :
        TerminalSkeletonData (terminalCount scale profileDelta) →
          (Fin (terminalCount scale profileDelta) → TerminalEntrance scale x) →
          (Fin (terminalCount scale profileDelta) → TerminalExit scale x) → ℝ≥0∞,
      MarkedStoppedDataLowerDecomposition fairSteps
        (stoppedSuccessfulPointEvent start scale profileDelta x)
        (stoppedThickPointEvent start scale profileDelta thickDelta x)
        skeletonWeight
        (supportedTerminalSkeletonKernel (profileDelta := profileDelta) scale x)
        (supportedTerminalMarkedKernel (profileDelta := profileDelta) scale x)
        (terminalVisitEvent scale thickDelta
          (terminalCount scale profileDelta)) := by
  refine ⟨terminalSkeletonWeight start scale profileDelta x (by omega), ?_⟩
  apply markedStoppedDataLowerDecomposition_of_terminal_insertion_events
    start scale profileDelta thickDelta x hscale
  · intro data entrance exit hvalid
    exact stoppedTerminalSkeletonAtom_eq_unmarkedTerminalInsertionEvent
      (by omega) (rawSupportedTerminalCode data entrance exit) hvalid
  · intro data entrance exit visits hvalid
    exact stoppedMarkedTerminalAtom_eq_markedTerminalInsertionEvent
      (by omega) (rawSupportedTerminalCode data entrance exit) hvalid visits

end

end Erdos1165.TerminalMarkedSkeletonMass
