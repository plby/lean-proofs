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

import ErdosProblems.Erdos1165.MarkedBoundaryVisitKernel
import ErdosProblems.Erdos1165.TerminalSkeletonWords

/-!
# Literal terminal marked-skeleton decomposition

The endpoint coordinates in this file are boundary subtypes.  Consequently
the local marked Harnack theorem is asked only about genuine inner-boundary
entrances and outer-boundary exit marks.  The complete complementary word
data remains in `TerminalSkeletonData`; it is never discarded or asserted to
be measurable at an earlier entrance time.

This file first proves the event partition and the one-sided thick-event
containment.  The final constructor isolates only the two exact atom-mass
identities supplied by the literal stopped-word insertion factorization.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace Erdos1165.TerminalMarkedSkeletonDecomposition

open ThickPoint Proposition13Measurability TerminalExcursionPathwise
open TerminalSkeletonWords MarkedSkeletonPartition
open MarkedTerminalDisintegration MarkedBoundaryVisitKernel

noncomputable section

abbrev terminalCount (scale : ℕ) (profileDelta : ℝ) :=
  AppendixLocalTime.requiredTerminalCount scale profileDelta

abbrev SupportedSkeletonIndex (scale : ℕ) (profileDelta : ℝ)
    (x : Point) :=
  SkeletonIndex (TerminalSkeletonData (terminalCount scale profileDelta))
    (TerminalEntrance scale x) (TerminalExit scale x)
    (terminalCount scale profileDelta)

abbrev SupportedMarkedIndex (scale : ℕ) (profileDelta : ℝ)
    (x : Point) :=
  MarkedIndex (TerminalSkeletonData (terminalCount scale profileDelta))
    (TerminalEntrance scale x) (TerminalExit scale x)
    (terminalCount scale profileDelta)

/-- Forget only the boundary-membership proofs in a supported skeleton code. -/
def eraseSupportedSkeletonIndex
    {scale : ℕ} {profileDelta : ℝ} {x : Point} :
    SupportedSkeletonIndex scale profileDelta x →
      TerminalSkeletonCode (terminalCount scale profileDelta)
  | (data, (entrance, exit)) =>
      (data, ((fun j ↦ (entrance j).1), fun j ↦ (exit j).1))

/-- Forget boundary-membership proofs and retain the visit vector. -/
def eraseSupportedMarkedIndex
    {scale : ℕ} {profileDelta : ℝ} {x : Point} :
    SupportedMarkedIndex scale profileDelta x →
      MarkedIndex (TerminalSkeletonData (terminalCount scale profileDelta))
        Point Point (terminalCount scale profileDelta)
  | (data, (entrance, (exit, visits))) =>
      (data, ((fun j ↦ (entrance j).1),
        ((fun j ↦ (exit j).1), visits)))

theorem eraseSupportedSkeletonIndex_injective
    {scale : ℕ} {profileDelta : ℝ} {x : Point} :
    Function.Injective
      (eraseSupportedSkeletonIndex (scale := scale)
        (profileDelta := profileDelta) (x := x)) := by
  rintro ⟨data, entrance, exit⟩ ⟨data', entrance', exit'⟩ h
  simp only [eraseSupportedSkeletonIndex, Prod.mk.injEq] at h
  rcases h with ⟨rfl, hentrance, hexit⟩
  have hu : entrance = entrance' := by
    funext j
    exact Subtype.ext (congrFun hentrance j)
  have hz : exit = exit' := by
    funext j
    exact Subtype.ext (congrFun hexit j)
  simp only [hu, hz]

theorem eraseSupportedMarkedIndex_injective
    {scale : ℕ} {profileDelta : ℝ} {x : Point} :
    Function.Injective
      (eraseSupportedMarkedIndex (scale := scale)
        (profileDelta := profileDelta) (x := x)) := by
  rintro ⟨data, entrance, exit, visits⟩
    ⟨data', entrance', exit', visits'⟩ h
  simp only [eraseSupportedMarkedIndex, Prod.mk.injEq] at h
  rcases h with ⟨rfl, hentrance, hexit, rfl⟩
  have hu : entrance = entrance' := by
    funext j
    exact Subtype.ext (congrFun hentrance j)
  have hz : exit = exit' := by
    funext j
    exact Subtype.ext (congrFun hexit j)
  simp only [hu, hz]

/-- The literal successful skeleton atom indexed only by supported endpoint
vectors. -/
def terminalSkeletonAtom (start scale : ℕ) (profileDelta : ℝ)
    (x : Point)
    (data : TerminalSkeletonData (terminalCount scale profileDelta))
    (entrance : Fin (terminalCount scale profileDelta) →
      TerminalEntrance scale x)
    (exit : Fin (terminalCount scale profileDelta) →
      TerminalExit scale x) : Set StepPath :=
  stoppedTerminalSkeletonAtom start scale profileDelta x
    (eraseSupportedSkeletonIndex (data, (entrance, exit)))

/-- The same complete skeleton atom with the terminal visit vector exposed. -/
def terminalMarkedAtom (start scale : ℕ) (profileDelta : ℝ)
    (x : Point)
    (data : TerminalSkeletonData (terminalCount scale profileDelta))
    (entrance : Fin (terminalCount scale profileDelta) →
      TerminalEntrance scale x)
    (exit : Fin (terminalCount scale profileDelta) →
      TerminalExit scale x)
    (visits : Fin (terminalCount scale profileDelta) → ℕ) : Set StepPath :=
  stoppedMarkedTerminalAtom start scale profileDelta x
    (eraseSupportedMarkedIndex (data, (entrance, (exit, visits))))

theorem measurableSet_terminalSkeletonAtom
    (start scale : ℕ) (profileDelta : ℝ) (x : Point)
    (data : TerminalSkeletonData (terminalCount scale profileDelta))
    (entrance : Fin (terminalCount scale profileDelta) →
      TerminalEntrance scale x)
    (exit : Fin (terminalCount scale profileDelta) →
      TerminalExit scale x) :
    MeasurableSet
      (terminalSkeletonAtom start scale profileDelta x data entrance exit) :=
  measurableSet_stoppedTerminalSkeletonAtom _ _ _ _ _

theorem measurableSet_terminalMarkedAtom
    (start scale : ℕ) (profileDelta : ℝ) (x : Point)
    (data : TerminalSkeletonData (terminalCount scale profileDelta))
    (entrance : Fin (terminalCount scale profileDelta) →
      TerminalEntrance scale x)
    (exit : Fin (terminalCount scale profileDelta) →
      TerminalExit scale x)
    (visits : Fin (terminalCount scale profileDelta) → ℕ) :
    MeasurableSet
      (terminalMarkedAtom start scale profileDelta x data entrance exit visits) :=
  measurableSet_stoppedMarkedTerminalAtom _ _ _ _ _

theorem terminalSkeletonAtom_pairwise
    (start scale : ℕ) (profileDelta : ℝ) (x : Point) :
    Pairwise fun i j : SupportedSkeletonIndex scale profileDelta x ↦
      Disjoint
        (indexedSkeletonAtom
          (terminalSkeletonAtom start scale profileDelta x) i)
        (indexedSkeletonAtom
          (terminalSkeletonAtom start scale profileDelta x) j) := by
  intro i j hij
  apply stoppedTerminalSkeletonAtom_disjoint_of_ne
  exact fun h ↦ hij (eraseSupportedSkeletonIndex_injective h)

theorem terminalMarkedAtom_pairwise
    (start scale : ℕ) (profileDelta : ℝ) (x : Point) :
    Pairwise fun i j : SupportedMarkedIndex scale profileDelta x ↦
      Disjoint
        (indexedMarkedAtom
          (terminalMarkedAtom start scale profileDelta x) i)
        (indexedMarkedAtom
          (terminalMarkedAtom start scale profileDelta x) j) := by
  intro i j hij
  apply stoppedMarkedTerminalAtom_disjoint_of_ne
  exact fun h ↦ hij (eraseSupportedMarkedIndex_injective h)

/-- Every stopped successful path has supported endpoint marks, and hence
belongs to exactly one supported complete skeleton atom. -/
theorem stoppedSuccessfulPointEvent_eq_iUnion_supportedSkeletonAtoms
    (start scale : ℕ) (profileDelta : ℝ) (x : Point)
    (hscale : 1 ≤ scale) :
    stoppedSuccessfulPointEvent start scale profileDelta x =
      ⋃ i : SupportedSkeletonIndex scale profileDelta x,
        indexedSkeletonAtom
          (terminalSkeletonAtom start scale profileDelta x) i := by
  ext omega
  constructor
  · rintro ⟨horizon, hexit, hx⟩
    let raw := extractTerminalSkeletonCode scale horizon profileDelta x
      (shiftSteps start omega)
    let supported := extractSupportedTerminalSkeletonCode hscale hexit hx
    refine Set.mem_iUnion.mpr ⟨supported, ?_⟩
    change omega ∈ stoppedTerminalSkeletonAtom start scale profileDelta x
      (eraseSupportedSkeletonIndex supported)
    apply Set.mem_iUnion.mpr
    refine ⟨horizon, ⟨hexit, hx⟩, ?_⟩
    change raw = eraseSupportedSkeletonIndex supported
    rfl
  · intro homega
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp homega
    change omega ∈ stoppedTerminalSkeletonAtom start scale profileDelta x
      (eraseSupportedSkeletonIndex i) at hi
    obtain ⟨horizon, hatom⟩ := Set.mem_iUnion.mp hi
    exact ⟨horizon, hatom.1⟩

/-- Visit vectors whose selected terminal pieces already force the desired
thick local-time threshold. -/
def terminalVisitEvent (scale : ℕ) (thickDelta : ℝ)
    (m : ℕ) : Set (Fin m → ℕ) :=
  {visits | thickThreshold scale thickDelta ≤
    AppendixLocalTime.totalVisits visits}

/-- The selected marked atoms are a literal subevent of stopped thick
success.  This is the one-sided direction used in the lower bound. -/
theorem restrictedTerminalMarkedAtoms_subset_stoppedThickPointEvent
    (start scale : ℕ) (profileDelta thickDelta : ℝ) (x : Point) :
    (⋃ i : SupportedMarkedIndex scale profileDelta x,
      restrictedMarkedAtom
        (terminalVisitEvent scale thickDelta (terminalCount scale profileDelta))
        (terminalMarkedAtom start scale profileDelta x) i) ⊆
      stoppedThickPointEvent start scale profileDelta thickDelta x := by
  intro omega homega
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp homega
  by_cases hvisits : i.2.2.2 ∈
      terminalVisitEvent scale thickDelta (terminalCount scale profileDelta)
  · rw [restrictedMarkedAtom, if_pos hvisits] at hi
    change omega ∈ stoppedMarkedTerminalAtom start scale profileDelta x
      (eraseSupportedMarkedIndex i) at hi
    obtain ⟨horizon, hatom⟩ := Set.mem_iUnion.mp hi
    have hvector : terminalVisitVector (shiftedWalk start omega) scale horizon
        profileDelta x = i.2.2.2 := by
      have h := congrArg (fun code ↦ code.2.2.2) hatom.2
      simpa only [extractMarkedTerminalCode,
        Proposition13Measurability.shiftedWalk,
        eraseSupportedMarkedIndex] using h
    refine ⟨horizon, hatom.1.1, ?_⟩
    apply thickSuccessfulPoint_of_terminalExcursionVisits hatom.1.2
    simpa only [terminalVisitEvent, Set.mem_ofPred_eq, hvector] using hvisits
  · rw [restrictedMarkedAtom, if_neg hvisits] at hi
    exact hi.elim

/-- Canonical unmarked endpoint kernel on the boundary-supported types. -/
def supportedTerminalSkeletonKernel {profileDelta : ℝ} (scale : ℕ) (x : Point)
    (_j : Fin (terminalCount scale profileDelta))
    (entrance : TerminalEntrance scale x) (exit : TerminalExit scale x) : ℝ≥0∞ :=
  terminalSkeletonKernel (terminalOuterBoundary scale x) entrance.1 exit.1

/-- Canonical joint visit-count/endpoint kernel on supported types. -/
def supportedTerminalMarkedKernel {profileDelta : ℝ} (scale : ℕ) (x : Point)
    (_j : Fin (terminalCount scale profileDelta))
    (entrance : TerminalEntrance scale x) (visits : ℕ)
    (exit : TerminalExit scale x) : ℝ≥0∞ :=
  terminalMarkedKernel (terminalOuterBoundary scale x) x entrance.1 visits exit.1

/-- Exact event-level disintegration after the two literal stopped-word mass
factorizations have been supplied.  No stopped-past measurability of success
and no entrance-only conditional product law occurs in this interface. -/
theorem markedStoppedDataLowerDecomposition_of_terminal_atom_masses
    (start scale : ℕ) (profileDelta thickDelta : ℝ) (x : Point)
    (hscale : 1 ≤ scale)
    (skeletonWeight : TerminalSkeletonData (terminalCount scale profileDelta) →
      (Fin (terminalCount scale profileDelta) → TerminalEntrance scale x) →
      (Fin (terminalCount scale profileDelta) → TerminalExit scale x) →
        ℝ≥0∞)
    (hskeleton_mass : ∀ data entrance exit,
      fairSteps (terminalSkeletonAtom start scale profileDelta x
          data entrance exit) =
        skeletonWeight data entrance exit *
          skeletonProduct
            (supportedTerminalSkeletonKernel
              (profileDelta := profileDelta) scale x)
            entrance exit)
    (hmarked_mass : ∀ data entrance exit visits,
      fairSteps (terminalMarkedAtom start scale profileDelta x
          data entrance exit visits) =
        skeletonWeight data entrance exit *
          markedProduct
            (supportedTerminalMarkedKernel
              (profileDelta := profileDelta) scale x)
            entrance exit visits) :
    MarkedStoppedDataLowerDecomposition fairSteps
      (stoppedSuccessfulPointEvent start scale profileDelta x)
      (stoppedThickPointEvent start scale profileDelta thickDelta x)
      skeletonWeight
      (supportedTerminalSkeletonKernel (profileDelta := profileDelta) scale x)
      (supportedTerminalMarkedKernel (profileDelta := profileDelta) scale x)
      (terminalVisitEvent scale thickDelta (terminalCount scale profileDelta)) := by
  apply markedStoppedDataLowerDecomposition_of_atom_partition fairSteps
    (stoppedSuccessfulPointEvent start scale profileDelta x)
    (stoppedThickPointEvent start scale profileDelta thickDelta x)
    skeletonWeight
    (supportedTerminalSkeletonKernel (profileDelta := profileDelta) scale x)
    (supportedTerminalMarkedKernel (profileDelta := profileDelta) scale x)
    (terminalVisitEvent scale thickDelta (terminalCount scale profileDelta))
    (terminalSkeletonAtom start scale profileDelta x)
    (terminalMarkedAtom start scale profileDelta x)
  · exact measurableSet_terminalSkeletonAtom start scale profileDelta x
  · exact measurableSet_terminalMarkedAtom start scale profileDelta x
  · exact terminalSkeletonAtom_pairwise start scale profileDelta x
  · exact terminalMarkedAtom_pairwise start scale profileDelta x
  · exact stoppedSuccessfulPointEvent_eq_iUnion_supportedSkeletonAtoms
      start scale profileDelta x hscale
  · exact restrictedTerminalMarkedAtoms_subset_stoppedThickPointEvent
      start scale profileDelta thickDelta x
  · exact hskeleton_mass
  · exact hmarked_mass

end

end Erdos1165.TerminalMarkedSkeletonDecomposition
