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

import ErdosProblems.Erdos1165.AnnularRadialLabelWord

/-!
# Arbitrary-source chronological radial segments

After a two-point path separates, the replaced radial history starts at the
retained separation boundary rather than at profile level one.  A segment
code stores that arbitrary source, the labels strictly before the final
level-zero hit, nearest-neighbor admissibility, and the absence of an earlier
zero.  Its literal first-zero trace event is exactly the same recursive
random-endpoint chain used by the full radial word.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace Erdos1165.AnnularRadialLabelSegment

open ThickPoint PlanarPotential MarkedBoundaryVisitKernel
open AnnularRadialLabelWord
open TerminalSequentialVisitLaw

noncomputable section

/-- An admissible radial trace beginning at an arbitrary nonzero label and
ending at its first level-zero hit.  `beforeZero` excludes both the source
and the final zero. -/
structure RadialLabelSegmentCode (n : ℕ) where
  source : Fin (n + 2)
  beforeZero : List (Fin (n + 2))
  adjacent : List.IsChain
    (fun left right : Fin (n + 2) ↦ Nat.dist left.val right.val = 1)
    (source :: beforeZero ++ [⟨0, by omega⟩])
  noZeroBeforeFinal :
    (⟨0, by omega⟩ : Fin (n + 2)) ∉ source :: beforeZero

@[ext] theorem RadialLabelSegmentCode.ext {n : ℕ}
    {left right : RadialLabelSegmentCode n}
    (hsource : left.source = right.source)
    (hbefore : left.beforeZero = right.beforeZero) : left = right := by
  cases left
  cases right
  cases hsource
  cases hbefore
  rfl

/-- Complete label list, including the retained source and final zero. -/
def RadialLabelSegmentCode.word {n : ℕ}
    (code : RadialLabelSegmentCode n) : List (Fin (n + 2)) :=
  code.source :: code.beforeZero ++ [⟨0, by omega⟩]

@[simp] theorem RadialLabelSegmentCode.word_ne_nil {n : ℕ}
    (code : RadialLabelSegmentCode n) : code.word ≠ [] := by
  simp [RadialLabelSegmentCode.word]

theorem RadialLabelSegmentCode.source_ne_zero {n : ℕ}
    (code : RadialLabelSegmentCode n) :
    code.source ≠ (⟨0, by omega⟩ : Fin (n + 2)) := by
  intro heq
  apply code.noZeroBeforeFinal
  simp [heq]

theorem RadialLabelSegmentCode.different {n : ℕ}
    (code : RadialLabelSegmentCode n) :
    List.IsChain (fun left right : Fin (n + 2) ↦ left ≠ right)
      code.word := by
  exact code.adjacent.imp (by
    intro left right hdist heq
    subst right
    simp at hdist)

/-- Literal stopped event: the path first hits level zero at `horizon`, and
its compressed chronological radial trace is exactly the coded word. -/
def radialLabelSegmentAtom {n : ℕ} (center start : Point)
    (code : RadialLabelSegmentCode n) : Set StepPath :=
  {omega | ∃ horizon : ℕ,
    AbsoluteBoundaryFirstAt
      (radialBoundary n center ⟨0, by omega⟩) start omega horizon ∧
    chronologicalRadialLabels n center
      (fun r ↦ trajectoryFrom start omega r) horizon = code.word}

/-- Recursive random-endpoint chain event for the same arbitrary-source
segment. -/
def radialLabelSegmentChainAtom {n : ℕ} (center start : Point)
    (code : RadialLabelSegmentCode n) : Set StepPath :=
  radialChainAtom n center code.source
    (code.beforeZero ++ [⟨0, by omega⟩]) start

/-- Endpoint-summed Strong-Markov kernel of the segment. -/
def radialLabelSegmentKernelENNReal {n : ℕ} (center start : Point)
    (code : RadialLabelSegmentCode n) : ℝ≥0∞ :=
  radialChainKernelENNReal n center code.source
    (code.beforeZero ++ [⟨0, by omega⟩]) start

/-- The recursive chain atom is exactly the literal arbitrary-source
first-zero trace atom. -/
theorem radialLabelSegmentChainAtom_eq_atom
    {n : ℕ} (hn : 2 ≤ n) (center start : Point)
    (code : RadialLabelSegmentCode n)
    (hstart : start ∈ radialBoundary n center code.source) :
    radialLabelSegmentChainAtom center start code =
      radialLabelSegmentAtom center start code := by
  unfold radialLabelSegmentChainAtom radialLabelSegmentAtom
    RadialLabelSegmentCode.word
  exact radialChainAtom_eq_firstZeroTraceEvent
    hn center start code.source code.beforeZero
      code.different code.noZeroBeforeFinal hstart

/-- Exact probability of an arbitrary-source literal segment. -/
theorem fairSteps_radialLabelSegmentAtom
    {n : ℕ} (hn : 2 ≤ n) (center start : Point)
    (code : RadialLabelSegmentCode n)
    (hstart : start ∈ radialBoundary n center code.source) :
    fairSteps (radialLabelSegmentAtom center start code) =
      radialLabelSegmentKernelENNReal center start code := by
  rw [← radialLabelSegmentChainAtom_eq_atom hn center start code hstart]
  exact fairSteps_radialChainAtom n center code.source
    (code.beforeZero ++ [⟨0, by omega⟩]) start

theorem measurableSet_radialLabelSegmentAtom
    {n : ℕ} (hn : 2 ≤ n) (center start : Point)
    (code : RadialLabelSegmentCode n)
    (hstart : start ∈ radialBoundary n center code.source) :
    MeasurableSet (radialLabelSegmentAtom center start code) := by
  rw [← radialLabelSegmentChainAtom_eq_atom hn center start code hstart]
  exact measurableSet_radialChainAtom n center code.source
    (code.beforeZero ++ [⟨0, by omega⟩]) start

/-- Distinct stopped label words define disjoint literal events. -/
theorem disjoint_radialLabelSegmentAtom_of_word_ne
    {n : ℕ} (center start : Point)
    {left right : RadialLabelSegmentCode n}
    (hne : left.word ≠ right.word) :
    Disjoint (radialLabelSegmentAtom center start left)
      (radialLabelSegmentAtom center start right) := by
  rw [Set.disjoint_left]
  intro omega hleft hright
  obtain ⟨leftHorizon, leftFirst, leftTrace⟩ := hleft
  obtain ⟨rightHorizon, rightFirst, rightTrace⟩ := hright
  have htime : leftHorizon = rightHorizon := by
    rcases lt_trichotomy leftHorizon rightHorizon with hlt | heq | hgt
    · exact (rightFirst.2 leftHorizon hlt leftFirst.1).elim
    · exact heq
    · exact (leftFirst.2 rightHorizon hgt rightFirst.1).elim
  apply hne
  rw [← leftTrace, ← rightTrace, htime]

/-- The coded scanner count at a positive level. -/
def radialLabelSegmentCompletedCount {n : ℕ}
    (code : RadialLabelSegmentCode n) (k : ℕ) : ℕ :=
  (scanRadialLabels k code.word).completed

/-- On every realization, the literal alternating-clock count through the
stopping horizon is exactly the count read from the coded label word. -/
theorem radialLabelSegmentCompletedCount_eq_literal_of_mem
    {n k : ℕ} (hn : 2 ≤ n) (hkpos : 0 < k) (hk : k < n + 2)
    (center start : Point) (code : RadialLabelSegmentCode n)
    (omega : StepPath) (homega : omega ∈ radialLabelSegmentAtom center start code) :
    ∃ horizon : ℕ,
      AbsoluteBoundaryFirstAt
        (radialBoundary n center ⟨0, by omega⟩) start omega horizon ∧
      radialCompletedExcursionCount n center k
          (fun r ↦ trajectoryFrom start omega r) horizon =
        radialLabelSegmentCompletedCount code k := by
  obtain ⟨horizon, hfirst, htrace⟩ := homega
  refine ⟨horizon, hfirst, ?_⟩
  unfold radialLabelSegmentCompletedCount
  have hcount := chronologicalRadialLabels_completed_eq_completedExcursionCount
    hn hkpos hk center (fun r ↦ trajectoryFrom start omega r) horizon
  rw [htrace] at hcount
  exact hcount.symm

end

end Erdos1165.AnnularRadialLabelSegment
