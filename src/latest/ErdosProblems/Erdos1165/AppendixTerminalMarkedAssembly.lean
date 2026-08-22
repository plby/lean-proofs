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

import ErdosProblems.Erdos1165.AppendixTerminalThick
import ErdosProblems.Erdos1165.TerminalMarkedSkeletonDecomposition
import ErdosProblems.Erdos1165.TerminalParameterBounds
import ErdosProblems.Erdos1165.PoissonKernelMarkedHarnack
import ErdosProblems.Erdos1165.TerminalMarkedParameterBounds
import ErdosProblems.Erdos1165.TerminalMarkedSkeletonMass

/-!
# Literal marked-skeleton assembly for Appendix A.7

This file removes the abstract data and endpoint types from the terminal
local-time adapter.  Its inputs are the two exact atom-mass factorizations
for the literal stopped successful event and the pointwise lower comparison
for the canonical joint visit-count/next-exit kernel.  The entire retained
outer-to-inner skeleton remains in `skeletonWeight`.

In particular, the theorem below does not condition the future-dependent
successful event at an earlier terminal entrance.  It is the direct adapter
from the stopped-word insertion factorization to
`Proposition13Scales.AnnularComparisons.terminalThick`.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Erdos1165.AppendixTerminalMarkedAssembly

open AppendixLocalTime AppendixTerminalThick MarkedTerminalDisintegration
open Proposition13Assembly Proposition13Scales
open TerminalMarkedSkeletonDecomposition TerminalSkeletonWords
open TerminalParameterBounds
open PoissonKernelMarkedHarnack
open TerminalMarkedParameterBounds
open TerminalMarkedSkeletonMass

noncomputable section

/-- Assemble the literal all-terminal-excursion marked decomposition into
the exact terminal-thickness field.  The two mass identities are precisely
the remaining pathwise stopped-word insertion facts; all count-vector
summation and concentration have already been discharged by the imported
adapters. -/
theorem annularComparisons_terminalThick_of_terminal_atom_masses
    {delta : ℝ} {n : ℕ}
    (hscale : 4 ≤ scaleIndex delta n)
    (q p eta : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hp0 : 0 < p) (hp1 : p ≤ 1)
    (hmargin : 0 < requiredHLOZTerminalMargin
      (scaleIndex delta n) chosenProfileDelta (chosenThickDelta delta) q p)
    (hratio : requiredTerminalVisitVariance
        (scaleIndex delta n) chosenProfileDelta q p /
      (requiredHLOZTerminalMargin
        (scaleIndex delta n) chosenProfileDelta (chosenThickDelta delta)
          q p) ^ 2 ≤ (scaleIndex delta n : ℝ)⁻¹)
    (heta0 : 0 ≤ eta) (heta1 : eta ≤ 1)
    (hlossQuarter :
      (requiredTerminalCount
          (scaleIndex delta n) chosenProfileDelta : ℝ) * eta ≤ 1 / 4)
    (skeletonWeight : ∀ (_i : Fin (chosenBlockCount delta n)) (x : Point),
      TerminalSkeletonData
          (requiredTerminalCount (scaleIndex delta n) chosenProfileDelta) →
        (Fin (requiredTerminalCount
            (scaleIndex delta n) chosenProfileDelta) →
          TerminalEntrance (scaleIndex delta n) x) →
        (Fin (requiredTerminalCount
            (scaleIndex delta n) chosenProfileDelta) →
          TerminalExit (scaleIndex delta n) x) → ℝ≥0∞)
    (hlower : ∀ (x : Point),
      x ∈ ThickPoint.candidateBox (scaleIndex delta n) →
      MarkedKernelLower
        (fun _ ↦ ENNReal.ofReal (1 - eta))
        (fun _ k ↦ ENNReal.ofReal (visitMass q p k))
        (supportedTerminalSkeletonKernel
          (profileDelta := chosenProfileDelta) (scaleIndex delta n) x)
        (supportedTerminalMarkedKernel
          (profileDelta := chosenProfileDelta) (scaleIndex delta n) x))
    (hskeletonMass : ∀ (i : Fin (chosenBlockCount delta n)) (x : Point),
      x ∈ ThickPoint.candidateBox (scaleIndex delta n) →
      ∀ data entrance exit,
        fairSteps
            (terminalSkeletonAtom
              ((i : ℕ) * chosenBlockLength delta n)
              (scaleIndex delta n) chosenProfileDelta x
              data entrance exit) =
          skeletonWeight i x data entrance exit *
            skeletonProduct
              (supportedTerminalSkeletonKernel
                (profileDelta := chosenProfileDelta)
                (scaleIndex delta n) x)
              entrance exit)
    (hmarkedMass : ∀ (i : Fin (chosenBlockCount delta n)) (x : Point),
      x ∈ ThickPoint.candidateBox (scaleIndex delta n) →
      ∀ data entrance exit visits,
        fairSteps
            (terminalMarkedAtom
              ((i : ℕ) * chosenBlockLength delta n)
              (scaleIndex delta n) chosenProfileDelta x
              data entrance exit visits) =
          skeletonWeight i x data entrance exit *
            markedProduct
              (supportedTerminalMarkedKernel
                (profileDelta := chosenProfileDelta)
                (scaleIndex delta n) x)
              entrance exit visits) :
    ∀ (i : Fin (chosenBlockCount delta n)) (x : Point),
      x ∈ ThickPoint.candidateBox (scaleIndex delta n) →
      (1 - terminalEpsilon) * fairSteps.real
          (stoppedSuccessfulPointEvent
            ((i : ℕ) * chosenBlockLength delta n)
            (scaleIndex delta n) chosenProfileDelta x) ≤
        fairSteps.real
          (stoppedThickPointEvent
            ((i : ℕ) * chosenBlockLength delta n)
            (scaleIndex delta n) chosenProfileDelta
            (chosenThickDelta delta) x) := by
  apply annularComparisons_terminalThick_of_markedStoppedData hscale
    (fun _ _ ↦ TerminalSkeletonData
      (requiredTerminalCount (scaleIndex delta n) chosenProfileDelta))
    (fun _ x ↦ TerminalEntrance (scaleIndex delta n) x)
    (fun _ x ↦ TerminalExit (scaleIndex delta n) x)
    (fun _ _ ↦ q) (fun _ _ ↦ p) (fun _ _ ↦ eta)
    (fun _ _ _ ↦ hq0) (fun _ _ _ ↦ hq1)
    (fun _ _ _ ↦ hp0) (fun _ _ _ ↦ hp1)
    (fun _ _ _ ↦ hmargin) (fun _ _ _ ↦ hratio)
    (fun _ _ _ ↦ heta0) (fun _ _ _ ↦ heta1)
    (fun _ _ _ ↦ hlossQuarter)
    skeletonWeight
    (fun _ x ↦ supportedTerminalSkeletonKernel
      (profileDelta := chosenProfileDelta) (scaleIndex delta n) x)
    (fun _ x ↦ supportedTerminalMarkedKernel
      (profileDelta := chosenProfileDelta) (scaleIndex delta n) x)
    (fun _ x hx ↦ hlower x hx)
  intro i x hx
  exact markedStoppedDataLowerDecomposition_of_terminal_atom_masses
    ((i : ℕ) * chosenBlockLength delta n)
    (scaleIndex delta n) chosenProfileDelta (chosenThickDelta delta) x
    (by omega) (skeletonWeight i x)
    (hskeletonMass i x hx) (hmarkedMass i x hx)

/-- The same literal assembly with all Bernoulli--geometric concentration
hypotheses supplied by the packaged canonical terminal-parameter
certificate.  After this specialization, only the marked Poisson-kernel loss
and the two exact stopped-word atom factorizations remain. -/
theorem annularComparisons_terminalThick_of_parameterCertificate_atom_masses
    {delta : ℝ} {n : ℕ}
    (hparameters : TerminalParameterCertificate delta (scaleIndex delta n))
    (eta : ℝ) (heta0 : 0 ≤ eta) (heta1 : eta ≤ 1)
    (hlossQuarter :
      (requiredTerminalCount
          (scaleIndex delta n) chosenProfileDelta : ℝ) * eta ≤ 1 / 4)
    (skeletonWeight :
      ∀ (_i : Fin (chosenBlockCount delta n)) (x : Point),
        TerminalSkeletonData
            (requiredTerminalCount (scaleIndex delta n) chosenProfileDelta) →
          (Fin (requiredTerminalCount
              (scaleIndex delta n) chosenProfileDelta) →
            TerminalEntrance (scaleIndex delta n) x) →
          (Fin (requiredTerminalCount
              (scaleIndex delta n) chosenProfileDelta) →
            TerminalExit (scaleIndex delta n) x) → ℝ≥0∞)
    (hlower : ∀ (x : Point),
      x ∈ ThickPoint.candidateBox (scaleIndex delta n) →
      MarkedKernelLower
        (fun _ ↦ ENNReal.ofReal (1 - eta))
        (fun _ k ↦ ENNReal.ofReal
          (visitMass
            (terminalHitProbability (scaleIndex delta n))
            (terminalEscapeProbability (scaleIndex delta n)) k))
        (supportedTerminalSkeletonKernel
          (profileDelta := chosenProfileDelta) (scaleIndex delta n) x)
        (supportedTerminalMarkedKernel
          (profileDelta := chosenProfileDelta) (scaleIndex delta n) x))
    (hskeletonMass : ∀ (i : Fin (chosenBlockCount delta n)) (x : Point),
      x ∈ ThickPoint.candidateBox (scaleIndex delta n) →
      ∀ data entrance exit,
        fairSteps
            (terminalSkeletonAtom
              ((i : ℕ) * chosenBlockLength delta n)
              (scaleIndex delta n) chosenProfileDelta x
              data entrance exit) =
          skeletonWeight i x data entrance exit *
            skeletonProduct
              (supportedTerminalSkeletonKernel
                (profileDelta := chosenProfileDelta)
                (scaleIndex delta n) x)
              entrance exit)
    (hmarkedMass : ∀ (i : Fin (chosenBlockCount delta n)) (x : Point),
      x ∈ ThickPoint.candidateBox (scaleIndex delta n) →
      ∀ data entrance exit visits,
        fairSteps
            (terminalMarkedAtom
              ((i : ℕ) * chosenBlockLength delta n)
              (scaleIndex delta n) chosenProfileDelta x
              data entrance exit visits) =
          skeletonWeight i x data entrance exit *
            markedProduct
              (supportedTerminalMarkedKernel
                (profileDelta := chosenProfileDelta)
                (scaleIndex delta n) x)
              entrance exit visits) :
    ∀ (i : Fin (chosenBlockCount delta n)) (x : Point),
      x ∈ ThickPoint.candidateBox (scaleIndex delta n) →
      (1 - terminalEpsilon) * fairSteps.real
          (stoppedSuccessfulPointEvent
            ((i : ℕ) * chosenBlockLength delta n)
            (scaleIndex delta n) chosenProfileDelta x) ≤
        fairSteps.real
          (stoppedThickPointEvent
            ((i : ℕ) * chosenBlockLength delta n)
            (scaleIndex delta n) chosenProfileDelta
            (chosenThickDelta delta) x) := by
  exact annularComparisons_terminalThick_of_terminal_atom_masses
    hparameters.scale_ge_four
    (terminalHitProbability (scaleIndex delta n))
    (terminalEscapeProbability (scaleIndex delta n)) eta
    hparameters.hit_nonneg hparameters.hit_le_one
    hparameters.escape_pos hparameters.escape_le_one
    hparameters.margin_pos hparameters.variance_ratio
    heta0 heta1 hlossQuarter skeletonWeight hlower hskeletonMass hmarkedMass

/-- Existential-decomposition form of the canonical terminal adapter.  This
is the most convenient consumer for the final stopped-word insertion
theorem: the retained skeleton weight is allowed to be constructed
separately for each block and candidate, and is eliminated immediately after
the event-level lower bound is applied. -/
theorem annularComparisons_terminalThick_of_parameterCertificate_decomposition
    {delta : ℝ} {n : ℕ}
    (hparameters : TerminalParameterCertificate delta (scaleIndex delta n))
    (eta : ℝ) (heta0 : 0 ≤ eta) (heta1 : eta ≤ 1)
    (hlossQuarter :
      (requiredTerminalCount
          (scaleIndex delta n) chosenProfileDelta : ℝ) * eta ≤ 1 / 4)
    (hlower : ∀ (x : Point),
      x ∈ ThickPoint.candidateBox (scaleIndex delta n) →
      MarkedKernelLower
        (fun _ ↦ ENNReal.ofReal (1 - eta))
        (fun _ k ↦ ENNReal.ofReal
          (visitMass
            (terminalHitProbability (scaleIndex delta n))
            (terminalEscapeProbability (scaleIndex delta n)) k))
        (supportedTerminalSkeletonKernel
          (profileDelta := chosenProfileDelta) (scaleIndex delta n) x)
        (supportedTerminalMarkedKernel
          (profileDelta := chosenProfileDelta) (scaleIndex delta n) x))
    (hdecompose : ∀ (i : Fin (chosenBlockCount delta n)) (x : Point),
      x ∈ ThickPoint.candidateBox (scaleIndex delta n) →
      ∃ skeletonWeight :
          TerminalSkeletonData
              (requiredTerminalCount
                (scaleIndex delta n) chosenProfileDelta) →
            (Fin (requiredTerminalCount
                (scaleIndex delta n) chosenProfileDelta) →
              TerminalEntrance (scaleIndex delta n) x) →
            (Fin (requiredTerminalCount
                (scaleIndex delta n) chosenProfileDelta) →
              TerminalExit (scaleIndex delta n) x) → ℝ≥0∞,
        MarkedStoppedDataLowerDecomposition fairSteps
          (stoppedSuccessfulPointEvent
            ((i : ℕ) * chosenBlockLength delta n)
            (scaleIndex delta n) chosenProfileDelta x)
          (stoppedThickPointEvent
            ((i : ℕ) * chosenBlockLength delta n)
            (scaleIndex delta n) chosenProfileDelta
            (chosenThickDelta delta) x)
          skeletonWeight
          (supportedTerminalSkeletonKernel
            (profileDelta := chosenProfileDelta) (scaleIndex delta n) x)
          (supportedTerminalMarkedKernel
            (profileDelta := chosenProfileDelta) (scaleIndex delta n) x)
          (terminalVisitEvent (scaleIndex delta n)
            (chosenThickDelta delta)
            (requiredTerminalCount
              (scaleIndex delta n) chosenProfileDelta))) :
    ∀ (i : Fin (chosenBlockCount delta n)) (x : Point),
      x ∈ ThickPoint.candidateBox (scaleIndex delta n) →
      (1 - terminalEpsilon) * fairSteps.real
          (stoppedSuccessfulPointEvent
            ((i : ℕ) * chosenBlockLength delta n)
            (scaleIndex delta n) chosenProfileDelta x) ≤
        fairSteps.real
          (stoppedThickPointEvent
            ((i : ℕ) * chosenBlockLength delta n)
            (scaleIndex delta n) chosenProfileDelta
            (chosenThickDelta delta) x) := by
  intro i x hx
  obtain ⟨skeletonWeight, hdata⟩ := hdecompose i x hx
  have hlowerEvent := event_terminal_half_lower_of_markedStoppedData
    fairSteps
    (stoppedSuccessfulPointEvent
      ((i : ℕ) * chosenBlockLength delta n)
      (scaleIndex delta n) chosenProfileDelta x)
    (stoppedThickPointEvent
      ((i : ℕ) * chosenBlockLength delta n)
      (scaleIndex delta n) chosenProfileDelta
      (chosenThickDelta delta) x)
    hparameters.scale_ge_four chosenProfileDelta (chosenThickDelta delta)
    (terminalHitProbability (scaleIndex delta n))
    (terminalEscapeProbability (scaleIndex delta n))
    hparameters.hit_nonneg hparameters.hit_le_one
    hparameters.escape_pos hparameters.escape_le_one
    hparameters.margin_pos hparameters.variance_ratio
    eta heta0 heta1 hlossQuarter skeletonWeight
    (supportedTerminalSkeletonKernel
      (profileDelta := chosenProfileDelta) (scaleIndex delta n) x)
    (supportedTerminalMarkedKernel
      (profileDelta := chosenProfileDelta) (scaleIndex delta n) x)
    (hlower x hx)
    (by
      simpa only [terminalVisitEvent] using hdata)
  have hterminal : (1 : ℝ) - terminalEpsilon = 1 / 2 := by
    norm_num [terminalEpsilon]
  rw [hterminal]
  exact hlowerEvent

/-- Canonical downstream specialization of the terminal adapter using the
sharp marked Poisson-kernel theorem.  The endpoint Harnack comparison and
the escape/Green normalization are discharged internally; the remaining
analytic inputs are the explicit cut geometry, the two hit-kernel bounds,
and their accumulated loss. -/
theorem annularComparisons_terminalThick_of_markedPoisson_decomposition
    {delta : ℝ} {n : ℕ}
    (hparameters : TerminalParameterCertificate delta (scaleIndex delta n))
    (S : ℕ) (hitError : ℝ)
    (hS : (scaleIndex delta n) ^ 6 + 2 ≤ S)
    (hcutScale : S + 2 * (scaleIndex delta n) ^ 6 + 2 ≤
      (scaleIndex delta n) ^ 9)
    (hcutOuter : S + 4 ≤ (scaleIndex delta n) ^ 9)
    (hgreenLower : 0 < PoissonKernelGreenPole.greenPoleLower
      ((scaleIndex delta n) ^ 9) S ((scaleIndex delta n) ^ 6))
    (hexitError1 : terminalPoissonExitError (scaleIndex delta n) S ≤ 1)
    (hhitError0 : 0 ≤ hitError) (hhitFactor0 : 0 ≤ 1 - hitError)
    (hloss1 : terminalMarkedPoissonLowerError
      (scaleIndex delta n) S hitError ≤ 1)
    (hlossQuarter :
      (requiredTerminalCount
          (scaleIndex delta n) chosenProfileDelta : ℝ) *
        terminalMarkedPoissonLowerError
          (scaleIndex delta n) S hitError ≤ 1 / 4)
    (hhitLower : ∀ (x : Point),
      x ∈ ThickPoint.candidateBox (scaleIndex delta n) →
      ∀ u : TerminalEntrance (scaleIndex delta n) x,
        (1 - hitError) *
            terminalHitProbability (scaleIndex delta n) ≤
          TerminalExcursionDisintegration.boundaryStoppedHitKernel
            (TerminalExcursionPathwise.terminalOuterBoundary
              (scaleIndex delta n) x) x u.1)
    (hhitUpper : ∀ (x : Point),
      x ∈ ThickPoint.candidateBox (scaleIndex delta n) →
      ∀ u : TerminalEntrance (scaleIndex delta n) x,
        TerminalExcursionDisintegration.boundaryStoppedHitKernel
            (TerminalExcursionPathwise.terminalOuterBoundary
              (scaleIndex delta n) x) x u.1 ≤
          (1 + hitError) *
            terminalHitProbability (scaleIndex delta n))
    (hdecompose : ∀ (i : Fin (chosenBlockCount delta n)) (x : Point),
      x ∈ ThickPoint.candidateBox (scaleIndex delta n) →
      ∃ skeletonWeight :
          TerminalSkeletonData
              (requiredTerminalCount
                (scaleIndex delta n) chosenProfileDelta) →
            (Fin (requiredTerminalCount
                (scaleIndex delta n) chosenProfileDelta) →
              TerminalEntrance (scaleIndex delta n) x) →
            (Fin (requiredTerminalCount
                (scaleIndex delta n) chosenProfileDelta) →
              TerminalExit (scaleIndex delta n) x) → ℝ≥0∞,
        MarkedStoppedDataLowerDecomposition fairSteps
          (stoppedSuccessfulPointEvent
            ((i : ℕ) * chosenBlockLength delta n)
            (scaleIndex delta n) chosenProfileDelta x)
          (stoppedThickPointEvent
            ((i : ℕ) * chosenBlockLength delta n)
            (scaleIndex delta n) chosenProfileDelta
            (chosenThickDelta delta) x)
          skeletonWeight
          (supportedTerminalSkeletonKernel
            (profileDelta := chosenProfileDelta) (scaleIndex delta n) x)
          (supportedTerminalMarkedKernel
            (profileDelta := chosenProfileDelta) (scaleIndex delta n) x)
          (terminalVisitEvent (scaleIndex delta n)
            (chosenThickDelta delta)
            (requiredTerminalCount
              (scaleIndex delta n) chosenProfileDelta))) :
    ∀ (i : Fin (chosenBlockCount delta n)) (x : Point),
      x ∈ ThickPoint.candidateBox (scaleIndex delta n) →
      (1 - terminalEpsilon) * fairSteps.real
          (stoppedSuccessfulPointEvent
            ((i : ℕ) * chosenBlockLength delta n)
            (scaleIndex delta n) chosenProfileDelta x) ≤
        fairSteps.real
          (stoppedThickPointEvent
            ((i : ℕ) * chosenBlockLength delta n)
            (scaleIndex delta n) chosenProfileDelta
            (chosenThickDelta delta) x) := by
  let eta := terminalMarkedPoissonLowerError
    (scaleIndex delta n) S hitError
  have hn : 2 ≤ scaleIndex delta n := by
    have hs4 := hparameters.scale_ge_four
    omega
  have hexit0 : 0 ≤ terminalPoissonExitError (scaleIndex delta n) S :=
    PoissonKernelHarnack.poissonKernelRelativeError_nonneg hS (by omega)
      hgreenLower
  have heta0 : 0 ≤ eta := by
    dsimp [eta, terminalMarkedPoissonLowerError]
    unfold markedPoissonLowerError
    apply le_max_of_le_left
    nlinarith [mul_nonneg hexit0 hhitFactor0]
  apply annularComparisons_terminalThick_of_parameterCertificate_decomposition
    hparameters eta heta0 (by simpa only [eta] using hloss1)
    (by simpa only [eta] using hlossQuarter)
  · intro x hx
    dsimp only [eta]
    change MarkedKernelLower
      (fun _ : Fin (requiredTerminalCount
        (scaleIndex delta n) chosenProfileDelta) ↦
          ENNReal.ofReal (1 - terminalMarkedPoissonLowerError
            (scaleIndex delta n) S hitError))
      (fun _ k ↦ ENNReal.ofReal
        (visitMass (terminalHitProbability (scaleIndex delta n))
          (terminalEscapeProbability (scaleIndex delta n)) k))
      (fun _ (u : TerminalEntrance (scaleIndex delta n) x)
          (z : TerminalExit (scaleIndex delta n) x) ↦
        MarkedBoundaryVisitKernel.terminalSkeletonKernel
          (TerminalExcursionPathwise.terminalOuterBoundary
            (scaleIndex delta n) x) u.1 z.1)
      (fun _ (u : TerminalEntrance (scaleIndex delta n) x) k
          (z : TerminalExit (scaleIndex delta n) x) ↦
        MarkedBoundaryVisitKernel.terminalMarkedKernel
          (TerminalExcursionPathwise.terminalOuterBoundary
            (scaleIndex delta n) x) x u.1 k z.1)
    exact terminalMarkedKernel_terminalBoundary_markedKernelLower
      (requiredTerminalCount (scaleIndex delta n) chosenProfileDelta)
      (scaleIndex delta n) S x hitError hn hS
      hcutScale hcutOuter hgreenLower hexitError1
      (by linarith [hparameters.hit_le_half]) hhitError0 hhitFactor0 hloss1
      (hhitLower x hx) (hhitUpper x hx)
  · exact hdecompose

/-- Final canonical terminal adapter.  The combined scale certificate
discharges all mean--variance, Harnack, cut-geometry, and accumulated-loss
estimates.  Its sole remaining input is the genuine full complementary-
skeleton disintegration of each stopped successful-point event. -/
theorem annularComparisons_terminalThick_of_markedScaleCertificate_decomposition
    {delta : ℝ} {n : ℕ}
    (hcertificate : TerminalMarkedScaleCertificate delta (scaleIndex delta n))
    (hdecompose : ∀ (i : Fin (chosenBlockCount delta n)) (x : Point),
      x ∈ ThickPoint.candidateBox (scaleIndex delta n) →
      ∃ skeletonWeight :
          TerminalSkeletonData
              (requiredTerminalCount
                (scaleIndex delta n) chosenProfileDelta) →
            (Fin (requiredTerminalCount
                (scaleIndex delta n) chosenProfileDelta) →
              TerminalEntrance (scaleIndex delta n) x) →
            (Fin (requiredTerminalCount
                (scaleIndex delta n) chosenProfileDelta) →
              TerminalExit (scaleIndex delta n) x) → ℝ≥0∞,
        MarkedStoppedDataLowerDecomposition fairSteps
          (stoppedSuccessfulPointEvent
            ((i : ℕ) * chosenBlockLength delta n)
            (scaleIndex delta n) chosenProfileDelta x)
          (stoppedThickPointEvent
            ((i : ℕ) * chosenBlockLength delta n)
            (scaleIndex delta n) chosenProfileDelta
            (chosenThickDelta delta) x)
          skeletonWeight
          (supportedTerminalSkeletonKernel
            (profileDelta := chosenProfileDelta) (scaleIndex delta n) x)
          (supportedTerminalMarkedKernel
            (profileDelta := chosenProfileDelta) (scaleIndex delta n) x)
          (terminalVisitEvent (scaleIndex delta n)
            (chosenThickDelta delta)
            (requiredTerminalCount
              (scaleIndex delta n) chosenProfileDelta))) :
    ∀ (i : Fin (chosenBlockCount delta n)) (x : Point),
      x ∈ ThickPoint.candidateBox (scaleIndex delta n) →
      (1 - terminalEpsilon) * fairSteps.real
          (stoppedSuccessfulPointEvent
            ((i : ℕ) * chosenBlockLength delta n)
            (scaleIndex delta n) chosenProfileDelta x) ≤
        fairSteps.real
          (stoppedThickPointEvent
            ((i : ℕ) * chosenBlockLength delta n)
            (scaleIndex delta n) chosenProfileDelta
            (chosenThickDelta delta) x) := by
  exact annularComparisons_terminalThick_of_markedPoisson_decomposition
    hcertificate.parameters ((scaleIndex delta n) ^ 8)
    (terminalHitRelativeError (scaleIndex delta n))
    hcertificate.marked.cut_inner hcertificate.marked.cut_scale
    hcertificate.marked.cut_outer hcertificate.marked.greenLower_pos
    hcertificate.marked.exitError_le_one
    hcertificate.marked.hitError_nonneg hcertificate.marked.hitFactor_nonneg
    hcertificate.marked.markedLoss_le_one
    hcertificate.marked.markedLoss_quarter
    (fun _ _ u ↦ hcertificate.marked.hitLower _ u)
    (fun _ _ u ↦ hcertificate.marked.hitUpper _ u)
    hdecompose

/-- The exact `AnnularComparisons.terminalThick` field at every scale carrying
the canonical terminal certificate.  The stopped-word insertion theorem now
discharges the last full-skeleton decomposition input. -/
theorem annularComparisons_terminalThick_of_markedScaleCertificate
    {delta : ℝ} {n : ℕ}
    (hcertificate : TerminalMarkedScaleCertificate delta (scaleIndex delta n)) :
    ∀ (i : Fin (chosenBlockCount delta n)) (x : Point),
      x ∈ ThickPoint.candidateBox (scaleIndex delta n) →
      (1 - terminalEpsilon) * fairSteps.real
          (stoppedSuccessfulPointEvent
            ((i : ℕ) * chosenBlockLength delta n)
            (scaleIndex delta n) chosenProfileDelta x) ≤
        fairSteps.real
          (stoppedThickPointEvent
            ((i : ℕ) * chosenBlockLength delta n)
            (scaleIndex delta n) chosenProfileDelta
            (chosenThickDelta delta) x) := by
  apply annularComparisons_terminalThick_of_markedScaleCertificate_decomposition
    hcertificate
  intro i x _hx
  exact exists_terminalMarkedStoppedDataLowerDecomposition
    ((i : ℕ) * chosenBlockLength delta n) (scaleIndex delta n)
    chosenProfileDelta (chosenThickDelta delta) x (by
      have hs := hcertificate.marked.scale_ge_four
      omega)

/-- Appendix A.7 at the exact HLOZ scales: for every positive deviation
parameter, the terminal-thickness field holds at all sufficiently large
scale indices with no remaining assumptions. -/
theorem eventually_annularComparisons_terminalThick
    {delta : ℝ} (hdelta : 0 < delta) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∀ (i : Fin (chosenBlockCount delta n)) (x : Point),
        x ∈ ThickPoint.candidateBox (scaleIndex delta n) →
        (1 - terminalEpsilon) * fairSteps.real
            (stoppedSuccessfulPointEvent
              ((i : ℕ) * chosenBlockLength delta n)
              (scaleIndex delta n) chosenProfileDelta x) ≤
          fairSteps.real
            (stoppedThickPointEvent
              ((i : ℕ) * chosenBlockLength delta n)
              (scaleIndex delta n) chosenProfileDelta
              (chosenThickDelta delta) x) := by
  filter_upwards
      [eventually_terminalMarkedScaleCertificate_scaleIndex hdelta]
      with n hcertificate
  exact annularComparisons_terminalThick_of_markedScaleCertificate hcertificate

end

end Erdos1165.AppendixTerminalMarkedAssembly
