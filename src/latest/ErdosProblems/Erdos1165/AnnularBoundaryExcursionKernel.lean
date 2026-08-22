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

import ErdosProblems.Erdos1165.AnnularProfileClocks
import ErdosProblems.Erdos1165.MarkedBridgeFactorization

/-!
# Joint intermediate-annulus excursion-count/exit kernels

The Appendix-A.6 mark is not a point local time.  A bridge begins on a
middle boundary, stops at the first hit of an outer boundary, and is marked
by the number of completed middle-to-inner excursions before that exit.
This file defines that literal joint atom and supplies a canonical
prefix-free finite-word code for it.  Consequently the atom can be inserted
by `MarkedBridgeFactorization` without any assumed measure identity.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Erdos1165.AnnularBoundaryExcursionKernel

noncomputable section

open MarkedBridgeFactorization TerminalSequentialVisitLaw
open ThickPoint PlanarPotential

/-- The exact nested excursion count of a finite fresh bridge. -/
noncomputable def boundaryExcursionCount
    (middle inner : Set Point) (start : Point)
    (omega : StepPath) (horizon : ℕ) : ℕ := by
  classical
  exact completedExcursionCount (trajectoryFrom start omega)
    middle inner horizon

/-- A middle-started bridge which first exits at `outer`, makes exactly `q`
completed middle-to-inner excursions, and retains the outer endpoint. -/
def boundaryExcursionExitAtom
    (outer middle inner : Set Point) (start : Point)
    (q : ℕ) (exit : Point) : Set StepPath :=
  ⋃ horizon : ℕ,
    {omega |
      AbsoluteBoundaryFirstAt outer start omega horizon ∧
      boundaryExcursionCount middle inner start omega horizon = q ∧
      trajectoryFrom start omega horizon = exit}

/-- The corresponding literal joint kernel. -/
def boundaryExcursionExitKernel
    (outer middle inner : Set Point) (start : Point)
    (q : ℕ) (exit : Point) : ℝ≥0∞ :=
  fairSteps (boundaryExcursionExitAtom outer middle inner start q exit)

lemma boundaryExcursionCount_congr_prefix
    {middle inner : Set Point} {start : Point} {omega eta : StepPath}
    {horizon : ℕ}
    (hprefix : ∀ t ≤ horizon,
      trajectoryFrom start omega t = trajectoryFrom start eta t) :
    boundaryExcursionCount middle inner start omega horizon =
      boundaryExcursionCount middle inner start eta horizon := by
  classical
  unfold boundaryExcursionCount
  exact Proposition13Measurability.completedExcursionCount_congr_prefix
    hprefix middle inner

/-- Finite first-outer-hit words carrying both the nested excursion count
and the exact exit endpoint. -/
abbrev BoundaryExcursionExitWordCode
    (outer middle inner : Set Point) (start : Point)
    (q : ℕ) (exit : Point) :=
  {w : StoppedWord //
    AbsoluteBoundaryFirstAt outer start (extendStoppedWord w) w.1 ∧
      boundaryExcursionCount middle inner start (extendStoppedWord w) w.1 = q ∧
      trajectoryFrom start (extendStoppedWord w) w.1 = exit}

theorem prefixFree_boundaryExcursionExitWordCode
    (outer middle inner : Set Point) (start : Point)
    (q : ℕ) (exit : Point) :
    PrefixFree (fun c : BoundaryExcursionExitWordCode
      outer middle inner start q exit ↦ c.1) := by
  intro c d hcd
  rw [Set.disjoint_left]
  intro omega hc hd
  have hcfirst := absoluteBoundaryFirstAt_of_mem_stoppedWordCylinder
    hc c.2.1
  have hdfirst := absoluteBoundaryFirstAt_of_mem_stoppedWordCylinder
    hd d.2.1
  have hlen : c.1.1 = d.1.1 :=
    absoluteBoundaryFirstAt_unique hcfirst hdfirst
  apply hcd
  apply Subtype.ext
  apply Sigma.ext hlen
  apply (Fin.heq_fun_iff hlen).2
  intro i
  change stepPrefix c.1.1 omega = c.1.2 at hc
  change stepPrefix d.1.1 omega = d.1.2 at hd
  have hci := congrFun hc i
  have hdi := congrFun hd ⟨(i : ℕ), hlen ▸ i.2⟩
  simpa only [stepPrefix] using hci.symm.trans hdi

private lemma boundaryExcursionCount_eq_extendStoppedWord_of_mem
    {middle inner : Set Point} {start : Point}
    {omega : StepPath} {w : StoppedWord}
    (homega : omega ∈ stoppedWordCylinder w) :
    boundaryExcursionCount middle inner start omega w.1 =
      boundaryExcursionCount middle inner start (extendStoppedWord w) w.1 := by
  apply boundaryExcursionCount_congr_prefix
  intro t ht
  exact trajectoryFrom_eq_extendStoppedWord_of_mem homega start ht

/-- Pathwise coverage of the joint intermediate-annulus atom by its literal
finite stopped words. -/
theorem boundaryExcursionExitAtom_eq_stoppedWordEvent
    (outer middle inner : Set Point) (start : Point)
    (q : ℕ) (exit : Point) :
    boundaryExcursionExitAtom outer middle inner start q exit =
      stoppedWordEvent
        (fun c : BoundaryExcursionExitWordCode
          outer middle inner start q exit ↦ c.1) := by
  ext omega
  constructor
  · intro homega
    obtain ⟨horizon, hfirst, hcount, hendpoint⟩ := mem_iUnion.mp homega
    let w : StoppedWord := ⟨horizon, stepPrefix horizon omega⟩
    have hwmem : omega ∈ stoppedWordCylinder w := by
      change stepPrefix horizon omega = stepPrefix horizon omega
      rfl
    have hwfirst : AbsoluteBoundaryFirstAt outer start
        (extendStoppedWord w) horizon := by
      constructor
      · rw [← trajectoryFrom_eq_extendStoppedWord_of_mem hwmem start le_rfl]
        exact hfirst.1
      · intro t ht
        rw [← trajectoryFrom_eq_extendStoppedWord_of_mem hwmem start ht.le]
        exact hfirst.2 t ht
    have hwcount : boundaryExcursionCount middle inner start
        (extendStoppedWord w) horizon = q := by
      rw [← boundaryExcursionCount_eq_extendStoppedWord_of_mem hwmem]
      exact hcount
    have hwendpoint : trajectoryFrom start (extendStoppedWord w) horizon = exit := by
      rw [← trajectoryFrom_eq_extendStoppedWord_of_mem hwmem start le_rfl]
      exact hendpoint
    let c : BoundaryExcursionExitWordCode outer middle inner start q exit :=
      ⟨w, hwfirst, hwcount, hwendpoint⟩
    exact mem_iUnion.mpr ⟨c, hwmem⟩
  · intro homega
    obtain ⟨c, hc⟩ := mem_iUnion.mp homega
    have hfirst := absoluteBoundaryFirstAt_of_mem_stoppedWordCylinder hc c.2.1
    have hcount : boundaryExcursionCount middle inner start omega c.1.1 = q := by
      rw [boundaryExcursionCount_eq_extendStoppedWord_of_mem hc]
      exact c.2.2.1
    have hendpoint : trajectoryFrom start omega c.1.1 = exit := by
      rw [trajectoryFrom_eq_extendStoppedWord_of_mem hc start le_rfl]
      exact c.2.2.2
    exact mem_iUnion.mpr ⟨c.1.1, hfirst, hcount, hendpoint⟩

theorem measurableSet_boundaryExcursionExitAtom
    (outer middle inner : Set Point) (start : Point)
    (q : ℕ) (exit : Point) :
    MeasurableSet (boundaryExcursionExitAtom outer middle inner start q exit) := by
  rw [boundaryExcursionExitAtom_eq_stoppedWordEvent]
  exact measurableSet_stoppedWordEvent _

/-- Canonical prefix-free stopped-event code for the correct A.6 marked
bridge kernel. -/
def boundaryExcursionExitStoppedEventCode
    (outer middle inner : Set Point) (start : Point)
    (q : ℕ) (exit : Point) :
    StoppedEventCode
      (boundaryExcursionExitAtom outer middle inner start q exit) where
  Code := BoundaryExcursionExitWordCode outer middle inner start q exit
  countableCode := inferInstance
  word := fun c ↦ c.1
  prefixFree_word := prefixFree_boundaryExcursionExitWordCode
    outer middle inner start q exit
  event_eq := boundaryExcursionExitAtom_eq_stoppedWordEvent
    outer middle inner start q exit

/-- Exact mass of the canonical word code, with no probabilistic premise. -/
theorem boundaryExcursionExitKernel_eq_tsum_stoppedWordMass
    (outer middle inner : Set Point) (start : Point)
    (q : ℕ) (exit : Point) :
    boundaryExcursionExitKernel outer middle inner start q exit =
      ∑' c : BoundaryExcursionExitWordCode outer middle inner start q exit,
        stoppedWordMass c.1 := by
  exact (boundaryExcursionExitStoppedEventCode
    outer middle inner start q exit).mass_eq

/-- The unmarked first-outer-exit endpoint event is partitioned by the exact
nested excursion count. -/
theorem boundaryExitEndpointSteps_eq_iUnion_boundaryExcursionExitAtom
    (outer middle inner : Set Point) (start exit : Point) :
    boundaryExitEndpointSteps outer start exit =
      ⋃ q : ℕ, boundaryExcursionExitAtom outer middle inner start q exit := by
  ext omega
  constructor
  · intro homega
    obtain ⟨horizon, hfirst, hendpoint⟩ := mem_iUnion.mp homega
    let q := boundaryExcursionCount middle inner start omega horizon
    exact mem_iUnion.mpr ⟨q, mem_iUnion.mpr
      ⟨horizon, hfirst, rfl, hendpoint⟩⟩
  · intro homega
    obtain ⟨q, hq⟩ := mem_iUnion.mp homega
    obtain ⟨horizon, hfirst, _hcount, hendpoint⟩ := mem_iUnion.mp hq
    exact mem_iUnion.mpr ⟨horizon, hfirst, hendpoint⟩

theorem boundaryExcursionExitAtom_pairwise
    (outer middle inner : Set Point) (start exit : Point) :
    Pairwise fun q q' : ℕ ↦
      Disjoint (boundaryExcursionExitAtom outer middle inner start q exit)
        (boundaryExcursionExitAtom outer middle inner start q' exit) := by
  intro q q' hne
  rw [Set.disjoint_left]
  intro omega hq hq'
  obtain ⟨horizon, hfirst, hcount, _hexit⟩ := mem_iUnion.mp hq
  obtain ⟨horizon', hfirst', hcount', _hexit'⟩ := mem_iUnion.mp hq'
  have hhorizon : horizon = horizon' :=
    absoluteBoundaryFirstAt_unique hfirst hfirst'
  subst horizon'
  exact hne (hcount.symm.trans hcount')

/-- Exact normalization of the joint count/endpoint kernel. -/
theorem fairSteps_boundaryExitEndpointSteps_eq_tsum_excursionKernel
    (outer middle inner : Set Point) (start exit : Point) :
    fairSteps (boundaryExitEndpointSteps outer start exit) =
      ∑' q : ℕ,
        boundaryExcursionExitKernel outer middle inner start q exit := by
  rw [boundaryExitEndpointSteps_eq_iUnion_boundaryExcursionExitAtom,
    measure_iUnion (boundaryExcursionExitAtom_pairwise
      outer middle inner start exit)]
  · rfl
  · intro q
    exact measurableSet_boundaryExcursionExitAtom
      outer middle inner start q exit

end

end Erdos1165.AnnularBoundaryExcursionKernel
