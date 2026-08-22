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

import ErdosProblems.Erdos1165.AnnularOffspringKernelLiteralProfile
import ErdosProblems.Erdos1165.AnnularNestedProfileKernel
import ErdosProblems.Erdos1165.TerminalSkeletonWords

/-!
# Child-entrance vector refinement of a literal annular gap

The endpoint-integrated one-gap count atom is not enough for recursive
Appendix-A.6 disintegration: the next radial level starts at all of the
inner-boundary points visited by the completed offspring excursions.  This
file refines the literal atom by that finite vector and proves that summing
the vector recovers the original literal atom and kernel exactly.

The refinement is defined by prefix-free stopped words.  Hence its
measurability and exact partition are properties of the actual walk event,
not an assumed future-vector law.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace Erdos1165.AnnularGapChildVector

open AnnularBoundaryExcursionKernel AnnularOffspringKernel
open MarkedBridgeFactorization PlanarPotential TerminalSkeletonWords
open TerminalExcursionPathwise TerminalSequentialVisitLaw ThickPoint

noncomputable section

/-- Finite supported inner-boundary states. -/
abbrev InnerBoundaryPoint (inner : Set Point) := {z : Point // z ∈ inner}

/-- The child entrance point at the completion of offspring excursion `j`
inside a finite gap word. -/
noncomputable def gapChildFinish
    (middle inner : Set Point) (start : Point)
    (omega : StepPath) (horizon j : ℕ) : ℕ := by
  classical
  exact excursionFinish (trajectoryFrom start omega)
    middle inner horizon j

noncomputable def gapChildPoint
    (middle inner : Set Point) (start : Point)
    (omega : StepPath) (horizon j : ℕ) : Point := by
  classical
  exact trajectoryFrom start omega
    (gapChildFinish middle inner start omega horizon j)

/-- Prefix-free words for one literal gap, refined by the ordered vector of
all inner-boundary child entrances. -/
abbrev GapChildVectorWordCode
    (outer middle inner : Set Point) (start : Point) (q : ℕ)
    (children : Fin q → InnerBoundaryPoint inner) :=
  {w : StoppedWord //
    AbsoluteBoundaryFirstAt outer start (extendStoppedWord w) w.1 ∧
      boundaryExcursionCount middle inner start (extendStoppedWord w) w.1 = q ∧
      ∀ j : Fin q,
        gapChildPoint middle inner start (extendStoppedWord w) w.1 j = children j}

theorem prefixFree_gapChildVectorWordCode
    (outer middle inner : Set Point) (start : Point) (q : ℕ)
    (children : Fin q → InnerBoundaryPoint inner) :
    PrefixFree (fun c : GapChildVectorWordCode
      outer middle inner start q children ↦ c.1) := by
  intro c d hcd
  rw [Set.disjoint_left]
  intro omega hc hd
  have hcfirst := absoluteBoundaryFirstAt_of_mem_stoppedWordCylinder hc c.2.1
  have hdfirst := absoluteBoundaryFirstAt_of_mem_stoppedWordCylinder hd d.2.1
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

/-- Literal stopped event for a fixed ordered child-entrance vector. -/
def literalGapChildVectorAtom
    (outer middle inner : Set Point) (start : Point) (q : ℕ)
    (children : Fin q → InnerBoundaryPoint inner) : Set StepPath :=
  stoppedWordEvent (fun c : GapChildVectorWordCode
    outer middle inner start q children ↦ c.1)

theorem measurableSet_literalGapChildVectorAtom
    (outer middle inner : Set Point) (start : Point) (q : ℕ)
    (children : Fin q → InnerBoundaryPoint inner) :
    MeasurableSet
      (literalGapChildVectorAtom outer middle inner start q children) := by
  exact measurableSet_stoppedWordEvent _

private lemma boundaryExcursionCount_eq_extend_of_mem
    {middle inner : Set Point} {start : Point}
    {omega : StepPath} {w : StoppedWord}
    (homega : omega ∈ stoppedWordCylinder w) :
    boundaryExcursionCount middle inner start omega w.1 =
      boundaryExcursionCount middle inner start (extendStoppedWord w) w.1 := by
  apply boundaryExcursionCount_congr_prefix
  intro t ht
  exact trajectoryFrom_eq_extendStoppedWord_of_mem homega start ht

private lemma gapChildFinish_eq_extend_of_mem
    {middle inner : Set Point} {start : Point}
    {omega : StepPath} {w : StoppedWord}
    (homega : omega ∈ stoppedWordCylinder w) (j : ℕ) :
    gapChildFinish middle inner start omega w.1 j =
      gapChildFinish middle inner start (extendStoppedWord w) w.1 j := by
  classical
  unfold gapChildFinish
  apply excursionFinish_congr_prefix
  intro t ht
  exact trajectoryFrom_eq_extendStoppedWord_of_mem homega start ht

private lemma gapChildPoint_eq_extend_of_mem
    {middle inner : Set Point} {start : Point}
    {omega : StepPath} {w : StoppedWord}
    (homega : omega ∈ stoppedWordCylinder w) (j : ℕ)
    (hfinish : gapChildFinish middle inner start omega w.1 j ≤ w.1) :
    gapChildPoint middle inner start omega w.1 j =
      gapChildPoint middle inner start (extendStoppedWord w) w.1 j := by
  classical
  unfold gapChildPoint
  rw [← gapChildFinish_eq_extend_of_mem homega j]
  apply trajectoryFrom_eq_extendStoppedWord_of_mem homega start
  exact hfinish

lemma mem_literalGapChildVectorAtom_exists
    {outer middle inner : Set Point} {start : Point} {q : ℕ}
    {children : Fin q → InnerBoundaryPoint inner} {omega : StepPath}
    (homega : omega ∈
      literalGapChildVectorAtom outer middle inner start q children) :
    ∃ horizon,
      AbsoluteBoundaryFirstAt outer start omega horizon ∧
      boundaryExcursionCount middle inner start omega horizon = q ∧
      ∀ j : Fin q,
        gapChildPoint middle inner start omega horizon j = children j := by
  classical
  obtain ⟨c, hc⟩ := Set.mem_iUnion.mp homega
  have hcount : boundaryExcursionCount middle inner start omega c.1.1 = q := by
    rw [boundaryExcursionCount_eq_extend_of_mem hc]
    exact c.2.2.1
  refine ⟨c.1.1,
    absoluteBoundaryFirstAt_of_mem_stoppedWordCylinder hc c.2.1, hcount, ?_⟩
  · intro j
    have hfinish : gapChildFinish middle inner start omega c.1.1 j ≤ c.1.1 := by
      unfold gapChildFinish
      apply finish_le_horizon_of_lt_completedExcursionCount
      unfold boundaryExcursionCount at hcount
      rw [hcount]
      exact j.isLt
    rw [gapChildPoint_eq_extend_of_mem hc j hfinish]
    exact c.2.2.2 j

/-- The fixed-vector events are disjoint because the actual child entrance
at each completed excursion is unique. -/
theorem literalGapChildVectorAtom_pairwise
    (outer middle inner : Set Point) (start : Point) (q : ℕ) :
    Pairwise fun children children' : Fin q → InnerBoundaryPoint inner ↦
      Disjoint
        (literalGapChildVectorAtom outer middle inner start q children)
        (literalGapChildVectorAtom outer middle inner start q children') := by
  intro children children' hne
  rw [Set.disjoint_left]
  intro omega hchildren hchildren'
  obtain ⟨horizon, hfirst, _hcount, hvector⟩ :=
    mem_literalGapChildVectorAtom_exists hchildren
  obtain ⟨horizon', hfirst', _hcount', hvector'⟩ :=
    mem_literalGapChildVectorAtom_exists hchildren'
  have hhorizon : horizon = horizon' :=
    absoluteBoundaryFirstAt_unique hfirst hfirst'
  subst horizon'
  apply hne
  funext j
  apply Subtype.ext
  exact (hvector j).symm.trans (hvector' j)

/-- Summing all supported child-entrance vectors is exactly the original
literal endpoint-integrated exact-count atom. -/
theorem literalGapIntegratedMarkedAtom_eq_iUnion_childVector
    (outer middle inner : Set Point) (start : Point) (q : ℕ) :
    literalGapIntegratedMarkedAtom outer middle inner start q =
      ⋃ children : Fin q → InnerBoundaryPoint inner,
        literalGapChildVectorAtom outer middle inner start q children := by
  classical
  ext omega
  constructor
  · intro homega
    obtain ⟨horizon, hfirst, hcount⟩ := Set.mem_iUnion.mp homega
    let s := trajectoryFrom start omega
    have hfinish (j : Fin q) :
        excursionFinish s middle inner horizon j ≤ horizon := by
      apply finish_le_horizon_of_lt_completedExcursionCount
      unfold boundaryExcursionCount at hcount
      dsimp only [s]
      rw [hcount]
      exact j.isLt
    let children : Fin q → InnerBoundaryPoint inner := fun j ↦
      ⟨gapChildPoint middle inner start omega horizon j,
        excursionFinish_mem_inner_of_le s middle inner horizon j (hfinish j)⟩
    let w : StoppedWord := ⟨horizon, stepPrefix horizon omega⟩
    have hwmem : omega ∈ stoppedWordCylinder w := rfl
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
      rw [← boundaryExcursionCount_eq_extend_of_mem hwmem]
      exact hcount
    have hwchildren : ∀ j : Fin q,
        gapChildPoint middle inner start (extendStoppedWord w) horizon j =
          children j := by
      intro j
      exact (gapChildPoint_eq_extend_of_mem hwmem j (hfinish j)).symm
    let c : GapChildVectorWordCode outer middle inner start q children :=
      ⟨w, hwfirst, hwcount, hwchildren⟩
    exact Set.mem_iUnion.mpr ⟨children, Set.mem_iUnion.mpr ⟨c, hwmem⟩⟩
  · intro homega
    obtain ⟨children, hchildren⟩ := Set.mem_iUnion.mp homega
    obtain ⟨c, hc⟩ := Set.mem_iUnion.mp hchildren
    have hfirst := absoluteBoundaryFirstAt_of_mem_stoppedWordCylinder hc c.2.1
    have hcount : boundaryExcursionCount middle inner start omega c.1.1 = q := by
      rw [boundaryExcursionCount_eq_extend_of_mem hc]
      exact c.2.2.1
    exact Set.mem_iUnion.mpr ⟨c.1.1, hfirst, hcount⟩

/-- Probability of one fixed child-entrance vector. -/
def literalGapChildVectorKernel
    (outer middle inner : Set Point) (start : Point) (q : ℕ)
    (children : Fin q → InnerBoundaryPoint inner) : ℝ≥0∞ :=
  fairSteps (literalGapChildVectorAtom
    outer middle inner start q children)

/-- Exact countable marginal identity for the concrete child-vector kernel.
For literal disc boundaries the index type is finite, so this specializes
immediately to a finite sum. -/
theorem tsum_literalGapChildVectorKernel_eq_integratedMarkedKernel
    (outer middle inner : Set Point) (start : Point) (q : ℕ) :
    ∑' children : Fin q → InnerBoundaryPoint inner,
        literalGapChildVectorKernel outer middle inner start q children =
      literalGapIntegratedMarkedKernel outer middle inner start q := by
  rw [literalGapIntegratedMarkedKernel,
    literalGapIntegratedMarkedAtom_eq_iUnion_childVector,
    measure_iUnion
      (literalGapChildVectorAtom_pairwise outer middle inner start q)]
  · rfl
  · exact fun children ↦
      measurableSet_literalGapChildVectorAtom
        outer middle inner start q children

end

end Erdos1165.AnnularGapChildVector
