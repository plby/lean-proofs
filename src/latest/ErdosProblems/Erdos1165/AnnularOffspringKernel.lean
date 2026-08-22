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

import ErdosProblems.Erdos1165.AnnularBoundaryExcursionKernel
import ErdosProblems.Erdos1165.MarkedBoundaryVisitKernel
import ErdosProblems.Erdos1165.ProfileGapChain

/-!
# Endpoint-retaining offspring kernels for an intermediate annular gap

Fix one erased Appendix-A.6 gap.  Its state on the middle boundary is `u`,
and `w` is the retained endpoint on the next outer boundary.  The subkernel
`cycle u v` is one completed middle-to-inner-to-middle excursion, ending at
the new middle-boundary state `v`.  The kernel `escape u w` is the final
middle-to-outer piece which makes no further inner excursion.  Iterating
`cycle` and then `escape` gives the joint kernel marked by the exact number
of completed offspring excursions.

The endpoint-conditioned theorem below records the exact finite renewal
algebra.  Under a genuine fixed-endpoint transport premise, the atom with
`q` offspring is trapped between

`(1-epsilon)^(q+1) 2^(-(q+1)) K₀(u,w)` and
`(1+epsilon)^(q+1) 2^(-(q+1)) K₀(u,w)`.

No independence after forgetting endpoints is used: the new middle endpoint
is summed at every cycle and the final outer endpoint is retained.  At the
consecutive HLOZ radii the fixed-endpoint premise is false because the
Poisson kernel has order-one angular variation.  The Appendix-A.6 comparison
therefore uses the endpoint-integrated row developed below; its one-parent
geometric bounds sum over weak compositions to the negative-binomial
transition mass.
-/

open scoped BigOperators ENNReal

namespace Erdos1165.AnnularOffspringKernel

noncomputable section

open MeasureTheory AppendixFirstMoment PathInsertion ProfileGapChain
open AnnularBoundaryExcursionKernel
open TerminalSequentialVisitLaw
open MarkedBridgeFactorization
open MarkedBoundaryVisitKernel

/-! ## The literal Appendix-A.6 joint kernel -/

/-- The unmarked first-outer-hit kernel, retaining the exact endpoint. -/
def literalGapSkeletonKernel
    (outer : Set Point) (start exit : Point) : ℝ≥0∞ :=
  fairSteps (TerminalSequentialVisitLaw.boundaryExitEndpointSteps
    outer start exit)

/-- The literal count/endpoint kernel from
`AnnularBoundaryExcursionKernel`. -/
def literalGapMarkedKernel
    (outer middle inner : Set Point) (start : Point)
    (q : ℕ) (exit : Point) : ℝ≥0∞ :=
  boundaryExcursionExitKernel outer middle inner start q exit

/-- Exact normalization of the literal count mark.  In particular the
count atoms lose no path mass and continue to remember the outer endpoint. -/
theorem literalGapSkeletonKernel_eq_tsum_marked
    (outer middle inner : Set Point) (start exit : Point) :
    literalGapSkeletonKernel outer start exit =
      ∑' q : ℕ, literalGapMarkedKernel outer middle inner start q exit := by
  exact fairSteps_boundaryExitEndpointSteps_eq_tsum_excursionKernel
    outer middle inner start exit

/-- The canonical endpoint-integrated atom: first exit at `outer` after
exactly `q` completed middle-to-inner excursions. -/
def literalGapIntegratedMarkedAtom
    (outer middle inner : Set Point) (start : Point) (q : ℕ) : Set StepPath :=
  ⋃ horizon : ℕ,
    {omega |
      AbsoluteBoundaryFirstAt outer start omega horizon ∧
        boundaryExcursionCount middle inner start omega horizon = q}

/-- Probability of the endpoint-integrated exact-offspring atom. -/
def literalGapIntegratedMarkedKernel
    (outer middle inner : Set Point) (start : Point) (q : ℕ) : ℝ≥0∞ :=
  fairSteps (literalGapIntegratedMarkedAtom outer middle inner start q)

/-- Integrating the retained endpoint is literally a union, not a change of
the underlying count event. -/
theorem literalGapIntegratedMarkedAtom_eq_iUnion_exit
    (outer middle inner : Set Point) (start : Point) (q : ℕ) :
    literalGapIntegratedMarkedAtom outer middle inner start q =
      ⋃ exit : Point,
        boundaryExcursionExitAtom outer middle inner start q exit := by
  ext omega
  constructor
  · intro homega
    obtain ⟨horizon, hfirst, hcount⟩ := Set.mem_iUnion.mp homega
    exact Set.mem_iUnion.mpr
      ⟨PlanarPotential.trajectoryFrom start omega horizon,
        Set.mem_iUnion.mpr ⟨horizon, hfirst, hcount, rfl⟩⟩
  · intro homega
    obtain ⟨exit, hexit⟩ := Set.mem_iUnion.mp homega
    obtain ⟨horizon, hfirst, hcount, _hendpoint⟩ := Set.mem_iUnion.mp hexit
    exact Set.mem_iUnion.mpr ⟨horizon, hfirst, hcount⟩

theorem measurableSet_literalGapIntegratedMarkedAtom
    (outer middle inner : Set Point) (start : Point) (q : ℕ) :
    MeasurableSet (literalGapIntegratedMarkedAtom
      outer middle inner start q) := by
  rw [literalGapIntegratedMarkedAtom_eq_iUnion_exit]
  exact MeasurableSet.iUnion fun exit ↦
    measurableSet_boundaryExcursionExitAtom
      outer middle inner start q exit

theorem boundaryExcursionExitAtom_pairwise_exit
    (outer middle inner : Set Point) (start : Point) (q : ℕ) :
    Pairwise fun exit exit' : Point ↦
      Disjoint (boundaryExcursionExitAtom outer middle inner start q exit)
        (boundaryExcursionExitAtom outer middle inner start q exit') := by
  intro exit exit' hne
  rw [Set.disjoint_left]
  intro omega hexit hexit'
  obtain ⟨horizon, hfirst, _hcount, hendpoint⟩ :=
    Set.mem_iUnion.mp hexit
  obtain ⟨horizon', hfirst', _hcount', hendpoint'⟩ :=
    Set.mem_iUnion.mp hexit'
  have hhorizon : horizon = horizon' :=
    absoluteBoundaryFirstAt_unique hfirst hfirst'
  apply hne
  rw [← hendpoint, ← hendpoint', hhorizon]

/-- Exact countable endpoint integration of the literal joint kernel. -/
theorem literalGapIntegratedMarkedKernel_eq_tsum_exit
    (outer middle inner : Set Point) (start : Point) (q : ℕ) :
    literalGapIntegratedMarkedKernel outer middle inner start q =
      ∑' exit : Point,
        literalGapMarkedKernel outer middle inner start q exit := by
  rw [literalGapIntegratedMarkedKernel,
    literalGapIntegratedMarkedAtom_eq_iUnion_exit,
    measure_iUnion
      (boundaryExcursionExitAtom_pairwise_exit outer middle inner start q)]
  · rfl
  · intro exit
    exact measurableSet_boundaryExcursionExitAtom
      outer middle inner start q exit

theorem literalGapIntegratedMarkedAtom_pairwise
    (outer middle inner : Set Point) (start : Point) :
    Pairwise fun q q' : ℕ ↦
      Disjoint (literalGapIntegratedMarkedAtom outer middle inner start q)
        (literalGapIntegratedMarkedAtom outer middle inner start q') := by
  intro q q' hne
  rw [Set.disjoint_left]
  intro omega hq hq'
  obtain ⟨horizon, hfirst, hcount⟩ := Set.mem_iUnion.mp hq
  obtain ⟨horizon', hfirst', hcount'⟩ := Set.mem_iUnion.mp hq'
  have hhorizon : horizon = horizon' :=
    absoluteBoundaryFirstAt_unique hfirst hfirst'
  subst horizon'
  exact hne (hcount.symm.trans hcount')

/-- The integrated count atoms partition the entire first-outer-exit event. -/
theorem boundaryExitMarkedSteps_univ_eq_iUnion_integratedMarkedAtom
    (outer middle inner : Set Point) (start : Point) :
    boundaryExitMarkedSteps outer Set.univ start =
      ⋃ q : ℕ, literalGapIntegratedMarkedAtom outer middle inner start q := by
  ext omega
  constructor
  · intro homega
    obtain ⟨horizon, hfirst, _hendpoint⟩ :=
      (mem_boundaryExitMarkedSteps_iff_exists_first
        outer Set.univ start omega).mp homega
    let q := boundaryExcursionCount middle inner start omega horizon
    exact Set.mem_iUnion.mpr
      ⟨q, Set.mem_iUnion.mpr ⟨horizon, hfirst, rfl⟩⟩
  · intro homega
    obtain ⟨q, hq⟩ := Set.mem_iUnion.mp homega
    obtain ⟨horizon, hfirst, _hcount⟩ := Set.mem_iUnion.mp hq
    exact (mem_boundaryExitMarkedSteps_iff_exists_first
      outer Set.univ start omega).mpr
        ⟨horizon, hfirst, Set.mem_univ _⟩

/-- Exact normalization of the endpoint-integrated offspring count. -/
theorem fairSteps_boundaryExitMarkedSteps_univ_eq_tsum_integratedMarkedKernel
    (outer middle inner : Set Point) (start : Point) :
    fairSteps (boundaryExitMarkedSteps outer Set.univ start) =
      ∑' q : ℕ,
        literalGapIntegratedMarkedKernel outer middle inner start q := by
  rw [boundaryExitMarkedSteps_univ_eq_iUnion_integratedMarkedAtom,
    measure_iUnion
      (literalGapIntegratedMarkedAtom_pairwise outer middle inner start)]
  · rfl
  · intro q
    exact measurableSet_literalGapIntegratedMarkedAtom
      outer middle inner start q

/-! ## Actual one-cycle components -/

/-- Actual middle-to-inner-to-middle cycle subkernel.  `innerPoint` and
`middlePoint` enumerate the literal boundary vertices.  The first factor is
the first hit of `inner ∪ outer`, marked by its inner endpoint; the second
factor is the subsequent first hit of the middle boundary. -/
def annularCycleKernel
    {Middle Inner : Type*} [Fintype Inner]
    (outer middle inner : Set Point)
    (middlePoint : Middle → Point) (innerPoint : Inner → Point)
    (u v : Middle) : ℝ≥0∞ :=
  ∑ z : Inner,
    MarkedBoundaryVisitKernel.skeletonExitKernel (inner ∪ outer)
        (middlePoint u) (innerPoint z) *
      MarkedBoundaryVisitKernel.skeletonExitKernel middle
        (innerPoint z) (middlePoint v)

/-- Actual final escape subkernel: hit the union boundary for the first time
at the retained outer endpoint. -/
def annularEscapeKernel
    {Middle Exit : Type*}
    (outer inner : Set Point)
    (middlePoint : Middle → Point) (exitPoint : Exit → Point)
    (u : Middle) (w : Exit) : ℝ≥0∞ :=
  MarkedBoundaryVisitKernel.skeletonExitKernel (inner ∪ outer)
    (middlePoint u) (exitPoint w)

/-- Actual unmarked first hit of the outer boundary at the retained
endpoint. -/
def annularUnmarkedKernel
    {Middle Exit : Type*}
    (outer : Set Point)
    (middlePoint : Middle → Point) (exitPoint : Exit → Point)
    (u : Middle) (w : Exit) : ℝ≥0∞ :=
  MarkedBoundaryVisitKernel.skeletonExitKernel outer
    (middlePoint u) (exitPoint w)

/-- Finite real versions consumed by the renewal algebra. -/
def annularCycleKernelReal
    {Middle Inner : Type*} [Fintype Inner]
    (outer middle inner : Set Point)
    (middlePoint : Middle → Point) (innerPoint : Inner → Point)
    (u v : Middle) : ℝ :=
  (annularCycleKernel outer middle inner middlePoint innerPoint u v).toReal

def annularEscapeKernelReal
    {Middle Exit : Type*}
    (outer inner : Set Point)
    (middlePoint : Middle → Point) (exitPoint : Exit → Point)
    (u : Middle) (w : Exit) : ℝ :=
  (annularEscapeKernel outer inner middlePoint exitPoint u w).toReal

def annularUnmarkedKernelReal
    {Middle Exit : Type*}
    (outer : Set Point)
    (middlePoint : Middle → Point) (exitPoint : Exit → Point)
    (u : Middle) (w : Exit) : ℝ :=
  (annularUnmarkedKernel outer middlePoint exitPoint u w).toReal

theorem annularCycleKernelReal_nonneg
    {Middle Inner : Type*} [Fintype Inner]
    (outer middle inner : Set Point)
    (middlePoint : Middle → Point) (innerPoint : Inner → Point)
    (u v : Middle) :
    0 ≤ annularCycleKernelReal outer middle inner
      middlePoint innerPoint u v := ENNReal.toReal_nonneg

theorem annularEscapeKernelReal_nonneg
    {Middle Exit : Type*}
    (outer inner : Set Point)
    (middlePoint : Middle → Point) (exitPoint : Exit → Point)
    (u : Middle) (w : Exit) :
    0 ≤ annularEscapeKernelReal outer inner
      middlePoint exitPoint u w := ENNReal.toReal_nonneg

theorem annularUnmarkedKernelReal_nonneg
    {Middle Exit : Type*}
    (outer : Set Point)
    (middlePoint : Middle → Point) (exitPoint : Exit → Point)
    (u : Middle) (w : Exit) :
    0 ≤ annularUnmarkedKernelReal outer
      middlePoint exitPoint u w := ENNReal.toReal_nonneg

/-! ## Exact endpoint-retaining renewal kernel -/

/-- Apply a finite real subkernel to a nonnegative continuation weight. -/
def kernelAction {State : Type*} [Fintype State]
    (cycle : State → State → ℝ) (f : State → ℝ) (u : State) : ℝ :=
  ∑ v, cycle u v * f v

/-- The joint kernel of exactly `q` completed cycles followed by escape at
the retained endpoint `w`. -/
def markedOffspringKernel {State Exit : Type*} [Fintype State]
    (cycle : State → State → ℝ) (escape : State → Exit → ℝ) :
    ℕ → State → Exit → ℝ
  | 0, u, w => escape u w
  | q + 1, u, w => kernelAction cycle (fun v ↦
      markedOffspringKernel cycle escape q v w) u

@[simp] theorem markedOffspringKernel_zero
    {State Exit : Type*} [Fintype State]
    (cycle : State → State → ℝ) (escape : State → Exit → ℝ)
    (u : State) (w : Exit) :
    markedOffspringKernel cycle escape 0 u w = escape u w := rfl

theorem markedOffspringKernel_succ
    {State Exit : Type*} [Fintype State]
    (cycle : State → State → ℝ) (escape : State → Exit → ℝ)
    (q : ℕ) (u : State) (w : Exit) :
    markedOffspringKernel cycle escape (q + 1) u w =
      ∑ v, cycle u v * markedOffspringKernel cycle escape q v w := rfl

/-- Exact one-step renewal identity for the unmarked endpoint kernel. -/
def IsRenewalKernel {State Exit : Type*} [Fintype State]
    (cycle : State → State → ℝ) (escape unmarked : State → Exit → ℝ) : Prop :=
  ∀ u w, unmarked u w = escape u w +
    kernelAction cycle (fun v ↦ unmarked v w) u

/-- A cycle transports the endpoint-conditioned unmarked kernel like a
Bernoulli-`1/2` success, up to the displayed relative error. -/
def HalfTransportComparison {State Exit : Type*} [Fintype State]
    (epsilon : ℝ) (cycle : State → State → ℝ)
    (unmarked : State → Exit → ℝ) : Prop :=
  ∀ u w,
    ((1 - epsilon) / 2) * unmarked u w ≤
        kernelAction cycle (fun v ↦ unmarked v w) u ∧
      kernelAction cycle (fun v ↦ unmarked v w) u ≤
        ((1 + epsilon) / 2) * unmarked u w

/-- Equivalent direct annular formulation: conditioned on the retained
outer endpoint, the final middle-to-outer escape has mass `1/2` up to the
same relative error. -/
def EscapeHalfComparison {State Exit : Type*}
    (epsilon : ℝ) (escape unmarked : State → Exit → ℝ) : Prop :=
  ∀ u w,
    ((1 - epsilon) / 2) * unmarked u w ≤ escape u w ∧
      escape u w ≤ ((1 + epsilon) / 2) * unmarked u w

/-- Endpoint-integrated one-gap kernel.  All intermediate boundary states,
including the final state of this gap, are summed internally; only the
entrance state remains as an argument for the surrounding stopped history. -/
def integratedMarkedOffspringKernel {State : Type*} [Fintype State]
    (cycle : State → State → ℝ) (escape : State → ℝ)
    (q : ℕ) (u : State) : ℝ :=
  markedOffspringKernel cycle (fun v (_ : Unit) ↦ escape v) q u ()

/-- Exact stochastic renewal equation after integrating the outer endpoint. -/
def IsStochasticRenewalRow {State : Type*} [Fintype State]
    (cycle : State → State → ℝ) (escape : State → ℝ) : Prop :=
  ∀ u, 1 = escape u + ∑ v, cycle u v

/-- The integrated completed-cycle row has mass `1/2`, up to relative
error.  Unlike fixed-endpoint Harnack, this is the valid consecutive-radius
A.6 comparison. -/
def HalfRowComparison {State : Type*} [Fintype State]
    (epsilon : ℝ) (cycle : State → State → ℝ) : Prop :=
  ∀ u, (1 - epsilon) / 2 ≤ ∑ v, cycle u v ∧
    ∑ v, cycle u v ≤ (1 + epsilon) / 2

/-- Under the exact renewal equation, comparing the escape piece with half
of the retained-endpoint kernel is equivalent to comparing the completed
cycle continuation with the other half.  This conditional fixed-endpoint
interface is useful only when a corresponding Poisson comparison is
available; consecutive-radius A.6 uses `HalfRowComparison` instead. -/
theorem halfTransportComparison_iff_escapeHalfComparison
    {State Exit : Type*} [Fintype State]
    {epsilon : ℝ} {cycle : State → State → ℝ}
    {escape unmarked : State → Exit → ℝ}
    (hrenewal : IsRenewalKernel cycle escape unmarked) :
    HalfTransportComparison epsilon cycle unmarked ↔
      EscapeHalfComparison epsilon escape unmarked := by
  constructor
  · intro htransport u w
    have hrenew := hrenewal u w
    have hbounds := htransport u w
    constructor <;> linarith
  · intro hescape u w
    have hrenew := hrenewal u w
    have hbounds := hescape u w
    constructor <;> linarith

lemma kernelAction_nonneg
    {State : Type*} [Fintype State]
    {cycle : State → State → ℝ} {f : State → ℝ}
    (hcycle : ∀ u v, 0 ≤ cycle u v) (hf : ∀ v, 0 ≤ f v) (u : State) :
    0 ≤ kernelAction cycle f u := by
  exact Finset.sum_nonneg fun v _ ↦ mul_nonneg (hcycle u v) (hf v)

lemma kernelAction_mono
    {State : Type*} [Fintype State]
    {cycle : State → State → ℝ} {f g : State → ℝ}
    (hcycle : ∀ u v, 0 ≤ cycle u v) (hfg : ∀ v, f v ≤ g v)
    (u : State) :
    kernelAction cycle f u ≤ kernelAction cycle g u := by
  exact Finset.sum_le_sum fun v _ ↦
    mul_le_mul_of_nonneg_left (hfg v) (hcycle u v)

lemma kernelAction_const_mul
    {State : Type*} [Fintype State]
    (cycle : State → State → ℝ) (c : ℝ) (f : State → ℝ)
    (u : State) :
    kernelAction cycle (fun v ↦ c * f v) u =
      c * kernelAction cycle f u := by
  unfold kernelAction
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  ring

lemma markedOffspringKernel_nonneg
    {State Exit : Type*} [Fintype State]
    {cycle : State → State → ℝ} {escape : State → Exit → ℝ}
    (hcycle : ∀ u v, 0 ≤ cycle u v)
    (hescape : ∀ u w, 0 ≤ escape u w) :
    ∀ q u w, 0 ≤ markedOffspringKernel cycle escape q u w := by
  intro q
  induction q with
  | zero => exact fun u w ↦ hescape u w
  | succ q ih =>
      intro u w
      rw [markedOffspringKernel_succ]
      exact kernelAction_nonneg hcycle (fun v ↦ ih v w) u

/-! ## Endpoint-conditioned geometric law -/

/-- Lower endpoint-conditioned geometric offspring estimate. -/
theorem markedOffspringKernel_lower
    {State Exit : Type*} [Fintype State]
    {epsilon : ℝ} {cycle : State → State → ℝ}
    {escape unmarked : State → Exit → ℝ}
    (_hepsilon0 : 0 ≤ epsilon) (hepsilon1 : epsilon ≤ 1)
    (hcycle : ∀ u v, 0 ≤ cycle u v)
    (_hunmarked : ∀ u w, 0 ≤ unmarked u w)
    (hrenewal : IsRenewalKernel cycle escape unmarked)
    (htransport : HalfTransportComparison epsilon cycle unmarked) :
    ∀ q u w,
      (1 - epsilon) ^ (q + 1) * halfGeometricMass q * unmarked u w ≤
        markedOffspringKernel cycle escape q u w := by
  intro q
  induction q with
  | zero =>
      intro u w
      have hrenew := hrenewal u w
      have hupper := (htransport u w).2
      rw [markedOffspringKernel_zero]
      simp only [halfGeometricMass]
      nlinarith [_hunmarked u w]
  | succ q ih =>
      intro u w
      rw [markedOffspringKernel_succ]
      let c : ℝ := (1 - epsilon) ^ (q + 1) * halfGeometricMass q
      have hc0 : 0 ≤ c := by
        exact mul_nonneg (pow_nonneg (sub_nonneg.mpr hepsilon1) _)
          (halfGeometricMass_nonneg q)
      calc
        (1 - epsilon) ^ (q + 1 + 1) * halfGeometricMass (q + 1) *
              unmarked u w =
            c * (((1 - epsilon) / 2) * unmarked u w) := by
              unfold c halfGeometricMass
              rw [pow_succ (1 - epsilon) (q + 1), pow_succ (1 / 2 : ℝ) (q + 1)]
              ring
        _ ≤ c * kernelAction cycle (fun v ↦ unmarked v w) u :=
          mul_le_mul_of_nonneg_left (htransport u w).1 hc0
        _ = kernelAction cycle (fun v ↦ c * unmarked v w) u := by
          rw [kernelAction_const_mul]
        _ ≤ kernelAction cycle
              (fun v ↦ markedOffspringKernel cycle escape q v w) u :=
          kernelAction_mono hcycle (fun v ↦ ih v w) u

/-- Upper endpoint-conditioned geometric offspring estimate. -/
theorem markedOffspringKernel_upper
    {State Exit : Type*} [Fintype State]
    {epsilon : ℝ} {cycle : State → State → ℝ}
    {escape unmarked : State → Exit → ℝ}
    (hepsilon0 : 0 ≤ epsilon)
    (hcycle : ∀ u v, 0 ≤ cycle u v)
    (_hunmarked : ∀ u w, 0 ≤ unmarked u w)
    (hrenewal : IsRenewalKernel cycle escape unmarked)
    (htransport : HalfTransportComparison epsilon cycle unmarked) :
    ∀ q u w,
      markedOffspringKernel cycle escape q u w ≤
        (1 + epsilon) ^ (q + 1) * halfGeometricMass q * unmarked u w := by
  intro q
  induction q with
  | zero =>
      intro u w
      have hrenew := hrenewal u w
      have hlower := (htransport u w).1
      rw [markedOffspringKernel_zero]
      simp only [halfGeometricMass]
      nlinarith [_hunmarked u w]
  | succ q ih =>
      intro u w
      rw [markedOffspringKernel_succ]
      let c : ℝ := (1 + epsilon) ^ (q + 1) * halfGeometricMass q
      have hc0 : 0 ≤ c := by
        exact mul_nonneg (pow_nonneg (by linarith) _)
          (halfGeometricMass_nonneg q)
      calc
        kernelAction cycle
            (fun v ↦ markedOffspringKernel cycle escape q v w) u ≤
            kernelAction cycle (fun v ↦ c * unmarked v w) u :=
          kernelAction_mono hcycle (fun v ↦ ih v w) u
        _ = c * kernelAction cycle (fun v ↦ unmarked v w) u :=
          kernelAction_const_mul cycle c (fun v ↦ unmarked v w) u
        _ ≤ c * (((1 + epsilon) / 2) * unmarked u w) :=
          mul_le_mul_of_nonneg_left (htransport u w).2 hc0
        _ = (1 + epsilon) ^ (q + 1 + 1) *
              halfGeometricMass (q + 1) * unmarked u w := by
          unfold c halfGeometricMass
          rw [pow_succ (1 + epsilon) (q + 1), pow_succ (1 / 2 : ℝ) (q + 1)]
          ring

theorem markedOffspringKernel_two_sided
    {State Exit : Type*} [Fintype State]
    {epsilon : ℝ} {cycle : State → State → ℝ}
    {escape unmarked : State → Exit → ℝ}
    (hepsilon0 : 0 ≤ epsilon) (hepsilon1 : epsilon ≤ 1)
    (hcycle : ∀ u v, 0 ≤ cycle u v)
    (hunmarked : ∀ u w, 0 ≤ unmarked u w)
    (hrenewal : IsRenewalKernel cycle escape unmarked)
    (htransport : HalfTransportComparison epsilon cycle unmarked)
    (q : ℕ) (u : State) (w : Exit) :
    (1 - epsilon) ^ (q + 1) * halfGeometricMass q * unmarked u w ≤
        markedOffspringKernel cycle escape q u w ∧
      markedOffspringKernel cycle escape q u w ≤
        (1 + epsilon) ^ (q + 1) * halfGeometricMass q * unmarked u w :=
  ⟨markedOffspringKernel_lower hepsilon0 hepsilon1 hcycle hunmarked
      hrenewal htransport q u w,
    markedOffspringKernel_upper hepsilon0 hcycle hunmarked hrenewal
      htransport q u w⟩

/-- With exact half-mass transport, the endpoint-retaining offspring law is
literally geometric; the retained endpoint is not summed out. -/
theorem markedOffspringKernel_eq_halfGeometricMass
    {State Exit : Type*} [Fintype State]
    {cycle : State → State → ℝ}
    {escape unmarked : State → Exit → ℝ}
    (hcycle : ∀ u v, 0 ≤ cycle u v)
    (hunmarked : ∀ u w, 0 ≤ unmarked u w)
    (hrenewal : IsRenewalKernel cycle escape unmarked)
    (htransport : HalfTransportComparison 0 cycle unmarked)
    (q : ℕ) (u : State) (w : Exit) :
    markedOffspringKernel cycle escape q u w =
      halfGeometricMass q * unmarked u w := by
  apply le_antisymm
  · simpa only [add_zero, one_pow, one_mul] using
      markedOffspringKernel_upper (epsilon := 0) le_rfl hcycle hunmarked
        hrenewal htransport q u w
  · simpa only [sub_zero, one_pow, one_mul] using
      markedOffspringKernel_lower (epsilon := 0) le_rfl zero_le_one
        hcycle hunmarked hrenewal htransport q u w

/-- Valid endpoint-integrated geometric comparison for one annular gap.
The random exit state is consumed by the stopped history rather than fixed
inside a pointwise Poisson-kernel ratio. -/
theorem integratedMarkedOffspringKernel_two_sided
    {State : Type*} [Fintype State]
    {epsilon : ℝ} {cycle : State → State → ℝ} {escape : State → ℝ}
    (hepsilon0 : 0 ≤ epsilon) (hepsilon1 : epsilon ≤ 1)
    (hcycle : ∀ u v, 0 ≤ cycle u v)
    (hrenewal : IsStochasticRenewalRow cycle escape)
    (hrow : HalfRowComparison epsilon cycle)
    (q : ℕ) (u : State) :
    (1 - epsilon) ^ (q + 1) * halfGeometricMass q ≤
        integratedMarkedOffspringKernel cycle escape q u ∧
      integratedMarkedOffspringKernel cycle escape q u ≤
        (1 + epsilon) ^ (q + 1) * halfGeometricMass q := by
  let unmarked : State → Unit → ℝ := fun _ _ ↦ 1
  let escape' : State → Unit → ℝ := fun v _ ↦ escape v
  have hrenewal' : IsRenewalKernel cycle escape' unmarked := by
    intro v _w
    simpa only [unmarked, escape', kernelAction, mul_one] using hrenewal v
  have htransport : HalfTransportComparison epsilon cycle unmarked := by
    intro v _w
    simpa only [unmarked, mul_one, kernelAction] using hrow v
  have hbounds := markedOffspringKernel_two_sided hepsilon0 hepsilon1
    hcycle (fun _ _ ↦ zero_le_one) hrenewal' htransport q u ()
  simpa only [integratedMarkedOffspringKernel, escape', unmarked, mul_one]
    using hbounds

/-- Exact geometric law for the endpoint-integrated gap when its completed
cycle row has exactly mass `1/2`. -/
theorem integratedMarkedOffspringKernel_eq_halfGeometricMass
    {State : Type*} [Fintype State]
    {cycle : State → State → ℝ} {escape : State → ℝ}
    (hcycle : ∀ u v, 0 ≤ cycle u v)
    (hrenewal : IsStochasticRenewalRow cycle escape)
    (hrow : HalfRowComparison 0 cycle)
    (q : ℕ) (u : State) :
    integratedMarkedOffspringKernel cycle escape q u =
      halfGeometricMass q := by
  exact le_antisymm
    (by simpa only [add_zero, one_pow, one_mul] using
      (integratedMarkedOffspringKernel_two_sided le_rfl zero_le_one
        hcycle hrenewal hrow q u).2)
    (by simpa only [sub_zero, one_pow, one_mul] using
      (integratedMarkedOffspringKernel_two_sided le_rfl zero_le_one
        hcycle hrenewal hrow q u).1)

/-! ## From row mass and Poisson Harnack to half transport -/

/-- The elementary annulus-exit estimate and endpoint Poisson Harnack imply
the half-transport hypothesis.  This is the exact interface at which the
two analytic estimates enter; the conclusion already has the arbitrary
retained outer endpoint `w`. -/
theorem halfTransportComparison_of_rowMass_of_endpointHarnack
    {State Exit : Type*} [Fintype State]
    {rowError endpointError : ℝ}
    {cycle : State → State → ℝ} {unmarked : State → Exit → ℝ}
    (hrowError0 : 0 ≤ rowError) (hrowError1 : rowError ≤ 1)
    (hendpointError0 : 0 ≤ endpointError)
    (hendpointError1 : endpointError ≤ 1)
    (hcycle : ∀ u v, 0 ≤ cycle u v)
    (hunmarked : ∀ u w, 0 ≤ unmarked u w)
    (hrow : ∀ u,
      (1 - rowError) / 2 ≤ ∑ v, cycle u v ∧
        ∑ v, cycle u v ≤ (1 + rowError) / 2)
    (hendpoint : ∀ u v w,
      (1 - endpointError) * unmarked u w ≤ unmarked v w ∧
        unmarked v w ≤ (1 + endpointError) * unmarked u w) :
    HalfTransportComparison
      (rowError + endpointError + rowError * endpointError)
      cycle unmarked := by
  intro u w
  let e := rowError + endpointError + rowError * endpointError
  have hrowLower0 : 0 ≤ (1 - rowError) / 2 := by positivity
  have hrowUpper0 : 0 ≤ (1 + rowError) / 2 := by positivity
  have hendpointLower0 : 0 ≤ 1 - endpointError :=
    sub_nonneg.mpr hendpointError1
  constructor
  · calc
      ((1 - e) / 2) * unmarked u w ≤
          (((1 - rowError) * (1 - endpointError)) / 2) *
            unmarked u w := by
        dsimp only [e]
        have hfactor : 1 - (rowError + endpointError + rowError * endpointError) ≤
            (1 - rowError) * (1 - endpointError) := by nlinarith
        exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hfactor (by norm_num))
          (hunmarked u w)
      _ = ((1 - rowError) / 2) *
          ((1 - endpointError) * unmarked u w) := by ring
      _ ≤ (∑ v, cycle u v) *
          ((1 - endpointError) * unmarked u w) :=
        mul_le_mul_of_nonneg_right (hrow u).1
          (mul_nonneg hendpointLower0 (hunmarked u w))
      _ = ∑ v, cycle u v *
          ((1 - endpointError) * unmarked u w) := by rw [Finset.sum_mul]
      _ ≤ ∑ v, cycle u v * unmarked v w := by
        exact Finset.sum_le_sum fun v _ ↦
          mul_le_mul_of_nonneg_left (hendpoint u v w).1 (hcycle u v)
  · calc
      ∑ v, cycle u v * unmarked v w ≤
          ∑ v, cycle u v * ((1 + endpointError) * unmarked u w) := by
        exact Finset.sum_le_sum fun v _ ↦
          mul_le_mul_of_nonneg_left (hendpoint u v w).2 (hcycle u v)
      _ = (∑ v, cycle u v) *
          ((1 + endpointError) * unmarked u w) := by rw [Finset.sum_mul]
      _ ≤ ((1 + rowError) / 2) *
          ((1 + endpointError) * unmarked u w) :=
        mul_le_mul_of_nonneg_right (hrow u).2
          (mul_nonneg (by linarith) (hunmarked u w))
      _ = ((1 + e) / 2) * unmarked u w := by
        dsimp only [e]
        ring

/-! ## Actual annular-kernel specialization -/

/-- Abstract endpoint-conditioned comparison for the actual
middle→inner→middle and escape kernels above.  It is useful when a genuine
fixed-endpoint Harnack estimate is available.  For consecutive HLOZ radii
the valid A.6 consumer is instead the endpoint-integrated row theorem below;
no such fixed-endpoint premise is asserted there. -/
theorem annularMarkedOffspringKernel_two_sided
    {Middle Inner Exit : Type*} [Fintype Middle] [Fintype Inner]
    (outer middle inner : Set Point)
    (middlePoint : Middle → Point) (innerPoint : Inner → Point)
    (exitPoint : Exit → Point)
    (rowError endpointError : ℝ)
    (hrowError0 : 0 ≤ rowError) (hrowError1 : rowError ≤ 1)
    (hendpointError0 : 0 ≤ endpointError)
    (hendpointError1 : endpointError ≤ 1)
    (hrenewal : IsRenewalKernel
      (annularCycleKernelReal outer middle inner middlePoint innerPoint)
      (annularEscapeKernelReal outer inner middlePoint exitPoint)
      (annularUnmarkedKernelReal outer middlePoint exitPoint))
    (hrow : ∀ u,
      (1 - rowError) / 2 ≤
          ∑ v, annularCycleKernelReal outer middle inner
            middlePoint innerPoint u v ∧
        ∑ v, annularCycleKernelReal outer middle inner
            middlePoint innerPoint u v ≤ (1 + rowError) / 2)
    (hendpoint : ∀ u v w,
      (1 - endpointError) *
          annularUnmarkedKernelReal outer middlePoint exitPoint u w ≤
        annularUnmarkedKernelReal outer middlePoint exitPoint v w ∧
      annularUnmarkedKernelReal outer middlePoint exitPoint v w ≤
        (1 + endpointError) *
          annularUnmarkedKernelReal outer middlePoint exitPoint u w)
    (hcombined : rowError + endpointError + rowError * endpointError ≤ 1)
    (q : ℕ) (u : Middle) (w : Exit) :
    let error := rowError + endpointError + rowError * endpointError
    (1 - error) ^ (q + 1) * halfGeometricMass q *
          annularUnmarkedKernelReal outer middlePoint exitPoint u w ≤
        markedOffspringKernel
          (annularCycleKernelReal outer middle inner middlePoint innerPoint)
          (annularEscapeKernelReal outer inner middlePoint exitPoint)
          q u w ∧
      markedOffspringKernel
          (annularCycleKernelReal outer middle inner middlePoint innerPoint)
          (annularEscapeKernelReal outer inner middlePoint exitPoint)
          q u w ≤
        (1 + error) ^ (q + 1) * halfGeometricMass q *
          annularUnmarkedKernelReal outer middlePoint exitPoint u w := by
  dsimp only
  let error := rowError + endpointError + rowError * endpointError
  have htransport : HalfTransportComparison error
      (annularCycleKernelReal outer middle inner middlePoint innerPoint)
      (annularUnmarkedKernelReal outer middlePoint exitPoint) :=
    halfTransportComparison_of_rowMass_of_endpointHarnack
      hrowError0 hrowError1 hendpointError0 hendpointError1
      (fun a b ↦ annularCycleKernelReal_nonneg
        outer middle inner middlePoint innerPoint a b)
      (fun a b ↦ annularUnmarkedKernelReal_nonneg
        outer middlePoint exitPoint a b)
      hrow hendpoint
  exact markedOffspringKernel_two_sided
    (by positivity) hcombined
    (fun a b ↦ annularCycleKernelReal_nonneg
      outer middle inner middlePoint innerPoint a b)
    (fun a b ↦ annularUnmarkedKernelReal_nonneg
      outer middlePoint exitPoint a b)
    hrenewal htransport q u w

/-- Conditional fixed-endpoint specialization.  Its sole analytic premise
is the displayed escape comparison; this theorem does not assert that the
premise holds for consecutive HLOZ radii. -/
theorem annularMarkedOffspringKernel_two_sided_of_escape
    {Middle Inner Exit : Type*} [Fintype Middle] [Fintype Inner]
    (outer middle inner : Set Point)
    (middlePoint : Middle → Point) (innerPoint : Inner → Point)
    (exitPoint : Exit → Point)
    (epsilon : ℝ) (hepsilon0 : 0 ≤ epsilon) (hepsilon1 : epsilon ≤ 1)
    (hrenewal : IsRenewalKernel
      (annularCycleKernelReal outer middle inner middlePoint innerPoint)
      (annularEscapeKernelReal outer inner middlePoint exitPoint)
      (annularUnmarkedKernelReal outer middlePoint exitPoint))
    (hescape : EscapeHalfComparison epsilon
      (annularEscapeKernelReal outer inner middlePoint exitPoint)
      (annularUnmarkedKernelReal outer middlePoint exitPoint))
    (q : ℕ) (u : Middle) (w : Exit) :
    (1 - epsilon) ^ (q + 1) * halfGeometricMass q *
          annularUnmarkedKernelReal outer middlePoint exitPoint u w ≤
        markedOffspringKernel
          (annularCycleKernelReal outer middle inner middlePoint innerPoint)
          (annularEscapeKernelReal outer inner middlePoint exitPoint)
          q u w ∧
      markedOffspringKernel
          (annularCycleKernelReal outer middle inner middlePoint innerPoint)
          (annularEscapeKernelReal outer inner middlePoint exitPoint)
          q u w ≤
        (1 + epsilon) ^ (q + 1) * halfGeometricMass q *
          annularUnmarkedKernelReal outer middlePoint exitPoint u w := by
  apply markedOffspringKernel_two_sided hepsilon0 hepsilon1
    (fun a b ↦ annularCycleKernelReal_nonneg
      outer middle inner middlePoint innerPoint a b)
    (fun a b ↦ annularUnmarkedKernelReal_nonneg
      outer middlePoint exitPoint a b)
    hrenewal
  exact (halfTransportComparison_iff_escapeHalfComparison hrenewal).2 hescape

/-- ENNReal lower form used directly by full complementary-skeleton
factorizations. -/
theorem annularMarkedOffspringKernel_ennreal_lower
    {Middle Inner Exit : Type*} [Fintype Middle] [Fintype Inner]
    (outer middle inner : Set Point)
    (middlePoint : Middle → Point) (innerPoint : Inner → Point)
    (exitPoint : Exit → Point)
    (rowError endpointError : ℝ)
    (hrowError0 : 0 ≤ rowError) (hrowError1 : rowError ≤ 1)
    (hendpointError0 : 0 ≤ endpointError)
    (hendpointError1 : endpointError ≤ 1)
    (hrenewal : IsRenewalKernel
      (annularCycleKernelReal outer middle inner middlePoint innerPoint)
      (annularEscapeKernelReal outer inner middlePoint exitPoint)
      (annularUnmarkedKernelReal outer middlePoint exitPoint))
    (hrow : ∀ u,
      (1 - rowError) / 2 ≤
          ∑ v, annularCycleKernelReal outer middle inner
            middlePoint innerPoint u v ∧
        ∑ v, annularCycleKernelReal outer middle inner
            middlePoint innerPoint u v ≤ (1 + rowError) / 2)
    (hendpoint : ∀ u v w,
      (1 - endpointError) *
          annularUnmarkedKernelReal outer middlePoint exitPoint u w ≤
        annularUnmarkedKernelReal outer middlePoint exitPoint v w ∧
      annularUnmarkedKernelReal outer middlePoint exitPoint v w ≤
        (1 + endpointError) *
          annularUnmarkedKernelReal outer middlePoint exitPoint u w)
    (hcombined : rowError + endpointError + rowError * endpointError ≤ 1)
    (q : ℕ) (u : Middle) (w : Exit) :
    let error := rowError + endpointError + rowError * endpointError
    ENNReal.ofReal ((1 - error) ^ (q + 1)) *
        ENNReal.ofReal (halfGeometricMass q) *
        annularUnmarkedKernel outer middlePoint exitPoint u w ≤
      ENNReal.ofReal
        (markedOffspringKernel
          (annularCycleKernelReal outer middle inner middlePoint innerPoint)
          (annularEscapeKernelReal outer inner middlePoint exitPoint)
          q u w) := by
  dsimp only
  have hreal := (annularMarkedOffspringKernel_two_sided
    outer middle inner middlePoint innerPoint exitPoint
    rowError endpointError hrowError0 hrowError1
    hendpointError0 hendpointError1 hrenewal hrow hendpoint hcombined q u w).1
  have herror1 : rowError + endpointError + rowError * endpointError ≤ 1 := hcombined
  have hfactor0 :
      0 ≤ (1 - (rowError + endpointError + rowError * endpointError)) ^ (q + 1) :=
    pow_nonneg (sub_nonneg.mpr herror1) _
  have hhalf0 : 0 ≤ halfGeometricMass q := halfGeometricMass_nonneg q
  have hof := ENNReal.ofReal_le_ofReal hreal
  rw [ENNReal.ofReal_mul (mul_nonneg hfactor0 hhalf0),
    ENNReal.ofReal_mul hfactor0] at hof
  have hunmarkedFinite :
      annularUnmarkedKernel outer middlePoint exitPoint u w ≠ ⊤ :=
    measure_ne_top fairSteps _
  simp only [annularUnmarkedKernelReal,
    ENNReal.ofReal_toReal hunmarkedFinite] at hof
  exact hof

/-! ## Weak compositions and the negative-binomial offspring law -/

/-- Joint marked mass for a fixed weak composition of `b` offspring among
`a` parent gaps.  Both endpoints of every erased gap remain fixed. -/
def offspringPatternKernel {State Exit : Type*} [Fintype State]
    {a b : ℕ} (cycle : Fin a → State → State → ℝ)
    (escape : Fin a → State → Exit → ℝ)
    (entrance : Fin a → State) (endpoint : Fin a → Exit)
    (g : GapPattern a b) : ℝ :=
  ∏ i, markedOffspringKernel (cycle i) (escape i)
    (gapMultiplicity g i) (entrance i) (endpoint i)

/-- Endpoint-integrated mass of a whole radial level word with one marked
gap per parent.  Intermediate gap endpoints are not frozen. -/
def integratedOffspringPatternKernel {State : Type*} [Fintype State]
    {a b : ℕ} (cycle : Fin a → State → State → ℝ)
    (escape : Fin a → State → ℝ) (entrance : Fin a → State)
    (g : GapPattern a b) : ℝ :=
  ∏ i, integratedMarkedOffspringKernel (cycle i) (escape i)
    (gapMultiplicity g i) (entrance i)

/-- Product lower comparison for one fixed weak composition. -/
theorem offspringPatternKernel_lower
    {State Exit : Type*} [Fintype State]
    {a b : ℕ} {epsilon : ℝ}
    {cycle : Fin a → State → State → ℝ}
    {escape unmarked : Fin a → State → Exit → ℝ}
    (hepsilon0 : 0 ≤ epsilon) (hepsilon1 : epsilon ≤ 1)
    (hcycle : ∀ i u v, 0 ≤ cycle i u v)
    (hunmarked : ∀ i u w, 0 ≤ unmarked i u w)
    (hrenewal : ∀ i, IsRenewalKernel (cycle i) (escape i) (unmarked i))
    (htransport : ∀ i, HalfTransportComparison epsilon (cycle i) (unmarked i))
    (entrance : Fin a → State) (endpoint : Fin a → Exit)
    (g : GapPattern a b) :
    (1 - epsilon) ^ (a + b) *
        (∏ i, halfGeometricMass (gapMultiplicity g i)) *
        (∏ i, unmarked i (entrance i) (endpoint i)) ≤
      offspringPatternKernel cycle escape entrance endpoint g := by
  have hpoint (i : Fin a) :
      (1 - epsilon) ^ (gapMultiplicity g i + 1) *
          halfGeometricMass (gapMultiplicity g i) *
          unmarked i (entrance i) (endpoint i) ≤
        markedOffspringKernel (cycle i) (escape i)
          (gapMultiplicity g i) (entrance i) (endpoint i) :=
    markedOffspringKernel_lower hepsilon0 hepsilon1 (hcycle i)
      (hunmarked i) (hrenewal i) (htransport i) _ _ _
  have hpower :
      ∏ i : Fin a, (1 - epsilon) ^ (gapMultiplicity g i + 1) =
        (1 - epsilon) ^ (a + b) := by
    calc
      (∏ i : Fin a, (1 - epsilon) ^ (gapMultiplicity g i + 1)) =
          (1 - epsilon) ^
            (∑ i : Fin a, (gapMultiplicity g i + 1)) := by
        simpa using Finset.prod_pow_eq_pow_sum (Finset.univ : Finset (Fin a))
          (fun i ↦ gapMultiplicity g i + 1) (1 - epsilon)
      _ = (1 - epsilon) ^ (a + b) := by
        congr 1
        rw [Finset.sum_add_distrib, sum_gapMultiplicity]
        simp [add_comm]
  calc
    (1 - epsilon) ^ (a + b) *
          (∏ i, halfGeometricMass (gapMultiplicity g i)) *
          (∏ i, unmarked i (entrance i) (endpoint i)) =
        ∏ i, ((1 - epsilon) ^ (gapMultiplicity g i + 1) *
          halfGeometricMass (gapMultiplicity g i) *
          unmarked i (entrance i) (endpoint i)) := by
      rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, hpower]
    _ ≤ ∏ i, markedOffspringKernel (cycle i) (escape i)
        (gapMultiplicity g i) (entrance i) (endpoint i) :=
      Finset.prod_le_prod
        (fun i _ ↦ mul_nonneg
          (mul_nonneg (pow_nonneg (sub_nonneg.mpr hepsilon1) _)
            (halfGeometricMass_nonneg _))
          (hunmarked i (entrance i) (endpoint i)))
        (fun i _ ↦ hpoint i)
    _ = offspringPatternKernel cycle escape entrance endpoint g := rfl

/-- Product upper comparison for one fixed weak composition. -/
theorem offspringPatternKernel_upper
    {State Exit : Type*} [Fintype State]
    {a b : ℕ} {epsilon : ℝ}
    {cycle : Fin a → State → State → ℝ}
    {escape unmarked : Fin a → State → Exit → ℝ}
    (hepsilon0 : 0 ≤ epsilon)
    (hcycle : ∀ i u v, 0 ≤ cycle i u v)
    (hescape : ∀ i u w, 0 ≤ escape i u w)
    (hunmarked : ∀ i u w, 0 ≤ unmarked i u w)
    (hrenewal : ∀ i, IsRenewalKernel (cycle i) (escape i) (unmarked i))
    (htransport : ∀ i, HalfTransportComparison epsilon (cycle i) (unmarked i))
    (entrance : Fin a → State) (endpoint : Fin a → Exit)
    (g : GapPattern a b) :
    offspringPatternKernel cycle escape entrance endpoint g ≤
      (1 + epsilon) ^ (a + b) *
        (∏ i, halfGeometricMass (gapMultiplicity g i)) *
        (∏ i, unmarked i (entrance i) (endpoint i)) := by
  have hpoint (i : Fin a) :
      markedOffspringKernel (cycle i) (escape i)
          (gapMultiplicity g i) (entrance i) (endpoint i) ≤
        (1 + epsilon) ^ (gapMultiplicity g i + 1) *
          halfGeometricMass (gapMultiplicity g i) *
          unmarked i (entrance i) (endpoint i) :=
    markedOffspringKernel_upper hepsilon0 (hcycle i)
      (hunmarked i) (hrenewal i) (htransport i) _ _ _
  have hpower :
      ∏ i : Fin a, (1 + epsilon) ^ (gapMultiplicity g i + 1) =
        (1 + epsilon) ^ (a + b) := by
    calc
      (∏ i : Fin a, (1 + epsilon) ^ (gapMultiplicity g i + 1)) =
          (1 + epsilon) ^
            (∑ i : Fin a, (gapMultiplicity g i + 1)) := by
        simpa using Finset.prod_pow_eq_pow_sum (Finset.univ : Finset (Fin a))
          (fun i ↦ gapMultiplicity g i + 1) (1 + epsilon)
      _ = (1 + epsilon) ^ (a + b) := by
        congr 1
        rw [Finset.sum_add_distrib, sum_gapMultiplicity]
        simp [add_comm]
  calc
    offspringPatternKernel cycle escape entrance endpoint g =
        ∏ i, markedOffspringKernel (cycle i) (escape i)
          (gapMultiplicity g i) (entrance i) (endpoint i) := rfl
    _ ≤ ∏ i, ((1 + epsilon) ^ (gapMultiplicity g i + 1) *
          halfGeometricMass (gapMultiplicity g i) *
          unmarked i (entrance i) (endpoint i)) :=
      Finset.prod_le_prod
        (fun i _ ↦ markedOffspringKernel_nonneg (hcycle i) (hescape i)
          _ _ _)
        (fun i _ ↦ hpoint i)
    _ = (1 + epsilon) ^ (a + b) *
          (∏ i, halfGeometricMass (gapMultiplicity g i)) *
          (∏ i, unmarked i (entrance i) (endpoint i)) := by
      rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, hpower]

/-- Whole-word lower comparison after integrating every intermediate radial
endpoint. -/
theorem integratedOffspringPatternKernel_lower
    {State : Type*} [Fintype State]
    {a b : ℕ} {epsilon : ℝ}
    {cycle : Fin a → State → State → ℝ}
    {escape : Fin a → State → ℝ}
    (hepsilon0 : 0 ≤ epsilon) (hepsilon1 : epsilon ≤ 1)
    (hcycle : ∀ i u v, 0 ≤ cycle i u v)
    (hrenewal : ∀ i, IsStochasticRenewalRow (cycle i) (escape i))
    (hrow : ∀ i, HalfRowComparison epsilon (cycle i))
    (entrance : Fin a → State) (g : GapPattern a b) :
    (1 - epsilon) ^ (a + b) *
        (∏ i, halfGeometricMass (gapMultiplicity g i)) ≤
      integratedOffspringPatternKernel cycle escape entrance g := by
  let escape' : Fin a → State → Unit → ℝ := fun i u _ ↦ escape i u
  let unmarked : Fin a → State → Unit → ℝ := fun _ _ _ ↦ 1
  have hrenewal' (i : Fin a) :
      IsRenewalKernel (cycle i) (escape' i) (unmarked i) := by
    intro u _w
    simpa only [escape', unmarked, kernelAction, mul_one] using hrenewal i u
  have htransport (i : Fin a) :
      HalfTransportComparison epsilon (cycle i) (unmarked i) := by
    intro u _w
    simpa only [unmarked, kernelAction, mul_one] using hrow i u
  have hbound := offspringPatternKernel_lower hepsilon0 hepsilon1 hcycle
    (fun _ _ _ ↦ zero_le_one) hrenewal' htransport entrance (fun _ ↦ ()) g
  simpa only [integratedOffspringPatternKernel, integratedMarkedOffspringKernel,
    offspringPatternKernel, escape', unmarked, Finset.prod_const_one, mul_one]
      using hbound

/-- Whole-word upper comparison after integrating every intermediate radial
endpoint. -/
theorem integratedOffspringPatternKernel_upper
    {State : Type*} [Fintype State]
    {a b : ℕ} {epsilon : ℝ}
    {cycle : Fin a → State → State → ℝ}
    {escape : Fin a → State → ℝ}
    (hepsilon0 : 0 ≤ epsilon)
    (hcycle : ∀ i u v, 0 ≤ cycle i u v)
    (hescape : ∀ i u, 0 ≤ escape i u)
    (hrenewal : ∀ i, IsStochasticRenewalRow (cycle i) (escape i))
    (hrow : ∀ i, HalfRowComparison epsilon (cycle i))
    (entrance : Fin a → State) (g : GapPattern a b) :
    integratedOffspringPatternKernel cycle escape entrance g ≤
      (1 + epsilon) ^ (a + b) *
        (∏ i, halfGeometricMass (gapMultiplicity g i)) := by
  let escape' : Fin a → State → Unit → ℝ := fun i u _ ↦ escape i u
  let unmarked : Fin a → State → Unit → ℝ := fun _ _ _ ↦ 1
  have hrenewal' (i : Fin a) :
      IsRenewalKernel (cycle i) (escape' i) (unmarked i) := by
    intro u _w
    simpa only [escape', unmarked, kernelAction, mul_one] using hrenewal i u
  have htransport (i : Fin a) :
      HalfTransportComparison epsilon (cycle i) (unmarked i) := by
    intro u _w
    simpa only [unmarked, kernelAction, mul_one] using hrow i u
  have hbound := offspringPatternKernel_upper hepsilon0 hcycle
    (fun i u _ ↦ hescape i u) (fun _ _ _ ↦ zero_le_one)
    hrenewal' htransport entrance (fun _ ↦ ()) g
  simpa only [integratedOffspringPatternKernel, integratedMarkedOffspringKernel,
    offspringPatternKernel, escape', unmarked, Finset.prod_const_one, mul_one]
      using hbound

/-- Exact product of geometric masses for an endpoint-integrated radial
level word. -/
theorem integratedOffspringPatternKernel_eq_geometric
    {State : Type*} [Fintype State]
    {a b : ℕ}
    {cycle : Fin a → State → State → ℝ}
    {escape : Fin a → State → ℝ}
    (hcycle : ∀ i u v, 0 ≤ cycle i u v)
    (hrenewal : ∀ i, IsStochasticRenewalRow (cycle i) (escape i))
    (hrow : ∀ i, HalfRowComparison 0 (cycle i))
    (entrance : Fin a → State) (g : GapPattern a b) :
    integratedOffspringPatternKernel cycle escape entrance g =
      ∏ i, halfGeometricMass (gapMultiplicity g i) := by
  apply Finset.prod_congr rfl
  intro i _hi
  exact integratedMarkedOffspringKernel_eq_halfGeometricMass
    (hcycle i) (hrenewal i) (hrow i)
      (gapMultiplicity g i) (entrance i)

/-- Summing the exact integrated whole-word masses gives the critical
negative-binomial transition law. -/
theorem sum_integratedOffspringPatternKernel_eq_transitionMass
    {State : Type*} [Fintype State]
    {a b : ℕ} (ha : 0 < a)
    {cycle : Fin a → State → State → ℝ}
    {escape : Fin a → State → ℝ}
    (hcycle : ∀ i u v, 0 ≤ cycle i u v)
    (hrenewal : ∀ i, IsStochasticRenewalRow (cycle i) (escape i))
    (hrow : ∀ i, HalfRowComparison 0 (cycle i))
    (entrance : Fin a → State) :
    ∑ g : GapPattern a b,
        integratedOffspringPatternKernel cycle escape entrance g =
      transitionMass a b := by
  simp_rw [integratedOffspringPatternKernel_eq_geometric
    hcycle hrenewal hrow entrance]
  exact (transitionMass_eq_sum_geometric_offspring ha b).symm

/-- Quantitative endpoint-integrated negative-binomial lower comparison. -/
theorem sum_integratedOffspringPatternKernel_lower
    {State : Type*} [Fintype State]
    {a b : ℕ} (ha : 0 < a) {epsilon : ℝ}
    {cycle : Fin a → State → State → ℝ}
    {escape : Fin a → State → ℝ}
    (hepsilon0 : 0 ≤ epsilon) (hepsilon1 : epsilon ≤ 1)
    (hcycle : ∀ i u v, 0 ≤ cycle i u v)
    (hrenewal : ∀ i, IsStochasticRenewalRow (cycle i) (escape i))
    (hrow : ∀ i, HalfRowComparison epsilon (cycle i))
    (entrance : Fin a → State) :
    (1 - epsilon) ^ (a + b) * transitionMass a b ≤
      ∑ g : GapPattern a b,
        integratedOffspringPatternKernel cycle escape entrance g := by
  rw [transitionMass_eq_sum_geometric_offspring ha b, Finset.mul_sum]
  exact Finset.sum_le_sum fun g _ ↦
    integratedOffspringPatternKernel_lower hepsilon0 hepsilon1
      hcycle hrenewal hrow entrance g

/-- Quantitative endpoint-integrated negative-binomial upper comparison. -/
theorem sum_integratedOffspringPatternKernel_upper
    {State : Type*} [Fintype State]
    {a b : ℕ} (ha : 0 < a) {epsilon : ℝ}
    {cycle : Fin a → State → State → ℝ}
    {escape : Fin a → State → ℝ}
    (hepsilon0 : 0 ≤ epsilon)
    (hcycle : ∀ i u v, 0 ≤ cycle i u v)
    (hescape : ∀ i u, 0 ≤ escape i u)
    (hrenewal : ∀ i, IsStochasticRenewalRow (cycle i) (escape i))
    (hrow : ∀ i, HalfRowComparison epsilon (cycle i))
    (entrance : Fin a → State) :
    ∑ g : GapPattern a b,
        integratedOffspringPatternKernel cycle escape entrance g ≤
      (1 + epsilon) ^ (a + b) * transitionMass a b := by
  rw [transitionMass_eq_sum_geometric_offspring ha b, Finset.mul_sum]
  exact Finset.sum_le_sum fun g _ ↦
    integratedOffspringPatternKernel_upper hepsilon0 hcycle hescape
      hrenewal hrow entrance g

/-- Exact product law for a fixed weak composition when every parent gap
has exact half-mass transport. -/
theorem offspringPatternKernel_eq_geometric
    {State Exit : Type*} [Fintype State]
    {a b : ℕ}
    {cycle : Fin a → State → State → ℝ}
    {escape unmarked : Fin a → State → Exit → ℝ}
    (hcycle : ∀ i u v, 0 ≤ cycle i u v)
    (hunmarked : ∀ i u w, 0 ≤ unmarked i u w)
    (hrenewal : ∀ i, IsRenewalKernel (cycle i) (escape i) (unmarked i))
    (htransport : ∀ i, HalfTransportComparison 0 (cycle i) (unmarked i))
    (entrance : Fin a → State) (endpoint : Fin a → Exit)
    (g : GapPattern a b) :
    offspringPatternKernel cycle escape entrance endpoint g =
      (∏ i, halfGeometricMass (gapMultiplicity g i)) *
        (∏ i, unmarked i (entrance i) (endpoint i)) := by
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _hi
  exact markedOffspringKernel_eq_halfGeometricMass
    (hcycle i) (hunmarked i) (hrenewal i) (htransport i)
      (gapMultiplicity g i) (entrance i) (endpoint i)

/-- Summing the fixed-composition bound gives the exact HLOZ
negative-binomial transition mass. -/
theorem sum_offspringPatternKernel_lower
    {State Exit : Type*} [Fintype State]
    {a b : ℕ} (ha : 0 < a) {epsilon : ℝ}
    {cycle : Fin a → State → State → ℝ}
    {escape unmarked : Fin a → State → Exit → ℝ}
    (hepsilon0 : 0 ≤ epsilon) (hepsilon1 : epsilon ≤ 1)
    (hcycle : ∀ i u v, 0 ≤ cycle i u v)
    (hunmarked : ∀ i u w, 0 ≤ unmarked i u w)
    (hrenewal : ∀ i, IsRenewalKernel (cycle i) (escape i) (unmarked i))
    (htransport : ∀ i, HalfTransportComparison epsilon (cycle i) (unmarked i))
    (entrance : Fin a → State) (endpoint : Fin a → Exit) :
    (1 - epsilon) ^ (a + b) * transitionMass a b *
        (∏ i, unmarked i (entrance i) (endpoint i)) ≤
      ∑ g : GapPattern a b,
        offspringPatternKernel cycle escape entrance endpoint g := by
  rw [transitionMass_eq_sum_geometric_offspring ha b]
  rw [Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_le_sum fun g _ ↦
    offspringPatternKernel_lower hepsilon0 hepsilon1 hcycle hunmarked
      hrenewal htransport entrance endpoint g

/-- Upper negative-binomial comparison after summing all weak
compositions. -/
theorem sum_offspringPatternKernel_upper
    {State Exit : Type*} [Fintype State]
    {a b : ℕ} (ha : 0 < a) {epsilon : ℝ}
    {cycle : Fin a → State → State → ℝ}
    {escape unmarked : Fin a → State → Exit → ℝ}
    (hepsilon0 : 0 ≤ epsilon)
    (hcycle : ∀ i u v, 0 ≤ cycle i u v)
    (hescape : ∀ i u w, 0 ≤ escape i u w)
    (hunmarked : ∀ i u w, 0 ≤ unmarked i u w)
    (hrenewal : ∀ i, IsRenewalKernel (cycle i) (escape i) (unmarked i))
    (htransport : ∀ i, HalfTransportComparison epsilon (cycle i) (unmarked i))
    (entrance : Fin a → State) (endpoint : Fin a → Exit) :
    ∑ g : GapPattern a b,
        offspringPatternKernel cycle escape entrance endpoint g ≤
      (1 + epsilon) ^ (a + b) * transitionMass a b *
        (∏ i, unmarked i (entrance i) (endpoint i)) := by
  rw [transitionMass_eq_sum_geometric_offspring ha b]
  rw [Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_le_sum fun g _ ↦
    offspringPatternKernel_upper hepsilon0 hcycle hescape hunmarked
      hrenewal htransport entrance endpoint g

/-- Exact negative-binomial offspring law, still conditioned on every
retained outer endpoint. -/
theorem sum_offspringPatternKernel_eq_transitionMass
    {State Exit : Type*} [Fintype State]
    {a b : ℕ} (ha : 0 < a)
    {cycle : Fin a → State → State → ℝ}
    {escape unmarked : Fin a → State → Exit → ℝ}
    (hcycle : ∀ i u v, 0 ≤ cycle i u v)
    (hunmarked : ∀ i u w, 0 ≤ unmarked i u w)
    (hrenewal : ∀ i, IsRenewalKernel (cycle i) (escape i) (unmarked i))
    (htransport : ∀ i, HalfTransportComparison 0 (cycle i) (unmarked i))
    (entrance : Fin a → State) (endpoint : Fin a → Exit) :
    ∑ g : GapPattern a b,
        offspringPatternKernel cycle escape entrance endpoint g =
      transitionMass a b *
        (∏ i, unmarked i (entrance i) (endpoint i)) := by
  simp_rw [offspringPatternKernel_eq_geometric hcycle hunmarked
    hrenewal htransport entrance endpoint]
  rw [← Finset.sum_mul, ← transitionMass_eq_sum_geometric_offspring ha b]

end

end Erdos1165.AnnularOffspringKernel
