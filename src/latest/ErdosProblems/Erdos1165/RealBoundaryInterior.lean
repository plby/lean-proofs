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

/-!
# The exact finite interior of a literal real-radius disc

The HLOZ radii are real.  The natural number `boxRadius` below is used only
to exhibit a finite carrier.  Under `0 ≤ R ≤ boxRadius`, membership in the
resulting finset is exactly membership in `D(0,R)` with its literal inner
vertex boundary removed.  In particular, the definition never rounds `R`.

The last part identifies the canonical first-hit endpoint event, and hence
`terminalSkeletonKernel`, with the usual exit mass from this finite domain.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Erdos1165.RealBoundaryInterior

open Annulus AnnulusHarnack GreenHarnack GreenProbability MarkedBoundaryVisitKernel
open PlanarPotential PotentialEuclideanGeometry RadialHarnackSpecialization
open TerminalSequentialVisitLaw ThickPoint

noncomputable section

/-! ## Finite realization of the literal graph interior -/

/-- The graph interior of the literal real-radius disc.  `boxRadius` is only
a finite carrier; `mem_realBoundaryInterior_iff` removes it from membership. -/
noncomputable def realBoundaryInterior (R : ℝ) (boxRadius : ℕ) : Finset Point :=
  by
    classical
    exact (coordinateBox boxRadius).filter fun z ↦
      z ∈ ThickPoint.disc 0 R ∧ z ∉ ThickPoint.discBoundary 0 R

@[simp] theorem mem_realBoundaryInterior_raw
    {R : ℝ} {boxRadius : ℕ} {z : Point} :
    z ∈ realBoundaryInterior R boxRadius ↔
      z ∈ coordinateBox boxRadius ∧
        z ∈ ThickPoint.disc 0 R ∧
          z ∉ ThickPoint.discBoundary 0 R := by
  simp [realBoundaryInterior]

/-- A point of `D(0,R)` lies in the finite carrier whenever
`R ≤ boxRadius`. -/
theorem disc_zero_subset_coordinateBox
    {R : ℝ} {boxRadius : ℕ} (_hR : 0 ≤ R)
    (hRbox : R ≤ (boxRadius : ℝ)) :
    ThickPoint.disc 0 R ⊆ (coordinateBox boxRadius : Set Point) := by
  intro z hz
  have hzRadius : euclideanRadius z ≤ R := by
    simpa [ThickPoint.disc, latticeDistance_zero_eq_euclideanRadius] using hz
  have hzClosed : z ∈ closedDisc boxRadius :=
    mem_closedDisc_of_euclideanRadius_le (hzRadius.trans hRbox)
  exact (mem_closedDisc boxRadius z).mp hzClosed |>.1

/-- Exact membership: the box is only a finiteness witness. -/
@[simp] theorem mem_realBoundaryInterior_iff
    {R : ℝ} {boxRadius : ℕ} (hR : 0 ≤ R)
    (hRbox : R ≤ (boxRadius : ℝ)) {z : Point} :
    z ∈ realBoundaryInterior R boxRadius ↔
      z ∈ ThickPoint.disc 0 R ∧
        z ∉ ThickPoint.discBoundary 0 R := by
  rw [mem_realBoundaryInterior_raw]
  constructor
  · exact fun hz ↦ hz.2
  · intro hz
    exact ⟨disc_zero_subset_coordinateBox hR hRbox hz.1, hz⟩

theorem realBoundaryInterior_subset_coordinateBox
    (R : ℝ) (boxRadius : ℕ) :
    realBoundaryInterior R boxRadius ⊆ coordinateBox boxRadius := by
  intro z hz
  exact (mem_realBoundaryInterior_raw.mp hz).1

private theorem adjacent_neighbor (x : Point) (d : Direction) :
    ThickPoint.Adjacent x (neighbor x d) := by
  rcases x with ⟨x1, x2⟩
  fin_cases d <;> simp [ThickPoint.Adjacent, neighbor, directionVector]

/-- Every neighbor of an interior point is either interior or on the literal
inner boundary. -/
theorem neighbor_mem_realBoundaryInterior_or_discBoundary
    {R : ℝ} {boxRadius : ℕ} (hR : 0 ≤ R)
    (hRbox : R ≤ (boxRadius : ℝ))
    {x : Point} (hx : x ∈ realBoundaryInterior R boxRadius)
    (d : Direction) :
    neighbor x d ∈ realBoundaryInterior R boxRadius ∨
      neighbor x d ∈ ThickPoint.discBoundary 0 R := by
  have hxData := (mem_realBoundaryInterior_iff hR hRbox).mp hx
  have hnDisc : neighbor x d ∈ ThickPoint.disc 0 R := by
    by_contra hnDisc
    apply hxData.2
    exact ⟨hxData.1, neighbor x d, hnDisc, adjacent_neighbor x d⟩
  by_cases hnBoundary : neighbor x d ∈ ThickPoint.discBoundary 0 R
  · exact Or.inr hnBoundary
  · exact Or.inl ((mem_realBoundaryInterior_iff hR hRbox).mpr
      ⟨hnDisc, hnBoundary⟩)

/-- The graph outer boundary is contained in the literal disc boundary. -/
theorem outerBoundary_realBoundaryInterior_subset_discBoundary
    {R : ℝ} {boxRadius : ℕ} (hR : 0 ≤ R)
    (hRbox : R ≤ (boxRadius : ℝ)) :
    ∀ {z}, z ∈ outerBoundary (realBoundaryInterior R boxRadius) →
      z ∈ ThickPoint.discBoundary 0 R := by
  intro z hz
  rw [mem_outerBoundary] at hz
  obtain ⟨hzNot, x, hx, d, rfl⟩ := hz
  exact (neighbor_mem_realBoundaryInterior_or_discBoundary
    hR hRbox hx d).resolve_left hzNot

/-- The finite interior is disjoint from any finite subset of the literal
boundary. -/
theorem realBoundaryInterior_disjoint_of_subset_discBoundary
    {R : ℝ} {boxRadius : ℕ} (hR : 0 ≤ R)
    (hRbox : R ≤ (boxRadius : ℝ)) (B : Finset Point)
    (hB : ↑B ⊆ ThickPoint.discBoundary 0 R) :
    Disjoint (realBoundaryInterior R boxRadius) B := by
  rw [Finset.disjoint_left]
  intro z hzD hzB
  exact ((mem_realBoundaryInterior_iff hR hRbox).mp hzD).2 (hB hzB)

theorem realBoundaryInterior_disjoint_singleton_of_mem_discBoundary
    {R : ℝ} {boxRadius : ℕ} (hR : 0 ≤ R)
    (hRbox : R ≤ (boxRadius : ℝ)) {exit : Point}
    (hexit : exit ∈ ThickPoint.discBoundary 0 R) :
    Disjoint (realBoundaryInterior R boxRadius) {exit} := by
  apply realBoundaryInterior_disjoint_of_subset_discBoundary hR hRbox
  intro z hz
  have hzEq : z = exit := by simpa using hz
  simpa [hzEq] using hexit

/-! ## Exact first-hit event and exit-mass bridge -/

private lemma absorbedPosition_eq_trajectoryFrom_of_absorbed_stays
    (D : Finset Point) (start : Point) (omega : StepPath) :
    ∀ n, (∀ k < n, absorbedPosition D start omega k ∈ D) →
      absorbedPosition D start omega n =
        PlanarPotential.trajectoryFrom start omega n := by
  intro n hstay
  induction n with
  | zero => simp [PlanarPotential.trajectoryFrom]
  | succ n ih =>
      rw [absorbedPosition_succ,
        absorbedStep_of_mem D (hstay n (Nat.lt_succ_self n)),
        ih (fun k hk ↦ hstay k (hk.trans (Nat.lt_succ_self n))),
        PlanarPotential.trajectoryFrom_succ]
      rfl

private lemma absorbedPosition_eq_trajectoryFrom_of_trajectory_stays
    (D : Finset Point) (start : Point) (omega : StepPath) :
    ∀ n, (∀ k < n, PlanarPotential.trajectoryFrom start omega k ∈ D) →
      absorbedPosition D start omega n =
        PlanarPotential.trajectoryFrom start omega n := by
  intro n hstay
  induction n with
  | zero => simp [PlanarPotential.trajectoryFrom]
  | succ n ih =>
      rw [absorbedPosition_succ,
        ih (fun k hk ↦ hstay k (hk.trans (Nat.lt_succ_self n))),
        absorbedStep_of_mem D (hstay n (Nat.lt_succ_self n)),
        PlanarPotential.trajectoryFrom_succ]
      rfl

private lemma trajectoryFrom_mem_realBoundaryInterior_before_firstBoundary
    {R : ℝ} {boxRadius : ℕ} (hR : 0 ≤ R)
    (hRbox : R ≤ (boxRadius : ℝ))
    {start : Point} (hstart : start ∈ realBoundaryInterior R boxRadius)
    {omega : StepPath} {N : ℕ}
    (hfirst : AbsoluteBoundaryFirstAt
      (ThickPoint.discBoundary 0 R) start omega N) :
    ∀ k < N, PlanarPotential.trajectoryFrom start omega k ∈
      realBoundaryInterior R boxRadius := by
  intro k hk
  induction k with
  | zero => simpa only [PlanarPotential.trajectoryFrom_zero] using hstart
  | succ k ih =>
      have hkN : k < N := (Nat.lt_succ_self k).trans hk
      have hprev := ih hkN
      have hcases := neighbor_mem_realBoundaryInterior_or_discBoundary
        hR hRbox hprev (omega k)
      have hstep : PlanarPotential.trajectoryFrom start omega (k + 1) =
          neighbor (PlanarPotential.trajectoryFrom start omega k) (omega k) := by
        rw [PlanarPotential.trajectoryFrom_succ]
        rfl
      rw [hstep]
      exact hcases.resolve_right (by
        rw [← hstep]
        exact hfirst.2 (k + 1) hk)

/-- For a fixed endpoint on the literal real-radius boundary, the canonical
first-boundary-hit event is exactly the increasing union of absorbed exit
events from the finite graph interior. -/
theorem boundaryExitEndpointSteps_discBoundary_eq_absorbedExit
    {R : ℝ} {boxRadius : ℕ} (hR : 0 ≤ R)
    (hRbox : R ≤ (boxRadius : ℝ)) {start exit : Point}
    (hstart : start ∈ realBoundaryInterior R boxRadius)
    (hexit : exit ∈ ThickPoint.discBoundary 0 R) :
    boundaryExitEndpointSteps (ThickPoint.discBoundary 0 R) start exit =
      ⋃ n : ℕ, absorbedExitAt
        (realBoundaryInterior R boxRadius) {exit} n start := by
  let D := realBoundaryInterior R boxRadius
  ext omega
  simp only [boundaryExitEndpointSteps, mem_iUnion, mem_ofPred_eq,
    absorbedExitAt]
  constructor
  · rintro ⟨N, hfirst, hendpoint⟩
    have hstay : ∀ k < N,
        PlanarPotential.trajectoryFrom start omega k ∈ D :=
      trajectoryFrom_mem_realBoundaryInterior_before_firstBoundary
        hR hRbox hstart hfirst
    have heq := absorbedPosition_eq_trajectoryFrom_of_trajectory_stays
      D start omega N hstay
    refine ⟨N, ?_⟩
    rw [heq, hendpoint]
    simp
  · rintro ⟨n, hn⟩
    have hnEndpoint : absorbedPosition D start omega n = exit := by
      simpa only [Finset.mem_singleton] using hn
    have hexitNotD : exit ∉ D := by
      exact fun hmem ↦
        ((mem_realBoundaryInterior_iff hR hRbox).mp hmem).2 hexit
    let P : ℕ → Prop := fun q ↦ absorbedPosition D start omega q ∉ D
    have hP : ∃ q, P q := ⟨n, by simpa [P, hnEndpoint] using hexitNotD⟩
    let q := Nat.find hP
    have hqNot : absorbedPosition D start omega q ∉ D := Nat.find_spec hP
    have hqle : q ≤ n := Nat.find_min' hP
      (by simpa [P, hnEndpoint] using hexitNotD)
    have hbefore : ∀ k < q, absorbedPosition D start omega k ∈ D := by
      intro k hk
      by_contra hkNot
      exact (Nat.find_min hP hk) hkNot
    have hqne : q ≠ 0 := by
      intro hq0
      apply hqNot
      rw [hq0]
      simpa [D] using hstart
    obtain ⟨r, hqr⟩ := Nat.exists_eq_succ_of_ne_zero hqne
    rw [hqr] at hqNot hqle hbefore
    have hqNot' : absorbedPosition D start omega (r + 1) ∉ D := by
      simpa [Nat.succ_eq_add_one] using hqNot
    have hqle' : r + 1 ≤ n := by
      simpa [Nat.succ_eq_add_one] using hqle
    have hbefore' : ∀ k < r + 1, absorbedPosition D start omega k ∈ D := by
      intro k hk
      exact hbefore k (by simpa [Nat.succ_eq_add_one] using hk)
    have hrMem : absorbedPosition D start omega r ∈ D :=
      hbefore' r (Nat.lt_succ_self r)
    have houter : absorbedPosition D start omega (r + 1) ∈ outerBoundary D :=
      absorbedPosition_exit_mem_outerBoundary D start omega hrMem hqNot'
    have hboundary : absorbedPosition D start omega (r + 1) ∈
        ThickPoint.discBoundary 0 R :=
      outerBoundary_realBoundaryInterior_subset_discBoundary hR hRbox houter
    have hstable := absorbedPosition_stable_after_exit D start omega hqNot'
      (n - (r + 1))
    rw [Nat.add_sub_of_le hqle'] at hstable
    have hqEndpoint : absorbedPosition D start omega (r + 1) = exit :=
      hstable.symm.trans hnEndpoint
    have hqTrajectory := absorbedPosition_eq_trajectoryFrom_of_absorbed_stays
      D start omega (r + 1) hbefore'
    refine ⟨r + 1, ⟨?_, ?_⟩, ?_⟩
    · rw [← hqTrajectory]
      exact hboundary
    · intro k hk
      have hkD := hbefore' k hk
      have hkTrajectory := absorbedPosition_eq_trajectoryFrom_of_absorbed_stays
        D start omega k (fun j hj ↦ hbefore' j (hj.trans hk))
      rw [← hkTrajectory]
      exact ((mem_realBoundaryInterior_iff hR hRbox).mp hkD).2
    · rw [← hqTrajectory]
      exact hqEndpoint

/-- Exact fixed-endpoint event probability for the real-radius boundary. -/
theorem fairSteps_boundaryExitEndpointSteps_discBoundary_eq_exitMass
    {R : ℝ} {boxRadius : ℕ} (hR : 0 ≤ R)
    (hRbox : R ≤ (boxRadius : ℝ)) {start exit : Point}
    (hstart : start ∈ realBoundaryInterior R boxRadius)
    (hexit : exit ∈ ThickPoint.discBoundary 0 R) :
    fairSteps (boundaryExitEndpointSteps
        (ThickPoint.discBoundary 0 R) start exit) =
      exitMass (realBoundaryInterior R boxRadius) {exit} start := by
  rw [boundaryExitEndpointSteps_discBoundary_eq_absorbedExit
    hR hRbox hstart hexit]
  exact fairSteps_iUnion_absorbedExitAt_eq_exitMass _ _
    (realBoundaryInterior_disjoint_singleton_of_mem_discBoundary
      hR hRbox hexit) start

/-- The canonical unmarked terminal skeleton kernel is exactly the standard
finite-domain exit mass at the prescribed endpoint. -/
theorem terminalSkeletonKernel_discBoundary_eq_exitMass
    {R : ℝ} {boxRadius : ℕ} (hR : 0 ≤ R)
    (hRbox : R ≤ (boxRadius : ℝ)) {start exit : Point}
    (hstart : start ∈ realBoundaryInterior R boxRadius)
    (hexit : exit ∈ ThickPoint.discBoundary 0 R) :
    terminalSkeletonKernel (ThickPoint.discBoundary 0 R) start exit =
      exitMass (realBoundaryInterior R boxRadius) {exit} start := by
  exact fairSteps_boundaryExitEndpointSteps_discBoundary_eq_exitMass
    hR hRbox hstart hexit

end

end Erdos1165.RealBoundaryInterior
