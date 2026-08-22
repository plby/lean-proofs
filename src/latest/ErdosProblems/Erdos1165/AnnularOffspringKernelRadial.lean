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

import ErdosProblems.Erdos1165.AnnularOffspringKernel
import ErdosProblems.Erdos1165.AnnularOffspringRenewal
import ErdosProblems.Erdos1165.AnnularIntegratedRenewal
import ErdosProblems.Erdos1165.LiteralRealAnnulus
import ErdosProblems.Erdos1165.LiteralRealBoundaryPotential
import ErdosProblems.Erdos1165.LiteralRealAnnulusRadialExit
import ErdosProblems.Erdos1165.RealDiscFinite

/-!
# The literal radial row estimate for one Appendix-A.6 offspring cycle

This file specializes the endpoint-retaining offspring kernel to the three
literal real radii in one HLOZ profile transition.  Natural-number boxes are
used only as finite carriers.  Every stopped event continues to use the
unrounded sets `discBoundary x (scaleRadius n k)`.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace Erdos1165.AnnularOffspringKernelRadial

open Annulus AnnulusHarnack AnnularOffspringKernel
open AnnularIntegratedRenewal AnnularOffspringRenewal
open AnnularProfileClocks
open BoundaryVisitRegeneration
open BoundaryVisitLaw
open GreenHarnack GreenProbability
open MarkedBoundaryVisitKernel PotentialEuclideanGeometry
open PlanarPotential
open RealBoundaryInterior
open RealDiscFinite
open TerminalSequentialVisitLaw ThickPoint

noncomputable section

/-- Canonical finite subtype of a literal real-radius boundary. -/
abbrev BoundaryFinsetPoint (center : Point) (radius : ℝ) :=
  ↑(discBoundaryFinset center radius)

theorem enumeratesBoundary_boundaryFinsetPoint
    (center : Point) (radius : ℝ) :
    EnumeratesBoundary
      (fun z : BoundaryFinsetPoint center radius ↦ z.1)
      (ThickPoint.discBoundary center radius) := by
  constructor
  · exact Subtype.val_injective
  · intro y
    constructor
    · intro hy
      exact ⟨⟨y, mem_discBoundaryFinset.mpr hy⟩, rfl⟩
    · rintro ⟨z, rfl⟩
      exact mem_discBoundaryFinset.mp z.2

/-! ## Total mass of a recurrent literal boundary hit -/

private theorem relativeBoundary_nonempty
    {boundary : Set Point} (hboundary : boundary.Nonempty) (start : Point) :
    (relativeBoundary boundary start).Nonempty := by
  obtain ⟨z, hz⟩ := hboundary
  refine ⟨z - start, ?_⟩
  change start + (z - start) ∈ boundary
  simpa [add_comm, add_left_comm, add_assoc] using hz

theorem fairSteps_boundaryExitMarkedSteps_univ_eq_one
    {boundary : Set Point} (hboundary : boundary.Nonempty) (start : Point) :
    fairSteps (boundaryExitMarkedSteps boundary Set.univ start) = 1 := by
  have hrelative := relativeBoundary_nonempty hboundary start
  have hfinite : ∀ᵐ omega ∂fairSteps,
      boundaryExitTime boundary start omega < ⊤ := by
    filter_upwards
        [TerminalExcursionBridge.ae_frequentlyVisitsSet_of_nonempty hrelative]
        with omega homega
    exact TerminalExcursionBridge.firstHitSetAfter_lt_top_of_frequently
      (by simp [zeroClock]) homega
  have hmem : ∀ᵐ omega ∂fairSteps,
      omega ∈ boundaryExitMarkedSteps boundary Set.univ start := by
    filter_upwards [hfinite] with omega homega
    exact ⟨homega, Set.mem_univ _⟩
  exact (mem_ae_iff_prob_eq_one
    (measurableSet_boundaryExitMarkedSteps boundary Set.univ start)).mp hmem

/-- The singleton endpoint atoms over the canonical finite boundary subtype
exhaust the unmarked recurrent boundary hit. -/
theorem biUnion_boundaryExitEndpointSteps_eq_marked_univ
    (boundary : Set Point) (start : Point)
    (hboundaryFinite : boundary.Finite) :
    (⋃ z ∈ hboundaryFinite.toFinset,
        boundaryExitEndpointSteps boundary start z) =
      boundaryExitMarkedSteps boundary Set.univ start := by
  ext omega
  constructor
  · intro homega
    simp only [Set.mem_iUnion] at homega
    obtain ⟨z, hz⟩ := homega
    obtain ⟨hzmem, hzatom⟩ := hz
    obtain ⟨N, hfirst, hend⟩ := Set.mem_iUnion.mp hzatom
    exact (mem_boundaryExitMarkedSteps_iff_exists_first
      boundary Set.univ start omega).2 ⟨N, hfirst, Set.mem_univ _⟩
  · intro homega
    obtain ⟨N, hfirst, _hend⟩ :=
      (mem_boundaryExitMarkedSteps_iff_exists_first
        boundary Set.univ start omega).1 homega
    let z : Point := PlanarPotential.trajectoryFrom start omega N
    have hzboundary : z ∈ boundary := hfirst.1
    have hzfin : z ∈ hboundaryFinite.toFinset := by
      simpa using hzboundary
    simp only [Set.mem_iUnion]
    exact ⟨z, hzfin, Set.mem_iUnion.mpr ⟨N, hfirst, rfl⟩⟩

/-- Summing the exact endpoint kernels over every vertex of a nonempty
finite boundary gives total mass one. -/
theorem sum_skeletonExitKernel_toReal_eq_one
    {boundary : Set Point} (hboundaryFinite : boundary.Finite)
    (hboundary : boundary.Nonempty) (start : Point) :
    ∑ z ∈ hboundaryFinite.toFinset,
        (skeletonExitKernel boundary start z).toReal = 1 := by
  have hdisjoint : Set.PairwiseDisjoint
      (hboundaryFinite.toFinset : Set Point)
      (fun z ↦ boundaryExitEndpointSteps boundary start z) := by
    intro z _hz w _hw hzw
    change Disjoint (boundaryExitEndpointSteps boundary start z)
      (boundaryExitEndpointSteps boundary start w)
    rw [Set.disjoint_left]
    intro omega hzmem hwmem
    obtain ⟨Nz, hzfirst, hzend⟩ := Set.mem_iUnion.mp hzmem
    obtain ⟨Nw, hwfirst, hwend⟩ := Set.mem_iUnion.mp hwmem
    have hN : Nz = Nw := by
      rcases lt_trichotomy Nz Nw with hlt | heq | hgt
      · exact (hwfirst.2 Nz hlt hzfirst.1).elim
      · exact heq
      · exact (hzfirst.2 Nw hgt hwfirst.1).elim
    apply hzw
    rw [← hzend, ← hwend, hN]
  have hmeasure :
      fairSteps (⋃ z ∈ hboundaryFinite.toFinset,
          boundaryExitEndpointSteps boundary start z) =
        ∑ z ∈ hboundaryFinite.toFinset,
          fairSteps (boundaryExitEndpointSteps boundary start z) := by
    exact measure_biUnion_finset hdisjoint
      (fun z _hz ↦ measurableSet_boundaryExitEndpointSteps boundary start z)
  have hsumENN :
      (∑ z ∈ hboundaryFinite.toFinset,
          skeletonExitKernel boundary start z) = 1 := by
    simp_rw [skeletonExitKernel_eq_canonical]
    rw [← hmeasure, biUnion_boundaryExitEndpointSteps_eq_marked_univ
      boundary start hboundaryFinite,
      fairSteps_boundaryExitMarkedSteps_univ_eq_one hboundary start]
  calc
    (∑ z ∈ hboundaryFinite.toFinset,
        (skeletonExitKernel boundary start z).toReal) =
        (∑ z ∈ hboundaryFinite.toFinset,
          skeletonExitKernel boundary start z).toReal :=
      (ENNReal.toReal_sum (fun z _hz ↦ by
        unfold skeletonExitKernel skeletonExitMarkKernel
        exact measure_ne_top fairSteps _)).symm
    _ = 1 := by rw [hsumENN]; norm_num

/-! ## Exact first-hit/absorbed-exit bridge -/

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

private theorem trajectoryFrom_mem_before_firstBoundary
    (D : Finset Point) (boundary : Set Point)
    (houter : ↑(outerBoundary D) ⊆ boundary)
    {start : Point} (hstart : start ∈ D)
    {omega : StepPath} {N : ℕ}
    (hfirst : AbsoluteBoundaryFirstAt boundary start omega N) :
    ∀ k < N, PlanarPotential.trajectoryFrom start omega k ∈ D := by
  intro k hk
  induction k with
  | zero => simpa only [PlanarPotential.trajectoryFrom_zero] using hstart
  | succ k ih =>
      have hkN : k < N := (Nat.lt_succ_self k).trans hk
      have hprev := ih hkN
      by_cases hnext : PlanarPotential.trajectoryFrom start omega (k + 1) ∈ D
      · exact hnext
      · exfalso
        apply hfirst.2 (k + 1) hk
        apply houter
        change PlanarPotential.trajectoryFrom start omega (k + 1) ∈
          outerBoundary D
        rw [mem_outerBoundary]
        refine ⟨hnext, PlanarPotential.trajectoryFrom start omega k,
          hprev, omega k, ?_⟩
        rw [PlanarPotential.trajectoryFrom_succ]
        rfl

/-- If a literal stopped boundary contains the graph outer boundary and is
disjoint from the graph interior, its marked first-hit event is exactly the
increasing absorbed-exit event of the finite graph. -/
theorem boundaryExitMarkedSteps_eq_iUnion_absorbedExitAt
    (D : Finset Point) (boundary : Set Point) (B : Finset Point)
    {start : Point} (hstart : start ∈ D)
    (houter : ↑(outerBoundary D) ⊆ boundary)
    (hDboundary : ∀ z, z ∈ D → z ∉ boundary)
    (hDB : Disjoint D B) :
    boundaryExitMarkedSteps boundary (↑B : Set Point) start =
      ⋃ n : ℕ, absorbedExitAt D B n start := by
  ext omega
  simp only [mem_iUnion, absorbedExitAt]
  constructor
  · intro homega
    obtain ⟨N, hfirst, hend⟩ :=
      (mem_boundaryExitMarkedSteps_iff_exists_first
        boundary (↑B : Set Point) start omega).1 homega
    have hstay : ∀ k < N,
        PlanarPotential.trajectoryFrom start omega k ∈ D :=
      trajectoryFrom_mem_before_firstBoundary D boundary houter
        hstart hfirst
    have heq := absorbedPosition_eq_trajectoryFrom_of_trajectory_stays
      D start omega N hstay
    refine ⟨N, ?_⟩
    change absorbedPosition D start omega N ∈ B
    rw [heq]
    exact hend
  · rintro ⟨n, hn⟩
    have hnNotD : absorbedPosition D start omega n ∉ D := by
      intro hnD
      exact Finset.disjoint_left.mp hDB hnD hn
    let P : ℕ → Prop := fun q ↦ absorbedPosition D start omega q ∉ D
    have hP : ∃ q, P q := ⟨n, hnNotD⟩
    let q := Nat.find hP
    have hqNot : absorbedPosition D start omega q ∉ D := Nat.find_spec hP
    have hqle : q ≤ n := Nat.find_min' hP hnNotD
    have hbefore : ∀ k < q, absorbedPosition D start omega k ∈ D := by
      intro k hk
      by_contra hkNot
      exact (Nat.find_min hP hk) hkNot
    have hqne : q ≠ 0 := by
      intro hq0
      apply hqNot
      rw [hq0]
      simpa using hstart
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
    have hboundary : absorbedPosition D start omega (r + 1) ∈ boundary :=
      houter (absorbedPosition_exit_mem_outerBoundary
        D start omega hrMem hqNot')
    have hstable := absorbedPosition_stable_after_exit D start omega hqNot'
      (n - (r + 1))
    rw [Nat.add_sub_of_le hqle'] at hstable
    have hqB : absorbedPosition D start omega (r + 1) ∈ B := by
      change absorbedPosition D start omega n ∈ B at hn
      rw [← hstable]
      exact hn
    have hqTrajectory := absorbedPosition_eq_trajectoryFrom_of_absorbed_stays
      D start omega (r + 1) hbefore'
    apply (mem_boundaryExitMarkedSteps_iff_exists_first
      boundary (↑B : Set Point) start omega).2
    refine ⟨r + 1, ⟨?_, ?_⟩, ?_⟩
    · rw [← hqTrajectory]
      exact hboundary
    · intro k hk
      have hkD := hbefore' k hk
      have hkTrajectory := absorbedPosition_eq_trajectoryFrom_of_absorbed_stays
        D start omega k (fun j hj ↦ hbefore' j (hj.trans hk))
      rw [← hkTrajectory]
      exact hDboundary _ hkD
    · rw [← hqTrajectory]
      exact hqB

/-- Probability form of `boundaryExitMarkedSteps_eq_iUnion_absorbedExitAt`. -/
theorem fairSteps_boundaryExitMarkedSteps_eq_exitMass
    (D : Finset Point) (boundary : Set Point) (B : Finset Point)
    {start : Point} (hstart : start ∈ D)
    (houter : ↑(outerBoundary D) ⊆ boundary)
    (hDboundary : ∀ z, z ∈ D → z ∉ boundary)
    (hDB : Disjoint D B) :
    fairSteps (boundaryExitMarkedSteps boundary (↑B : Set Point) start) =
      exitMass D B start := by
  rw [boundaryExitMarkedSteps_eq_iUnion_absorbedExitAt
    D boundary B hstart houter hDboundary hDB]
  exact fairSteps_iUnion_absorbedExitAt_eq_exitMass D B hDB start

/-- A finite sum of canonical endpoint kernels is exactly the probability
of the corresponding finite endpoint mark. -/
theorem sum_skeletonExitKernel_finset_toReal_eq_marked
    (boundary : Set Point) (B : Finset Point) (start : Point) :
    (∑ z ∈ B, (skeletonExitKernel boundary start z).toReal) =
      (fairSteps
        (boundaryExitMarkedSteps boundary (↑B : Set Point) start)).toReal := by
  have hunion :
      (⋃ z ∈ B, boundaryExitEndpointSteps boundary start z) =
        boundaryExitMarkedSteps boundary (↑B : Set Point) start := by
    ext omega
    constructor
    · intro homega
      simp only [Set.mem_iUnion] at homega
      obtain ⟨z, hzB, hzatom⟩ := homega
      obtain ⟨N, hfirst, hend⟩ := Set.mem_iUnion.mp hzatom
      apply (mem_boundaryExitMarkedSteps_iff_exists_first
        boundary (↑B : Set Point) start omega).2
      exact ⟨N, hfirst, by simpa [hend] using hzB⟩
    · intro homega
      obtain ⟨N, hfirst, hend⟩ :=
        (mem_boundaryExitMarkedSteps_iff_exists_first
          boundary (↑B : Set Point) start omega).1 homega
      simp only [Set.mem_iUnion]
      exact ⟨PlanarPotential.trajectoryFrom start omega N, hend,
        Set.mem_iUnion.mpr ⟨N, hfirst, rfl⟩⟩
  have hdisjoint : Set.PairwiseDisjoint (↑B : Set Point)
      (fun z ↦ boundaryExitEndpointSteps boundary start z) := by
    intro z _hz w _hw hzw
    change Disjoint (boundaryExitEndpointSteps boundary start z)
      (boundaryExitEndpointSteps boundary start w)
    rw [Set.disjoint_left]
    intro omega hzmem hwmem
    obtain ⟨Nz, hzfirst, hzend⟩ := Set.mem_iUnion.mp hzmem
    obtain ⟨Nw, hwfirst, hwend⟩ := Set.mem_iUnion.mp hwmem
    have hN : Nz = Nw := by
      rcases lt_trichotomy Nz Nw with hlt | heq | hgt
      · exact (hwfirst.2 Nz hlt hzfirst.1).elim
      · exact heq
      · exact (hzfirst.2 Nw hgt hwfirst.1).elim
    apply hzw
    rw [← hzend, ← hwend, hN]
  have hmeasure :
      fairSteps (⋃ z ∈ B,
          boundaryExitEndpointSteps boundary start z) =
        ∑ z ∈ B, fairSteps
          (boundaryExitEndpointSteps boundary start z) := by
    exact measure_biUnion_finset hdisjoint
      (fun z _hz ↦ measurableSet_boundaryExitEndpointSteps boundary start z)
  calc
    (∑ z ∈ B, (skeletonExitKernel boundary start z).toReal) =
        (∑ z ∈ B, skeletonExitKernel boundary start z).toReal :=
      (ENNReal.toReal_sum (fun z _hz ↦ by
        unfold skeletonExitKernel skeletonExitMarkKernel
        exact measure_ne_top fairSteps _)).symm
    _ = (fairSteps (⋃ z ∈ B,
          boundaryExitEndpointSteps boundary start z)).toReal := by
      simp_rw [skeletonExitKernel_eq_canonical]
      rw [hmeasure]
    _ = _ := by rw [hunion]

/-- Subtype form of the preceding finite marked-row identity. -/
theorem sum_skeletonExitKernel_boundaryFinsetPoint_eq_marked
    (boundary : Set Point) (center : Point) (radius : ℝ) (start : Point) :
    (∑ z : BoundaryFinsetPoint center radius,
        (skeletonExitKernel boundary start z.1).toReal) =
      (fairSteps (boundaryExitMarkedSteps boundary
        (ThickPoint.discBoundary center radius) start)).toReal := by
  have hfin := sum_skeletonExitKernel_finset_toReal_eq_marked
    boundary (discBoundaryFinset center radius) start
  have hmark : (↑(discBoundaryFinset center radius) : Set Point) =
      ThickPoint.discBoundary center radius := by
    ext z
    simp
  change (∑ z ∈ (Finset.univ : Finset
      (BoundaryFinsetPoint center radius)),
      (skeletonExitKernel boundary start z.1).toReal) = _
  rw [show (Finset.univ : Finset (BoundaryFinsetPoint center radius)) =
      (discBoundaryFinset center radius).attach by ext; simp]
  calc
    (∑ z ∈ (discBoundaryFinset center radius).attach,
        (skeletonExitKernel boundary start z.1).toReal) =
        ∑ z ∈ discBoundaryFinset center radius,
          (skeletonExitKernel boundary start z).toReal :=
      Finset.sum_attach (discBoundaryFinset center radius)
        (fun z : Point ↦ (skeletonExitKernel boundary start z).toReal)
    _ = (fairSteps (boundaryExitMarkedSteps boundary
          (↑(discBoundaryFinset center radius) : Set Point) start)).toReal := hfin
    _ = _ := by rw [hmark]

/-- Exact reduction of the endpoint sum on an absorbed boundary piece to
the standard finite-domain exit mass. -/
theorem sum_skeletonExitKernel_finset_toReal_eq_exitMass
    (D : Finset Point) (boundary : Set Point) (B : Finset Point)
    {start : Point} (hstart : start ∈ D)
    (houter : ↑(outerBoundary D) ⊆ boundary)
    (hDboundary : ∀ z, z ∈ D → z ∉ boundary)
    (hDB : Disjoint D B) :
    (∑ z ∈ B, (skeletonExitKernel boundary start z).toReal) =
      (exitMass D B start).toReal := by
  rw [sum_skeletonExitKernel_finset_toReal_eq_marked,
    fairSteps_boundaryExitMarkedSteps_eq_exitMass
      D boundary B hstart houter hDboundary hDB]

/-! ## Literal real-annulus specialization -/

open LiteralRealAnnulus

/-- The actual finite state space on the intermediate literal boundary. -/
abbrev LiteralMiddlePoint (rMiddle : ℝ) := BoundaryFinsetPoint 0 rMiddle

/-- The actual inner-side exit vertices of the finite literal annulus. -/
abbrev LiteralInnerExitPoint
    (rInner rOuter : ℝ) (boxRadius : ℕ) :=
  ↑(literalRealAnnulusInnerExit rInner rOuter boxRadius)

/-- The literal middle→inner→middle cycle kernel, retaining both endpoint
marks while enumerating only the inner-side exits which can actually occur. -/
noncomputable def literalAnnularCycleKernelReal
    (rInner rMiddle rOuter : ℝ) (boxRadius : ℕ) :
    LiteralMiddlePoint rMiddle → LiteralMiddlePoint rMiddle → ℝ :=
  annularCycleKernelReal
    (ThickPoint.discBoundary 0 rOuter)
    (ThickPoint.discBoundary 0 rMiddle)
    (ThickPoint.discBoundary 0 rInner)
    (fun u ↦ u.1) (fun z : LiteralInnerExitPoint rInner rOuter boxRadius ↦ z.1)

/-- A finite literal boundary row has total mass one, stated on its canonical
boundary subtype. -/
theorem sum_skeletonExitKernel_literalMiddlePoint_eq_one
    {rMiddle : ℝ}
    (hmiddle : (ThickPoint.discBoundary 0 rMiddle).Nonempty)
    (start : Point) :
    ∑ v : LiteralMiddlePoint rMiddle,
        (skeletonExitKernel (ThickPoint.discBoundary 0 rMiddle)
          start v.1).toReal = 1 := by
  have hmarked := sum_skeletonExitKernel_finset_toReal_eq_marked
    (ThickPoint.discBoundary 0 rMiddle)
    (discBoundaryFinset 0 rMiddle) start
  have hmass := fairSteps_boundaryExitMarkedSteps_univ_eq_one hmiddle start
  have hmarkEq :
      boundaryExitMarkedSteps (ThickPoint.discBoundary 0 rMiddle)
          (↑(discBoundaryFinset 0 rMiddle) : Set Point) start =
        boundaryExitMarkedSteps (ThickPoint.discBoundary 0 rMiddle)
          Set.univ start := by
    ext omega
    constructor
    · intro homega
      obtain ⟨N, hfirst, _hend⟩ :=
        (mem_boundaryExitMarkedSteps_iff_exists_first
          (ThickPoint.discBoundary 0 rMiddle)
          (↑(discBoundaryFinset 0 rMiddle) : Set Point)
          start omega).1 homega
      apply (mem_boundaryExitMarkedSteps_iff_exists_first
        (ThickPoint.discBoundary 0 rMiddle) Set.univ start omega).2
      exact ⟨N, hfirst, Set.mem_univ _⟩
    · intro homega
      obtain ⟨N, hfirst, _hend⟩ :=
        (mem_boundaryExitMarkedSteps_iff_exists_first
          (ThickPoint.discBoundary 0 rMiddle) Set.univ start omega).1 homega
      apply (mem_boundaryExitMarkedSteps_iff_exists_first
        (ThickPoint.discBoundary 0 rMiddle)
        (↑(discBoundaryFinset 0 rMiddle) : Set Point)
        start omega).2
      exact ⟨N, hfirst, by simpa using hfirst.1⟩
  have hfinset :
      (∑ z ∈ discBoundaryFinset 0 rMiddle,
          (skeletonExitKernel (ThickPoint.discBoundary 0 rMiddle)
            start z).toReal) = 1 := by
    rw [hmarked, hmarkEq, hmass]
    norm_num
  change (∑ v ∈ (Finset.univ : Finset (LiteralMiddlePoint rMiddle)),
      (skeletonExitKernel (ThickPoint.discBoundary 0 rMiddle)
        start v.1).toReal) = 1
  rw [show (Finset.univ : Finset (LiteralMiddlePoint rMiddle)) =
      (discBoundaryFinset 0 rMiddle).attach by ext; simp]
  exact (Finset.sum_attach (discBoundaryFinset 0 rMiddle)
    (fun z ↦ (skeletonExitKernel (ThickPoint.discBoundary 0 rMiddle)
      start z).toReal)).trans hfinset

/-- Centered-at-`center` form of the recurrent boundary row identity. -/
theorem sum_skeletonExitKernel_boundaryFinsetPoint_eq_one
    {center : Point} {radius : ℝ}
    (hboundary : (ThickPoint.discBoundary center radius).Nonempty)
    (start : Point) :
    ∑ v : BoundaryFinsetPoint center radius,
        (skeletonExitKernel (ThickPoint.discBoundary center radius)
          start v.1).toReal = 1 := by
  have hmarked := sum_skeletonExitKernel_finset_toReal_eq_marked
    (ThickPoint.discBoundary center radius)
    (discBoundaryFinset center radius) start
  have hmass := fairSteps_boundaryExitMarkedSteps_univ_eq_one hboundary start
  have hmarkEq :
      boundaryExitMarkedSteps (ThickPoint.discBoundary center radius)
          (↑(discBoundaryFinset center radius) : Set Point) start =
        boundaryExitMarkedSteps (ThickPoint.discBoundary center radius)
          Set.univ start := by
    ext omega
    constructor
    · intro homega
      obtain ⟨N, hfirst, _hend⟩ :=
        (mem_boundaryExitMarkedSteps_iff_exists_first
          (ThickPoint.discBoundary center radius)
          (↑(discBoundaryFinset center radius) : Set Point)
          start omega).1 homega
      apply (mem_boundaryExitMarkedSteps_iff_exists_first
        (ThickPoint.discBoundary center radius) Set.univ start omega).2
      exact ⟨N, hfirst, Set.mem_univ _⟩
    · intro homega
      obtain ⟨N, hfirst, _hend⟩ :=
        (mem_boundaryExitMarkedSteps_iff_exists_first
          (ThickPoint.discBoundary center radius) Set.univ start omega).1 homega
      apply (mem_boundaryExitMarkedSteps_iff_exists_first
        (ThickPoint.discBoundary center radius)
        (↑(discBoundaryFinset center radius) : Set Point)
        start omega).2
      exact ⟨N, hfirst, by simpa using hfirst.1⟩
  have hfinset :
      (∑ z ∈ discBoundaryFinset center radius,
          (skeletonExitKernel (ThickPoint.discBoundary center radius)
            start z).toReal) = 1 := by
    rw [hmarked, hmarkEq, hmass]
    norm_num
  change (∑ v ∈ (Finset.univ : Finset
      (BoundaryFinsetPoint center radius)),
      (skeletonExitKernel (ThickPoint.discBoundary center radius)
        start v.1).toReal) = 1
  rw [show (Finset.univ : Finset (BoundaryFinsetPoint center radius)) =
      (discBoundaryFinset center radius).attach by ext; simp]
  exact (Finset.sum_attach (discBoundaryFinset center radius)
    (fun z ↦ (skeletonExitKernel (ThickPoint.discBoundary center radius)
      start z).toReal)).trans hfinset

/-- Exact finite-domain meaning of the first (middle-to-inner) row mass in
the literal real annulus. -/
theorem sum_skeletonExitKernel_literalInnerExit_eq_exitMass
    {rInner rOuter : ℝ} {boxRadius : ℕ} {start : Point}
    (hrOuter : 0 ≤ rOuter) (hOuterBox : rOuter ≤ (boxRadius : ℝ))
    (hstart : start ∈ literalRealAnnulus rInner rOuter boxRadius) :
    (∑ z : LiteralInnerExitPoint rInner rOuter boxRadius,
        (skeletonExitKernel
          (ThickPoint.discBoundary 0 rInner ∪
            ThickPoint.discBoundary 0 rOuter) start z.1).toReal) =
      (exitMass (literalRealAnnulus rInner rOuter boxRadius)
        (literalRealAnnulusInnerExit rInner rOuter boxRadius) start).toReal := by
  let D := literalRealAnnulus rInner rOuter boxRadius
  let B := literalRealAnnulusInnerExit rInner rOuter boxRadius
  let C := literalRealAnnulusOuterExit rInner rOuter boxRadius
  let boundary := ThickPoint.discBoundary 0 rInner ∪
    ThickPoint.discBoundary 0 rOuter
  have houter : ↑(outerBoundary D) ⊆ boundary := by
    intro z hz
    have hzUnion : z ∈ B ∪ C := by
      rw [literalRealAnnulus_exit_union rInner rOuter boxRadius]
      exact hz
    rcases Finset.mem_union.mp hzUnion with hzB | hzC
    · exact Or.inl (literalRealAnnulusInnerExit_subset_discBoundary hzB)
    · exact Or.inr
        (literalRealAnnulusOuterExit_subset_discBoundary
          hrOuter hOuterBox hzC)
  have hDboundary : ∀ z, z ∈ D → z ∉ boundary := by
    intro z hzD hzBoundary
    have hzData := mem_literalRealAnnulus_raw.mp hzD
    rcases hzBoundary with hzInner | hzOuter
    · exact hzData.2.2.2 hzInner.1
    · exact hzData.2.2.1 hzOuter
  have hDB : Disjoint D B := by
    rw [Finset.disjoint_left]
    intro z hzD hzB
    exact (mem_outerBoundary D z).mp
      ((mem_literalRealAnnulusInnerExit
        rInner rOuter boxRadius z).mp hzB).1 |>.1 hzD
  have hsum := sum_skeletonExitKernel_finset_toReal_eq_exitMass
    D boundary B hstart houter hDboundary hDB
  change (∑ z ∈ (Finset.univ : Finset
      (LiteralInnerExitPoint rInner rOuter boxRadius)),
      (skeletonExitKernel boundary start z.1).toReal) = _
  rw [show (Finset.univ : Finset
      (LiteralInnerExitPoint rInner rOuter boxRadius)) = B.attach by
        ext; simp]
  exact (Finset.sum_attach B
    (fun z ↦ (skeletonExitKernel boundary start z).toReal)).trans hsum

/-! ## Row algebra for the literal two-stage kernel -/

/-- If the fresh inner-to-middle boundary kernel has total mass one, then
the row sum of the literal two-stage cycle kernel is exactly the probability
of first hitting the inner endpoint. -/
theorem sum_annularCycleKernelReal_eq_of_return_rows
    {Middle Inner : Type*} [Fintype Middle] [Fintype Inner]
    (outer middle inner : Set Point)
    (middlePoint : Middle → Point) (innerPoint : Inner → Point)
    (hreturn : ∀ z : Inner,
      ∑ v : Middle,
        (skeletonExitKernel middle (innerPoint z) (middlePoint v)).toReal = 1)
    (u : Middle) :
    (∑ v : Middle, annularCycleKernelReal outer middle inner
        middlePoint innerPoint u v) =
      ∑ z : Inner,
        (skeletonExitKernel (inner ∪ outer)
          (middlePoint u) (innerPoint z)).toReal := by
  classical
  have hfinite (boundary : Set Point) (start exit : Point) :
      skeletonExitKernel boundary start exit ≠ ⊤ := by
    unfold skeletonExitKernel skeletonExitMarkKernel
    exact measure_ne_top fairSteps _
  have hproduct (z : Inner) (v : Middle) :
      skeletonExitKernel (inner ∪ outer) (middlePoint u) (innerPoint z) *
          skeletonExitKernel middle (innerPoint z) (middlePoint v) ≠ ⊤ :=
    ENNReal.mul_ne_top (hfinite _ _ _) (hfinite _ _ _)
  simp only [annularCycleKernelReal, annularCycleKernel]
  simp_rw [ENNReal.toReal_sum (fun z _hz ↦ hproduct z _), ENNReal.toReal_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _hz
  rw [← Finset.mul_sum, hreturn z, mul_one]

/-- Exact row reduction for the literal middle→inner→middle cycle: its
total mass is the finite annular inner-exit probability. -/
theorem sum_literalAnnularCycleKernelReal_eq_exitMass
    {rInner rMiddle rOuter : ℝ} {boxRadius : ℕ}
    (hmiddle : (ThickPoint.discBoundary 0 rMiddle).Nonempty)
    (hrOuter : 0 ≤ rOuter) (hOuterBox : rOuter ≤ (boxRadius : ℝ))
    (u : LiteralMiddlePoint rMiddle)
    (huAnnulus : u.1 ∈ literalRealAnnulus rInner rOuter boxRadius) :
    (∑ v : LiteralMiddlePoint rMiddle,
        literalAnnularCycleKernelReal
          rInner rMiddle rOuter boxRadius u v) =
      (exitMass (literalRealAnnulus rInner rOuter boxRadius)
        (literalRealAnnulusInnerExit rInner rOuter boxRadius) u.1).toReal := by
  rw [literalAnnularCycleKernelReal,
    sum_annularCycleKernelReal_eq_of_return_rows]
  · exact sum_skeletonExitKernel_literalInnerExit_eq_exitMass
      hrOuter hOuterBox huAnnulus
  · intro z
    exact sum_skeletonExitKernel_literalMiddlePoint_eq_one hmiddle z.1

/-! ## The literal HLOZ profile row -/

/-- Translation of the marked inward event between two literal concentric
boundaries. -/
theorem boundaryExitMarkedSteps_twoDiscBoundaries_centered_eq_zero_real
    (rInner rOuter : ℝ) (center start : Point) :
    boundaryExitMarkedSteps
        (ThickPoint.discBoundary center rInner ∪
          ThickPoint.discBoundary center rOuter)
        (ThickPoint.discBoundary center rInner) start =
      boundaryExitMarkedSteps
        (ThickPoint.discBoundary 0 rInner ∪
          ThickPoint.discBoundary 0 rOuter)
        (ThickPoint.discBoundary 0 rInner) (start - center) := by
  ext omega
  constructor
  · intro homega
    obtain ⟨N, hfirst, hend⟩ :=
      (mem_boundaryExitMarkedSteps_iff_exists_first _ _ _ _).1 homega
    apply (mem_boundaryExitMarkedSteps_iff_exists_first _ _ _ _).2
    refine ⟨N, ⟨?_, ?_⟩, ?_⟩
    · rcases hfirst.1 with hinner | houter
      · exact Or.inl (by
          have ht := (BoundaryStoppedHarnack.mem_discBoundary_translate
            center rInner _).mp hinner
          simpa only [BoundaryStoppedHarnack.trajectoryFrom_sub_center]
            using ht)
      · exact Or.inr (by
          have ht := (BoundaryStoppedHarnack.mem_discBoundary_translate
            center rOuter _).mp houter
          simpa only [BoundaryStoppedHarnack.trajectoryFrom_sub_center]
            using ht)
    · intro q hq hcentered
      apply hfirst.2 q hq
      rcases hcentered with hinner | houter
      · exact Or.inl ((BoundaryStoppedHarnack.mem_discBoundary_translate
          center rInner _).mpr (by
            simpa only [BoundaryStoppedHarnack.trajectoryFrom_sub_center]
              using hinner))
      · exact Or.inr ((BoundaryStoppedHarnack.mem_discBoundary_translate
          center rOuter _).mpr (by
            simpa only [BoundaryStoppedHarnack.trajectoryFrom_sub_center]
              using houter))
    · have ht := (BoundaryStoppedHarnack.mem_discBoundary_translate
        center rInner _).mp hend
      simpa only [BoundaryStoppedHarnack.trajectoryFrom_sub_center] using ht
  · intro homega
    obtain ⟨N, hfirst, hend⟩ :=
      (mem_boundaryExitMarkedSteps_iff_exists_first _ _ _ _).1 homega
    apply (mem_boundaryExitMarkedSteps_iff_exists_first _ _ _ _).2
    refine ⟨N, ⟨?_, ?_⟩, ?_⟩
    · rcases hfirst.1 with hinner | houter
      · exact Or.inl ((BoundaryStoppedHarnack.mem_discBoundary_translate
          center rInner _).mpr (by
            simpa only [BoundaryStoppedHarnack.trajectoryFrom_sub_center]
              using hinner))
      · exact Or.inr ((BoundaryStoppedHarnack.mem_discBoundary_translate
          center rOuter _).mpr (by
            simpa only [BoundaryStoppedHarnack.trajectoryFrom_sub_center]
              using houter))
    · intro q hq horiginal
      apply hfirst.2 q hq
      rcases horiginal with hinner | houter
      · exact Or.inl (by
          have ht := (BoundaryStoppedHarnack.mem_discBoundary_translate
            center rInner _).mp hinner
          simpa only [BoundaryStoppedHarnack.trajectoryFrom_sub_center]
            using ht)
      · exact Or.inr (by
          have ht := (BoundaryStoppedHarnack.mem_discBoundary_translate
            center rOuter _).mp houter
          simpa only [BoundaryStoppedHarnack.trajectoryFrom_sub_center]
            using ht)
    · exact (BoundaryStoppedHarnack.mem_discBoundary_translate
        center rInner _).mpr (by
          simpa only [BoundaryStoppedHarnack.trajectoryFrom_sub_center]
            using hend)

/-- Intermediate spatial states on `profileInnerBoundary n k x`. -/
abbrev ProfileCycleMiddlePoint (n k : ℕ) (x : Point) :=
  BoundaryFinsetPoint x (ThickPoint.scaleRadius n k)

/-- Inner spatial states on `profileInnerBoundary n (k+1) x`. -/
abbrev ProfileCycleInnerPoint (n k : ℕ) (x : Point) :=
  BoundaryFinsetPoint x (ThickPoint.scaleRadius n (k + 1))

/-- Retained outer endpoints on `profileOuterBoundary n k x`. -/
abbrev ProfileCycleOuterPoint (n k : ℕ) (x : Point) :=
  BoundaryFinsetPoint x (ThickPoint.scaleRadius n (k - 1))

/-- The actual unrounded profile middle→inner→middle cycle subkernel.
Its three stopped sets are definitionally the outer, middle, and next inner
profile boundaries at level `k`. -/
noncomputable def profileAnnularCycleKernelReal
    (n k : ℕ) (x : Point) :
    ProfileCycleMiddlePoint n k x → ProfileCycleMiddlePoint n k x → ℝ :=
  annularCycleKernelReal
    (profileOuterBoundary n k x)
    (profileInnerBoundary n k x)
    (profileInnerBoundary n (k + 1) x)
    (fun u ↦ u.1) (fun z : ProfileCycleInnerPoint n k x ↦ z.1)

/-- The endpoint-integrated final escape row for the same literal profile
gap. -/
noncomputable def profileAnnularEscapeRowReal
    (n k : ℕ) (x : Point) (u : ProfileCycleMiddlePoint n k x) : ℝ :=
  ∑ w : ProfileCycleOuterPoint n k x,
    annularEscapeKernelReal
      (profileOuterBoundary n k x)
      (profileInnerBoundary n (k + 1) x)
      (fun v : ProfileCycleMiddlePoint n k x ↦ v.1)
      (fun w : ProfileCycleOuterPoint n k x ↦ w.1) u w

/-- Exact endpoint-conditioned renewal identity for the three profile
boundaries, with no analytic approximation. -/
theorem profileAnnularKernelsReal_isRenewalKernel
    {n k : ℕ} {x : Point}
    (hInnerMiddle : ThickPoint.scaleRadius n (k + 1) ≤
      ThickPoint.scaleRadius n k)
    (hMiddleOuter : ThickPoint.scaleRadius n k + 1 ≤
      ThickPoint.scaleRadius n (k - 1)) :
    IsRenewalKernel
      (profileAnnularCycleKernelReal n k x)
      (annularEscapeKernelReal
        (profileOuterBoundary n k x)
        (profileInnerBoundary n (k + 1) x)
        (fun v : ProfileCycleMiddlePoint n k x ↦ v.1)
        (fun w : ProfileCycleOuterPoint n k x ↦ w.1))
      (annularUnmarkedKernelReal
        (profileOuterBoundary n k x)
        (fun v : ProfileCycleMiddlePoint n k x ↦ v.1)
        (fun w : ProfileCycleOuterPoint n k x ↦ w.1)) := by
  unfold profileAnnularCycleKernelReal profileOuterBoundary
    profileInnerBoundary
  apply annularKernelsReal_isRenewalKernel
  · exact enumeratesBoundary_boundaryFinsetPoint _ _
  · exact enumeratesBoundary_boundaryFinsetPoint _ _
  · exact enumeratesBoundary_boundaryFinsetPoint _ _
  · apply discBoundaries_disjoint_of_separated
    linarith
  · intro z
    exact FirstHitSeparates.discBoundaries
      (mem_discBoundaryFinset.mp z.2) hInnerMiddle hMiddleOuter

/-- After summing the retained outer endpoint, the actual profile cycle and
escape rows form a stochastic renewal row. -/
theorem profileAnnularCycle_escape_isStochasticRenewalRow
    {n k : ℕ} {x : Point}
    (hOuterNonempty : (profileOuterBoundary n k x).Nonempty)
    (hInnerMiddle : ThickPoint.scaleRadius n (k + 1) ≤
      ThickPoint.scaleRadius n k)
    (hMiddleOuter : ThickPoint.scaleRadius n k + 1 ≤
      ThickPoint.scaleRadius n (k - 1)) :
    IsStochasticRenewalRow
      (profileAnnularCycleKernelReal n k x)
      (profileAnnularEscapeRowReal n k x) := by
  apply isStochasticRenewalRow_of_isRenewalKernel_of_sum_eq_one
    (profileAnnularKernelsReal_isRenewalKernel
      hInnerMiddle hMiddleOuter)
  intro u
  unfold annularUnmarkedKernelReal annularUnmarkedKernel
  simpa only [profileOuterBoundary] using
    (sum_skeletonExitKernel_boundaryFinsetPoint_eq_one hOuterNonempty u.1)

/-- Exact integrated row identity for the HLOZ profile cycle.  The return
from the next inner boundary has mass one by planar recurrence, so the cycle
row is precisely the (spatially integrated) probability that the next radial
index is inward. -/
theorem sum_profileAnnularCycleKernelReal_eq_inwardRow
    {n k : ℕ} {x : Point}
    (hmiddle : (profileInnerBoundary n k x).Nonempty)
    (u : ProfileCycleMiddlePoint n k x) :
    (∑ v : ProfileCycleMiddlePoint n k x,
        profileAnnularCycleKernelReal n k x u v) =
      ∑ z : ProfileCycleInnerPoint n k x,
        (skeletonExitKernel
          (profileInnerBoundary n (k + 1) x ∪
            profileOuterBoundary n k x) u.1 z.1).toReal := by
  rw [profileAnnularCycleKernelReal,
    sum_annularCycleKernelReal_eq_of_return_rows]
  intro z
  simpa only [profileInnerBoundary] using
    (sum_skeletonExitKernel_boundaryFinsetPoint_eq_one hmiddle z.1)

/-- Translation removes the profile center after all inner endpoints have
been integrated. -/
theorem profileInwardRow_eq_centeredInwardRow
    {n k : ℕ} {x : Point} (u : ProfileCycleMiddlePoint n k x) :
    (∑ z : ProfileCycleInnerPoint n k x,
        (skeletonExitKernel
          (profileInnerBoundary n (k + 1) x ∪
            profileOuterBoundary n k x) u.1 z.1).toReal) =
      ∑ z : LiteralMiddlePoint (ThickPoint.scaleRadius n (k + 1)),
        (skeletonExitKernel
          (ThickPoint.discBoundary 0 (ThickPoint.scaleRadius n (k + 1)) ∪
            ThickPoint.discBoundary 0 (ThickPoint.scaleRadius n (k - 1)))
          (u.1 - x) z.1).toReal := by
  rw [sum_skeletonExitKernel_boundaryFinsetPoint_eq_marked,
    sum_skeletonExitKernel_boundaryFinsetPoint_eq_marked]
  unfold profileInnerBoundary profileOuterBoundary
  rw [boundaryExitMarkedSteps_twoDiscBoundaries_centered_eq_zero_real]

/-- Any explicit two-sided estimate for the integrated inward radial row
immediately is the same estimate for the actual two-stage cycle row. -/
theorem sum_profileAnnularCycleKernelReal_two_sided_of_inwardRow
    {n k : ℕ} {x : Point} {error : ℝ}
    (hmiddle : (profileInnerBoundary n k x).Nonempty)
    (u : ProfileCycleMiddlePoint n k x)
    (hinward :
      (1 - error) / 2 ≤
          ∑ z : ProfileCycleInnerPoint n k x,
            (skeletonExitKernel
              (profileInnerBoundary n (k + 1) x ∪
                profileOuterBoundary n k x) u.1 z.1).toReal ∧
        (∑ z : ProfileCycleInnerPoint n k x,
            (skeletonExitKernel
              (profileInnerBoundary n (k + 1) x ∪
                profileOuterBoundary n k x) u.1 z.1).toReal) ≤
          (1 + error) / 2) :
    (1 - error) / 2 ≤
          ∑ v : ProfileCycleMiddlePoint n k x,
            profileAnnularCycleKernelReal n k x u v ∧
      (∑ v : ProfileCycleMiddlePoint n k x,
          profileAnnularCycleKernelReal n k x u v) ≤
        (1 + error) / 2 := by
  rw [sum_profileAnnularCycleKernelReal_eq_inwardRow hmiddle u]
  exact hinward

end

end Erdos1165.AnnularOffspringKernelRadial
