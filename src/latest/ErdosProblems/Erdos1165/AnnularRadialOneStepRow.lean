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
import ErdosProblems.Erdos1165.ProfileAnnularRowRegular

/-!
# Endpoint-integrated rows of the chronological radial chain

The chronological radial word stops each physical piece on the union of all
profile boundaries except its source boundary.  This file identifies its
finite endpoint sum with that literal marked first-hit event, and then reduces
an internal row to the ordinary adjacent two-boundary annulus row.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal Topology

namespace Erdos1165.AnnularRadialOneStepRow

open ThickPoint TerminalProfileBoundarySeparation
open TerminalSpliceProfileGeometry
open TerminalExcursionBridge
open PlanarPotential TerminalSequentialVisitLaw
open BoundaryVisitRegeneration
open MarkedBoundaryVisitKernel AnnularOffspringRenewal
open AnnularOffspringKernelRadial AnnularOffspringKernelRadialExit
open AnnularOffspringKernel
open AnnularRadialLabelWord AnnularProfileClocks RealDiscFinite
open ProfileAnnularRowRegular
open LiteralRealAnnulusRadialExit

noncomputable section

/-- The endpoint sum occurring in the recursive chronological chain is
exactly the probability of its endpoint-integrated one-step atom. -/
theorem sum_skeletonExitKernel_otherRadialBoundaries_toReal_eq
    (n : ℕ) (center : Point) (source target : Fin (n + 2))
    (start : Point) :
    (∑ endpoint : RadialBoundaryPoint n center target,
        (skeletonExitKernel (otherRadialBoundaries n center source)
          start endpoint.1).toReal) =
      (radialOneStepKernelENNReal n center source target start).toReal := by
  unfold radialOneStepKernelENNReal radialOneStepAtom radialBoundary
  calc
    (∑ endpoint : DiscBoundaryPoint center (scaleRadius n target),
        (skeletonExitKernel (otherRadialBoundaries n center source)
          start endpoint.1).toReal) =
        ∑ z ∈ discBoundaryFinset center (scaleRadius n target),
          (skeletonExitKernel (otherRadialBoundaries n center source)
            start z).toReal := by
      symm
      exact Finset.sum_subtype
        (discBoundaryFinset center (scaleRadius n target))
        (fun z ↦ mem_discBoundaryFinset) _
    _ = _ := by
      rw [← show (↑(discBoundaryFinset center (scaleRadius n target)) :
        Set Point) = discBoundary center (scaleRadius n target) by ext; simp]
      exact sum_skeletonExitKernel_finset_toReal_eq_marked
        (otherRadialBoundaries n center source)
          (discBoundaryFinset center (scaleRadius n target)) start

/-- ENNReal form of the exact finite endpoint-sum identity. -/
theorem sum_skeletonExitKernel_otherRadialBoundaries_eq
    (n : ℕ) (center : Point) (source target : Fin (n + 2))
    (start : Point) :
    (∑ endpoint : RadialBoundaryPoint n center target,
        skeletonExitKernel (otherRadialBoundaries n center source)
          start endpoint.1) =
      radialOneStepKernelENNReal n center source target start := by
  have hsumtop : (∑ endpoint : RadialBoundaryPoint n center target,
      skeletonExitKernel (otherRadialBoundaries n center source)
        start endpoint.1) ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr fun endpoint _ ↦ by
      unfold skeletonExitKernel skeletonExitMarkKernel
      exact measure_ne_top fairSteps _
  have hrowtop : radialOneStepKernelENNReal n center source target start ≠ ⊤ := by
    unfold radialOneStepKernelENNReal
    exact measure_ne_top fairSteps _
  apply (ENNReal.toReal_eq_toReal_iff' hsumtop hrowtop).mp
  rw [ENNReal.toReal_sum]
  · exact sum_skeletonExitKernel_otherRadialBoundaries_toReal_eq
      n center source target start
  · intro endpoint _
    unfold skeletonExitKernel skeletonExitMarkKernel
    exact measure_ne_top fairSteps _

/-- The inner vertex boundary of a disc also separates an exterior starting
point from every target contained in that disc.  This is the entrance-side
counterpart of `FirstHitSeparates.innerBoundary`. -/
theorem FirstHitSeparates.discBoundary_of_start_not_mem_disc
    {center start : Point} {radius : ℝ} {target : Set Point}
    (hstart : start ∉ disc center radius)
    (htarget : target ⊆ disc center radius) :
    FirstHitSeparates (discBoundary center radius) target start := by
  classical
  intro omega
  by_cases htop : boundaryExitTime target start omega = ⊤
  · rw [htop]
    exact le_top
  · lift boundaryExitTime target start omega to ℕ using htop with N hN
    have htargetTime : boundaryExitTime target start omega = N := hN.symm
    have hspec := (firstHitSetAfter_eq_coe_iff zeroClock
      (BoundaryVisitLaw.relativeBoundary target start) omega N).mp htargetTime
    have hNtarget : trajectoryFrom start omega N ∈ target := hspec.2.1
    have hNinside : trajectoryFrom start omega N ∈ disc center radius :=
      htarget hNtarget
    let henter : ∃ t : ℕ, trajectoryFrom start omega t ∈ disc center radius :=
      ⟨N, hNinside⟩
    let t : ℕ := Nat.find henter
    have htInside : trajectoryFrom start omega t ∈ disc center radius :=
      Nat.find_spec henter
    have htN : t ≤ N := Nat.find_min' henter hNinside
    have htpos : 0 < t := by
      by_contra ht0
      have htEq : t = 0 := Nat.eq_zero_of_not_pos ht0
      rw [htEq] at htInside
      have htrajectoryZero : trajectoryFrom start omega 0 = start := by
        unfold trajectoryFrom
        rw [trajectory_zero]
        ext <;> simp
      rw [htrajectoryZero] at htInside
      exact hstart htInside
    let q : ℕ := t - 1
    have hqt : q < t := by
      dsimp only [q]
      omega
    have hqOutside : trajectoryFrom start omega q ∉ disc center radius := by
      exact fun hqInside ↦ Nat.not_le_of_gt hqt
        (Nat.find_min' henter hqInside)
    have hqSucc : q + 1 = t := by
      dsimp only [q]
      omega
    have hadjacent : Adjacent (trajectoryFrom start omega t)
        (trajectoryFrom start omega q) := by
      have hforward :=
        TerminalGlobalExitSplice.adjacent_trajectoryFrom_succ start omega q
      rw [hqSucc] at hforward
      unfold Adjacent at hforward ⊢
      have hfirst :
          ((trajectoryFrom start omega t).1 -
              (trajectoryFrom start omega q).1).natAbs =
            ((trajectoryFrom start omega q).1 -
              (trajectoryFrom start omega t).1).natAbs := by
        have heq : (trajectoryFrom start omega t).1 -
            (trajectoryFrom start omega q).1 =
          -((trajectoryFrom start omega q).1 -
            (trajectoryFrom start omega t).1) := by omega
        calc
          ((trajectoryFrom start omega t).1 -
              (trajectoryFrom start omega q).1).natAbs =
              (-((trajectoryFrom start omega q).1 -
                (trajectoryFrom start omega t).1)).natAbs :=
            congrArg Int.natAbs heq
          _ = _ := Int.natAbs_neg _
      have hsecond :
          ((trajectoryFrom start omega t).2 -
              (trajectoryFrom start omega q).2).natAbs =
            ((trajectoryFrom start omega q).2 -
              (trajectoryFrom start omega t).2).natAbs := by
        have heq : (trajectoryFrom start omega t).2 -
            (trajectoryFrom start omega q).2 =
          -((trajectoryFrom start omega q).2 -
            (trajectoryFrom start omega t).2) := by omega
        calc
          ((trajectoryFrom start omega t).2 -
              (trajectoryFrom start omega q).2).natAbs =
              (-((trajectoryFrom start omega q).2 -
                (trajectoryFrom start omega t).2)).natAbs :=
            congrArg Int.natAbs heq
          _ = _ := Int.natAbs_neg _
      rw [hfirst, hsecond]
      exact hforward
    have htBoundary : trajectoryFrom start omega t ∈
        discBoundary center radius := by
      exact ⟨htInside, trajectoryFrom start omega q, hqOutside, hadjacent⟩
    have hbarrierLe : boundaryExitTime (discBoundary center radius)
        start omega ≤ t := by
      apply (firstHitSetAfter_le_iff zeroClock
        (BoundaryVisitLaw.relativeBoundary (discBoundary center radius) start)
          omega t).mpr
      exact ⟨t, le_rfl, by simp [zeroClock], htBoundary⟩
    exact hbarrierLe.trans (WithTop.coe_le_coe.mpr htN)

/-- Any two distinct profile labels are separated by a full lattice step in
the radial direction.  The statement includes the terminal label `n+1`. -/
theorem scaleRadius_add_one_le_of_label_lt
    {n : ℕ} (hn : 2 ≤ n) {outer inner : Fin (n + 2)}
    (hlt : (outer : ℕ) < (inner : ℕ)) :
    scaleRadius n inner + 1 ≤ scaleRadius n outer := by
  have hinnerPos : 0 < (inner : ℕ) := by omega
  have hinnerBound : (inner : ℕ) ≤ n + 1 := by omega
  have hadjacent := scaleRadius_add_one_le_previous
    hn hinnerPos hinnerBound
  have hprevious : scaleRadius n ((inner : ℕ) - 1) ≤
      scaleRadius n outer := by
    apply scaleRadius_antitone_of_le
    · omega
    · omega
  exact hadjacent.trans hprevious

/-- The two adjacent boundaries surrounding an internal profile label. -/
def adjacentRadialBoundaries
    (n k : ℕ) (center : Point) : Set Point :=
  discBoundary center (scaleRadius n (k + 1)) ∪
    discBoundary center (scaleRadius n (k - 1))

/-- Every different profile boundary is separated from an internal source
boundary by one of its two adjacent boundaries. -/
theorem adjacentRadialBoundaries_separates_other
    {n k : ℕ} (hn : 2 ≤ n) (hk : 1 ≤ k) (hkn : k ≤ n)
    (center start : Point)
    (hstart : start ∈ discBoundary center (scaleRadius n k)) :
    FirstHitSeparates (adjacentRadialBoundaries n k center)
      (otherRadialBoundaries n center ⟨k, by omega⟩) start := by
  classical
  let source : Fin (n + 2) := ⟨k, by omega⟩
  let inward : Fin (n + 2) := ⟨k + 1, by omega⟩
  let outward : Fin (n + 2) := ⟨k - 1, by omega⟩
  have hinnerSep : scaleRadius n inward + 1 ≤ scaleRadius n source := by
    exact scaleRadius_add_one_le_of_label_lt hn (by simp [source, inward])
  have houterSep : scaleRadius n source + 1 ≤ scaleRadius n outward := by
    exact scaleRadius_add_one_le_of_label_lt hn (by simp [source, outward]; omega)
  have hstartOutside : start ∉ disc center (scaleRadius n inward) := by
    intro hsmall
    exact (not_mem_discBoundary_of_mem_disc_of_add_one_le hsmall hinnerSep)
      (by simpa [source] using hstart)
  intro omega
  by_cases htop : boundaryExitTime
      (otherRadialBoundaries n center source) start omega = ⊤
  · rw [htop]
    exact le_top
  · lift boundaryExitTime (otherRadialBoundaries n center source)
      start omega to ℕ using htop with N hN
    have hotherTime : boundaryExitTime
        (otherRadialBoundaries n center source) start omega = N := hN.symm
    have hspec := (firstHitSetAfter_eq_coe_iff zeroClock
      (BoundaryVisitLaw.relativeBoundary
        (otherRadialBoundaries n center source) start) omega N).mp hotherTime
    have hNother : trajectoryFrom start omega N ∈
        otherRadialBoundaries n center source := hspec.2.1
    unfold otherRadialBoundaries at hNother
    obtain ⟨exitLabel, hExit⟩ := Set.mem_iUnion.mp hNother
    have hExitNe : exitLabel ≠ source := by
      intro heq
      subst exitLabel
      simpa using hExit
    have hNExit : trajectoryFrom start omega N ∈
        radialBoundary n center exitLabel := by
      simpa only [if_neg hExitNe] using hExit
    have hExitClock : boundaryExitTime
        (radialBoundary n center exitLabel) start omega ≤ N := by
      apply (firstHitSetAfter_le_iff zeroClock
        (BoundaryVisitLaw.relativeBoundary
          (radialBoundary n center exitLabel) start) omega N).mpr
      exact ⟨N, le_rfl, by simp [zeroClock], hNExit⟩
    have hseparate : FirstHitSeparates
        (adjacentRadialBoundaries n k center)
        (radialBoundary n center exitLabel) start := by
      rcases lt_or_gt_of_ne (fun hval ↦ hExitNe (Fin.ext hval)) with
        hExitOuter | hExitInner
      · by_cases hImmediate : (exitLabel : ℕ) = k - 1
        · have hlabel : exitLabel = outward := by
            apply Fin.ext
            simpa [outward] using hImmediate
          subst exitLabel
          apply FirstHitSeparates.of_subset
          intro z hz
          exact Or.inr (by simpa [radialBoundary, outward] using hz)
        · have hExitOuter' : (exitLabel : ℕ) < k := by
            simpa [source] using hExitOuter
          have hFar : (exitLabel : ℕ) < k - 1 := by omega
          have hbarrier : FirstHitSeparates
              (radialBoundary n center outward)
              (radialBoundary n center exitLabel) start := by
            apply FirstHitSeparates.discBoundaries
              (by simpa [radialBoundary, source] using hstart)
            · linarith
            · exact scaleRadius_add_one_le_of_label_lt hn
                (by simpa [outward] using hFar)
          intro path
          have hadjacentLe : boundaryExitTime
              (adjacentRadialBoundaries n k center) start path ≤
              boundaryExitTime (radialBoundary n center outward) start path := by
            apply FirstHitSeparates.of_subset (start := start)
            intro z hz
            exact Or.inr (by simpa [radialBoundary, outward])
          exact hadjacentLe.trans (hbarrier path)
      · by_cases hImmediate : (exitLabel : ℕ) = k + 1
        · have hlabel : exitLabel = inward := by
            apply Fin.ext
            simpa [inward] using hImmediate
          subst exitLabel
          apply FirstHitSeparates.of_subset
          intro z hz
          exact Or.inl (by simpa [radialBoundary, inward] using hz)
        · have hExitInner' : k < (exitLabel : ℕ) := by
            simpa [source] using hExitInner
          have hFar : k + 1 < (exitLabel : ℕ) := by omega
          have htargetInside : radialBoundary n center exitLabel ⊆
              disc center (scaleRadius n inward) := by
            intro z hz
            have hzdisc := hz.1
            change latticeDistance center z ≤ scaleRadius n exitLabel at hzdisc
            change latticeDistance center z ≤ scaleRadius n inward
            have hsep := scaleRadius_add_one_le_of_label_lt hn
              (show (inward : ℕ) < (exitLabel : ℕ) by
                simpa [inward] using hFar)
            exact hzdisc.trans (by linarith)
          have hbarrier : FirstHitSeparates
              (radialBoundary n center inward)
              (radialBoundary n center exitLabel) start := by
            exact FirstHitSeparates.discBoundary_of_start_not_mem_disc
              hstartOutside (by simpa [radialBoundary, inward] using htargetInside)
          intro path
          have hadjacentLe : boundaryExitTime
              (adjacentRadialBoundaries n k center) start path ≤
              boundaryExitTime (radialBoundary n center inward) start path := by
            apply FirstHitSeparates.of_subset (start := start)
            intro z hz
            exact Or.inl (by simpa [radialBoundary, inward])
          exact hadjacentLe.trans (hbarrier path)
    calc
      boundaryExitTime (adjacentRadialBoundaries n k center) start omega ≤
          boundaryExitTime (radialBoundary n center exitLabel) start omega :=
        hseparate omega
      _ ≤ (N : WithTop ℕ) := hExitClock
      _ = boundaryExitTime
          (otherRadialBoundaries n center source) start omega := hotherTime.symm

/-- The adjacent two-boundary set is contained in the all-other-boundaries
set used by the chronological scan. -/
theorem adjacentRadialBoundaries_subset_other
    {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n)
    (center : Point) :
    adjacentRadialBoundaries n k center ⊆
      otherRadialBoundaries n center ⟨k, by omega⟩ := by
  intro z hz
  rcases hz with hz | hz
  · rw [otherRadialBoundaries]
    refine Set.mem_iUnion.mpr ⟨(⟨k + 1, by omega⟩ : Fin (n + 2)), ?_⟩
    rw [if_neg (by intro heq; have := congrArg Fin.val heq; simp at this)]
    simpa [adjacentRadialBoundaries, radialBoundary] using hz
  · rw [otherRadialBoundaries]
    refine Set.mem_iUnion.mpr ⟨(⟨k - 1, by omega⟩ : Fin (n + 2)), ?_⟩
    rw [if_neg (by intro heq; have := congrArg Fin.val heq; simp at this; omega)]
    simpa [adjacentRadialBoundaries, radialBoundary] using hz

/-- For an internal source label, the successive-different-boundary clock
is exactly the first-hit clock of the two adjacent boundaries. -/
theorem boundaryExitTime_otherRadialBoundaries_eq_adjacent
    {n k : ℕ} (hn : 2 ≤ n) (hk : 1 ≤ k) (hkn : k ≤ n)
    (center start : Point)
    (hstart : start ∈ discBoundary center (scaleRadius n k)) :
    boundaryExitTime (otherRadialBoundaries n center ⟨k, by omega⟩) start =
      boundaryExitTime (adjacentRadialBoundaries n k center) start := by
  funext path
  apply le_antisymm
  · exact FirstHitSeparates.of_subset
      (adjacentRadialBoundaries_subset_other hk hkn center) path
  · exact adjacentRadialBoundaries_separates_other
      hn hk hkn center start hstart path

/-- The literal all-other one-step event is the ordinary adjacent-annulus
first-exit event, while retaining the same target mark. -/
theorem radialOneStepAtom_eq_adjacent
    {n k : ℕ} (hn : 2 ≤ n) (hk : 1 ≤ k) (hkn : k ≤ n)
    (center start : Point) (target : Fin (n + 2))
    (hstart : start ∈ discBoundary center (scaleRadius n k)) :
    radialOneStepAtom n center ⟨k, by omega⟩ target start =
      boundaryExitMarkedSteps (adjacentRadialBoundaries n k center)
        (radialBoundary n center target) start := by
  unfold radialOneStepAtom boundaryExitMarkedSteps
  rw [boundaryExitTime_otherRadialBoundaries_eq_adjacent
    hn hk hkn center start hstart]

/-- Exact inward-row reduction for an internal chronological transition.
The right side is the standard endpoint-integrated profile annulus row. -/
theorem radialOneStepKernelENNReal_internal_inward_toReal_eq
    {n k : ℕ} (hn : 2 ≤ n) (hk : 1 ≤ k) (hkn : k ≤ n)
    (center start : Point)
    (hstart : start ∈ discBoundary center (scaleRadius n k)) :
    (radialOneStepKernelENNReal n center ⟨k, by omega⟩
        ⟨k + 1, by omega⟩ start).toReal =
      ∑ z : ProfileCycleInnerPoint n k center,
        (skeletonExitKernel
          (profileInnerBoundary n (k + 1) center ∪
            profileOuterBoundary n k center) start z.1).toReal := by
  unfold radialOneStepKernelENNReal
  rw [radialOneStepAtom_eq_adjacent hn hk hkn center start
    ⟨k + 1, by omega⟩ hstart]
  have hrow := sum_skeletonExitKernel_boundaryFinsetPoint_eq_marked
    (adjacentRadialBoundaries n k center) center
      (scaleRadius n (k + 1)) start
  rw [show adjacentRadialBoundaries n k center =
      profileInnerBoundary n (k + 1) center ∪
        profileOuterBoundary n k center by
    rfl]
  exact hrow.symm

/-- Exact outward-row reduction for an internal chronological transition. -/
theorem radialOneStepKernelENNReal_internal_outward_toReal_eq
    {n k : ℕ} (hn : 2 ≤ n) (hk : 1 ≤ k) (hkn : k ≤ n)
    (center start : Point)
    (hstart : start ∈ discBoundary center (scaleRadius n k)) :
    (radialOneStepKernelENNReal n center ⟨k, by omega⟩
        ⟨k - 1, by omega⟩ start).toReal =
      profileAnnularEscapeRowReal n k center
        ⟨start, mem_discBoundaryFinset.mpr hstart⟩ := by
  unfold radialOneStepKernelENNReal
  rw [radialOneStepAtom_eq_adjacent hn hk hkn center start
    ⟨k - 1, by omega⟩ hstart]
  have hrow := sum_skeletonExitKernel_boundaryFinsetPoint_eq_marked
    (adjacentRadialBoundaries n k center) center
      (scaleRadius n (k - 1)) start
  change (fairSteps (boundaryExitMarkedSteps
      (adjacentRadialBoundaries n k center)
      (discBoundary center (scaleRadius n (k - 1))) start)).toReal = _
  rw [← hrow]
  unfold profileAnnularEscapeRowReal annularEscapeKernelReal
    annularEscapeKernel adjacentRadialBoundaries profileInnerBoundary
    profileOuterBoundary
  rfl

/-- Both directions of an internal chronological decision satisfy the same
explicit half-row comparison.  The error is the literal real-radius annulus
error; no fixed endpoint is conditioned upon. -/
theorem radialOneStepKernelENNReal_internal_half_bounds
    {n k : ℕ} (hn : 2 ≤ n) (hk : 1 ≤ k) (hkn : k + 1 ≤ n)
    (center start : Point)
    (hstart : start ∈ discBoundary center (scaleRadius n k))
    (hOuterNonempty : (profileOuterBoundary n k center).Nonempty) :
    let rowError := literalRealAnnulusRowError
      (scaleRadius n (k + 1)) (scaleRadius n k) (scaleRadius n (k - 1))
    (1 - rowError) / 2 ≤
        (radialOneStepKernelENNReal n center ⟨k, by omega⟩
          ⟨k + 1, by omega⟩ start).toReal ∧
      (radialOneStepKernelENNReal n center ⟨k, by omega⟩
          ⟨k + 1, by omega⟩ start).toReal ≤ (1 + rowError) / 2 ∧
      (1 - rowError) / 2 ≤
        (radialOneStepKernelENNReal n center ⟨k, by omega⟩
          ⟨k - 1, by omega⟩ start).toReal ∧
      (radialOneStepKernelENNReal n center ⟨k, by omega⟩
          ⟨k - 1, by omega⟩ start).toReal ≤ (1 + rowError) / 2 := by
  dsimp only
  let u : ProfileCycleMiddlePoint n k center :=
    ⟨start, mem_discBoundaryFinset.mpr hstart⟩
  have hhalf := profileAnnularCycleKernelReal_halfRowComparison_regular
    hn hk hkn u
  have hmiddleNonempty : (profileInnerBoundary n k center).Nonempty := by
    apply discBoundary_center_nonempty_of_nonneg
    unfold scaleRadius regularRadius
    split_ifs <;> positivity
  have hinwardRow := sum_profileAnnularCycleKernelReal_eq_inwardRow
    hmiddleNonempty u
  have hrenewal := profileAnnularCycle_escape_isStochasticRenewalRow
    hOuterNonempty
    (by
      have hsep := scaleRadius_add_one_le_of_label_lt hn
        (show ((⟨k, by omega⟩ : Fin (n + 2)) : ℕ) <
          ((⟨k + 1, by omega⟩ : Fin (n + 2)) : ℕ) by simp)
      linarith)
    (by
      exact scaleRadius_add_one_le_of_label_lt hn
        (show ((⟨k - 1, by omega⟩ : Fin (n + 2)) : ℕ) <
          ((⟨k, by omega⟩ : Fin (n + 2)) : ℕ) by simp; omega)) u
  have hinwardExact := radialOneStepKernelENNReal_internal_inward_toReal_eq
    hn hk (by omega) center start hstart
  have houtwardExact := radialOneStepKernelENNReal_internal_outward_toReal_eq
    hn hk (by omega) center start hstart
  have hinnerLower : (1 - literalRealAnnulusRowError
      (scaleRadius n (k + 1)) (scaleRadius n k) (scaleRadius n (k - 1))) / 2 ≤
      (radialOneStepKernelENNReal n center ⟨k, by omega⟩
        ⟨k + 1, by omega⟩ start).toReal := by
    rw [hinwardExact, ← hinwardRow]
    exact hhalf.1
  have hinnerUpper :
      (radialOneStepKernelENNReal n center ⟨k, by omega⟩
        ⟨k + 1, by omega⟩ start).toReal ≤
      (1 + literalRealAnnulusRowError
        (scaleRadius n (k + 1)) (scaleRadius n k) (scaleRadius n (k - 1))) / 2 := by
    rw [hinwardExact, ← hinwardRow]
    exact hhalf.2
  refine ⟨hinnerLower, hinnerUpper, ?_, ?_⟩
  · rw [houtwardExact]
    rw [hinwardRow] at hrenewal
    linarith
  · rw [houtwardExact]
    rw [hinwardRow] at hrenewal
    linarith

/-- ENNReal lower bounds for the two internal adjacent decisions. -/
theorem radialOneStepKernelENNReal_internal_ofReal_half_lower
    {n k : ℕ} (hn : 2 ≤ n) (hk : 1 ≤ k) (hkn : k + 1 ≤ n)
    (center start : Point)
    (hstart : start ∈ discBoundary center (scaleRadius n k))
    (hOuterNonempty : (profileOuterBoundary n k center).Nonempty) :
    let rowError := literalRealAnnulusRowError
      (scaleRadius n (k + 1)) (scaleRadius n k) (scaleRadius n (k - 1))
    ENNReal.ofReal ((1 - rowError) / 2) ≤
        radialOneStepKernelENNReal n center ⟨k, by omega⟩
          ⟨k + 1, by omega⟩ start ∧
      ENNReal.ofReal ((1 - rowError) / 2) ≤
        radialOneStepKernelENNReal n center ⟨k, by omega⟩
          ⟨k - 1, by omega⟩ start := by
  dsimp only
  have hbounds := radialOneStepKernelENNReal_internal_half_bounds
    hn hk hkn center start hstart hOuterNonempty
  constructor
  · apply (ENNReal.ofReal_le_iff_le_toReal (by
      unfold radialOneStepKernelENNReal
      exact measure_ne_top fairSteps _)).2
    exact hbounds.1
  · apply (ENNReal.ofReal_le_iff_le_toReal (by
      unfold radialOneStepKernelENNReal
      exact measure_ne_top fairSteps _)).2
    exact hbounds.2.2.1

/-- Eventually, uniformly over every internal profile level and every
spatial entrance, each adjacent chronological decision has mass at least
`(1-n⁻⁶)/2`. -/
theorem eventually_radialOneStepKernelENNReal_internal_lower_inv_pow_six :
    ∀ᶠ n : ℕ in atTop, ∀ k : ℕ, (hk : 0 < k) → (hkn : k + 1 ≤ n) →
      ∀ (center start : Point),
        start ∈ discBoundary center (scaleRadius n k) →
        ENNReal.ofReal ((1 - 1 / (n : ℝ) ^ 6) / 2) ≤
            radialOneStepKernelENNReal n center ⟨k, by omega⟩
              ⟨k + 1, by omega⟩ start ∧
          ENNReal.ofReal ((1 - 1 / (n : ℝ) ^ 6) / 2) ≤
            radialOneStepKernelENNReal n center ⟨k, by omega⟩
              ⟨k - 1, by omega⟩ start := by
  filter_upwards [eventually_profileRegularRowError_le_inv_pow_six,
      eventually_ge_atTop 2] with n herror hn
  intro k hk hkn center start hstart
  have houter : (profileOuterBoundary n k center).Nonempty := by
    apply discBoundary_center_nonempty_of_nonneg
    unfold scaleRadius regularRadius
    split_ifs <;> positivity
  have hbounds := radialOneStepKernelENNReal_internal_half_bounds
    hn hk hkn center start hstart houter
  constructor
  · apply (ENNReal.ofReal_le_iff_le_toReal (by
      unfold radialOneStepKernelENNReal
      exact measure_ne_top fairSteps _)).2
    calc
      (1 - 1 / (n : ℝ) ^ 6) / 2 ≤
          (1 - literalRealAnnulusRowError
            (scaleRadius n (k + 1)) (scaleRadius n k)
              (scaleRadius n (k - 1))) / 2 := by linarith [herror k hk hkn]
      _ ≤ _ := hbounds.1
  · apply (ENNReal.ofReal_le_iff_le_toReal (by
      unfold radialOneStepKernelENNReal
      exact measure_ne_top fairSteps _)).2
    calc
      (1 - 1 / (n : ℝ) ^ 6) / 2 ≤
          (1 - literalRealAnnulusRowError
            (scaleRadius n (k + 1)) (scaleRadius n k)
              (scaleRadius n (k - 1))) / 2 := by linarith [herror k hk hkn]
      _ ≤ _ := hbounds.2.2.1

/-! ## Initial and terminal chronological edges -/

/-- The initial `1 → 2` and `1 → 0` decisions are the `k = 1`
instance of the uniform regular-row estimate. -/
theorem eventually_radialOneStepKernelENNReal_initial_lower_inv_pow_six :
    ∀ᶠ n : ℕ in atTop, ∀ (hn : 2 ≤ n) (center start : Point),
      start ∈ radialBoundary n center ⟨1, by omega⟩ →
      ENNReal.ofReal ((1 - 1 / (n : ℝ) ^ 6) / 2) ≤
          radialOneStepKernelENNReal n center ⟨1, by omega⟩
            ⟨2, by omega⟩ start ∧
        ENNReal.ofReal ((1 - 1 / (n : ℝ) ^ 6) / 2) ≤
          radialOneStepKernelENNReal n center ⟨1, by omega⟩
            ⟨0, by omega⟩ start := by
  filter_upwards [eventually_radialOneStepKernelENNReal_internal_lower_inv_pow_six,
      eventually_ge_atTop 2] with n hrows hn
  intro _ center start hstart
  exact hrows 1 (by omega) (by omega) center start (by
    simpa [radialBoundary] using hstart)

/-- Exact reduction of the terminal inward decision `n → n+1` to the
literal annulus row.  This is structural and makes no asymptotic estimate. -/
theorem radialOneStepKernelENNReal_terminal_inward_toReal_eq
    {n : ℕ} (hn : 2 ≤ n) (center start : Point)
    (hstart : start ∈ radialBoundary n center ⟨n, by omega⟩) :
    (radialOneStepKernelENNReal n center ⟨n, by omega⟩
        ⟨n + 1, by omega⟩ start).toReal =
      ∑ z : ProfileCycleInnerPoint n n center,
        (skeletonExitKernel
          (profileInnerBoundary n (n + 1) center ∪
            profileOuterBoundary n n center) start z.1).toReal := by
  exact radialOneStepKernelENNReal_internal_inward_toReal_eq
    hn (by omega) le_rfl center start (by
      simpa [radialBoundary] using hstart)

/-- Exact reduction of the terminal outward decision `n → n-1` to the
complementary literal annulus row. -/
theorem radialOneStepKernelENNReal_terminal_outward_toReal_eq
    {n : ℕ} (hn : 2 ≤ n) (center start : Point)
    (hstart : start ∈ radialBoundary n center ⟨n, by omega⟩) :
    (radialOneStepKernelENNReal n center ⟨n, by omega⟩
        ⟨n - 1, by omega⟩ start).toReal =
      profileAnnularEscapeRowReal n n center
        ⟨start, mem_discBoundaryFinset.mpr (by
          simpa [radialBoundary] using hstart)⟩ := by
  exact radialOneStepKernelENNReal_internal_outward_toReal_eq
    hn (by omega) le_rfl center start (by
      simpa [radialBoundary] using hstart)

/-- From the innermost terminal boundary `n+1`, every different radial
boundary is reached through boundary `n`. -/
theorem terminalRadialBoundary_separates_other
    {n : ℕ} (hn : 2 ≤ n) (center start : Point)
    (hstart : start ∈ radialBoundary n center ⟨n + 1, by omega⟩) :
    FirstHitSeparates (radialBoundary n center ⟨n, by omega⟩)
      (otherRadialBoundaries n center ⟨n + 1, by omega⟩) start := by
  classical
  let source : Fin (n + 2) := ⟨n + 1, by omega⟩
  let barrier : Fin (n + 2) := ⟨n, by omega⟩
  intro path
  by_cases htop : boundaryExitTime
      (otherRadialBoundaries n center source) start path = ⊤
  · rw [htop]
    exact le_top
  · lift boundaryExitTime (otherRadialBoundaries n center source)
      start path to ℕ using htop with N hN
    have hotherTime : boundaryExitTime
        (otherRadialBoundaries n center source) start path = N := hN.symm
    have hspec := (firstHitSetAfter_eq_coe_iff zeroClock
      (BoundaryVisitLaw.relativeBoundary
        (otherRadialBoundaries n center source) start) path N).mp hotherTime
    have hNother : trajectoryFrom start path N ∈
        otherRadialBoundaries n center source := hspec.2.1
    unfold otherRadialBoundaries at hNother
    obtain ⟨exitLabel, hExit⟩ := Set.mem_iUnion.mp hNother
    have hExitNe : exitLabel ≠ source := by
      intro heq
      subst exitLabel
      simpa using hExit
    have hNExit : trajectoryFrom start path N ∈
        radialBoundary n center exitLabel := by
      simpa only [if_neg hExitNe] using hExit
    have hExitClock : boundaryExitTime
        (radialBoundary n center exitLabel) start path ≤ N := by
      apply (firstHitSetAfter_le_iff zeroClock
        (BoundaryVisitLaw.relativeBoundary
          (radialBoundary n center exitLabel) start) path N).mpr
      exact ⟨N, le_rfl, by simp [zeroClock], hNExit⟩
    have hExitLe : (exitLabel : ℕ) ≤ n := by
      have hbound : (exitLabel : ℕ) ≤ n + 1 := by omega
      have hne : (exitLabel : ℕ) ≠ n + 1 := by
        intro heq
        apply hExitNe
        apply Fin.ext
        simpa [source] using heq
      omega
    have hseparate : FirstHitSeparates
        (radialBoundary n center barrier)
        (radialBoundary n center exitLabel) start := by
      by_cases heq : (exitLabel : ℕ) = n
      · have hlabel : exitLabel = barrier := by
          apply Fin.ext
          simpa [barrier] using heq
        subst exitLabel
        exact FirstHitSeparates.of_subset (by intro z hz; exact hz)
      · apply FirstHitSeparates.discBoundaries
          (by simpa [radialBoundary, source] using hstart)
        · simpa [source, barrier] using
            (terminalRadius_le_regularRadius_self n (by omega))
        · exact scaleRadius_add_one_le_of_label_lt hn
            (show (exitLabel : ℕ) < (barrier : ℕ) by
              simpa [barrier] using (lt_of_le_of_ne hExitLe heq))
    calc
      boundaryExitTime (radialBoundary n center barrier) start path ≤
          boundaryExitTime (radialBoundary n center exitLabel) start path :=
        hseparate path
      _ ≤ (N : WithTop ℕ) := hExitClock
      _ = boundaryExitTime
          (otherRadialBoundaries n center source) start path := hotherTime.symm

/-- The all-other-boundaries clock from terminal level `n+1` is exactly the
first-hit clock of level `n`. -/
theorem boundaryExitTime_otherRadialBoundaries_terminal_eq
    {n : ℕ} (hn : 2 ≤ n) (center start : Point)
    (hstart : start ∈ radialBoundary n center ⟨n + 1, by omega⟩) :
    boundaryExitTime
        (otherRadialBoundaries n center ⟨n + 1, by omega⟩) start =
      boundaryExitTime (radialBoundary n center ⟨n, by omega⟩) start := by
  funext path
  apply le_antisymm
  · apply FirstHitSeparates.of_subset (start := start)
    intro z hz
    rw [otherRadialBoundaries]
    refine Set.mem_iUnion.mpr ⟨(⟨n, by omega⟩ : Fin (n + 2)), ?_⟩
    rw [if_neg (by intro heq; have := congrArg Fin.val heq; simp at this)]
    exact hz
  · exact terminalRadialBoundary_separates_other hn center start hstart path

/-- The terminal return `n+1 → n` is deterministic. -/
theorem radialOneStepKernelENNReal_terminal_return_eq_one
    {n : ℕ} (hn : 2 ≤ n) (center start : Point)
    (hstart : start ∈ radialBoundary n center ⟨n + 1, by omega⟩) :
    radialOneStepKernelENNReal n center ⟨n + 1, by omega⟩
        ⟨n, by omega⟩ start = 1 := by
  unfold radialOneStepKernelENNReal
  have hevent : radialOneStepAtom n center ⟨n + 1, by omega⟩
      ⟨n, by omega⟩ start =
      boundaryExitMarkedSteps (radialBoundary n center ⟨n, by omega⟩)
        (radialBoundary n center ⟨n, by omega⟩) start := by
    unfold radialOneStepAtom boundaryExitMarkedSteps
    rw [boundaryExitTime_otherRadialBoundaries_terminal_eq
      hn center start hstart]
  rw [hevent]
  have hboundary : (radialBoundary n center ⟨n, by omega⟩).Nonempty := by
    apply discBoundary_center_nonempty_of_nonneg
    rw [scaleRadius_of_le le_rfl, regularRadius_self]
    positivity
  have hmarked : boundaryExitMarkedSteps
      (radialBoundary n center ⟨n, by omega⟩)
        (radialBoundary n center ⟨n, by omega⟩) start =
      boundaryExitMarkedSteps (radialBoundary n center ⟨n, by omega⟩)
        Set.univ start := by
    ext path
    rw [mem_boundaryExitMarkedSteps_iff_exists_first,
      mem_boundaryExitMarkedSteps_iff_exists_first]
    constructor
    · rintro ⟨N, hfirst, _⟩
      exact ⟨N, hfirst, Set.mem_univ _⟩
    · rintro ⟨N, hfirst, _⟩
      exact ⟨N, hfirst, hfirst.1⟩
  rw [hmarked, fairSteps_boundaryExitMarkedSteps_univ_eq_one hboundary start]

end

end Erdos1165.AnnularRadialOneStepRow
