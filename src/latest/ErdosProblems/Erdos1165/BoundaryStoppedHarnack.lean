/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
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

import ErdosProblems.Erdos1165.TerminalExcursionDisintegration
import ErdosProblems.Erdos1165.RadialHarnackSpecialization

/-!
# Harnack comparison for the literal boundary-stopped terminal segment

The terminal visit segment ends at the next hit of the inner vertex boundary
of a Euclidean disc, whereas the earlier radial Harnack theorem stops one step
later, on leaving a closed lattice disc.  This module aligns the convention
exactly.  The finite killed domain is the graph interior obtained by removing
the inner vertex boundary from the closed disc.  A nearest-neighbor path
leaves that graph interior precisely by hitting the removed boundary.

We then prove the boundary-reference Green estimate for an arbitrary finite
domain in a coordinate box and apply the radial potential estimate to the
literal vertex boundary.  Thus the resulting `ConditionStar` theorem is for
`boundaryStoppedHitKernel` itself and needs no closed-disc-to-boundary bridge.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal Topology

namespace Erdos1165.BoundaryStoppedHarnack

open Annulus GreenFunction GreenProbability GreenAsymptotic GreenHarnack
open PlanarPotential PotentialConvergence
open PotentialEuclideanGeometry
open RadialHarnackSpecialization TerminalExcursionDisintegration ThickPoint

noncomputable section

/-- The finite graph interior of the real-radius disc: its inner vertex
boundary is removed. -/
noncomputable def boundaryInterior (R : ℕ) : Finset Point := by
  classical
  exact (closedDisc R).filter fun z ↦
    z ∉ ThickPoint.discBoundary 0 (R : ℝ)

@[simp] theorem mem_boundaryInterior {R : ℕ} {z : Point} :
    z ∈ boundaryInterior R ↔
      z ∈ closedDisc R ∧
        z ∉ ThickPoint.discBoundary 0 (R : ℝ) := by
  simp [boundaryInterior]

theorem mem_disc_zero_iff_mem_closedDisc (R : ℕ) (z : Point) :
    z ∈ ThickPoint.disc 0 (R : ℝ) ↔ z ∈ closedDisc R := by
  rw [ThickPoint.disc]
  change ThickPoint.latticeDistance 0 z ≤ (R : ℝ) ↔ _
  rw [latticeDistance_zero_eq_euclideanRadius]
  constructor
  · exact mem_closedDisc_of_euclideanRadius_le
  · exact euclideanRadius_le_of_mem_closedDisc

private theorem adjacent_neighbor (x : Point) (d : Direction) :
    ThickPoint.Adjacent x (neighbor x d) := by
  rcases x with ⟨x1, x2⟩
  fin_cases d <;> simp [ThickPoint.Adjacent, neighbor, directionVector]

/-- From a graph-interior vertex, every neighbor is either another interior
vertex or a vertex of the literal inner boundary. -/
theorem neighbor_mem_boundaryInterior_or_discBoundary
    {R : ℕ} {x : Point} (hx : x ∈ boundaryInterior R) (d : Direction) :
    neighbor x d ∈ boundaryInterior R ∨
      neighbor x d ∈ ThickPoint.discBoundary 0 (R : ℝ) := by
  have hxClosed := (mem_boundaryInterior.mp hx).1
  have hxNotBoundary := (mem_boundaryInterior.mp hx).2
  have hnClosed : neighbor x d ∈ closedDisc R := by
    by_contra hnClosed
    apply hxNotBoundary
    refine ⟨(mem_disc_zero_iff_mem_closedDisc R x).mpr hxClosed,
      neighbor x d, ?_, adjacent_neighbor x d⟩
    exact fun hnDisc ↦ hnClosed ((mem_disc_zero_iff_mem_closedDisc R _).mp hnDisc)
  by_cases hnBoundary :
      neighbor x d ∈ ThickPoint.discBoundary 0 (R : ℝ)
  · exact Or.inr hnBoundary
  · exact Or.inl (mem_boundaryInterior.mpr ⟨hnClosed, hnBoundary⟩)

theorem outerBoundary_boundaryInterior_subset_discBoundary (R : ℕ) :
    ∀ {z}, z ∈ outerBoundary (boundaryInterior R) →
      z ∈ ThickPoint.discBoundary 0 (R : ℝ) := by
  intro z hz
  rw [mem_outerBoundary] at hz
  obtain ⟨hzNot, x, hx, d, rfl⟩ := hz
  have hcases := neighbor_mem_boundaryInterior_or_discBoundary hx d
  exact hcases.resolve_left hzNot

theorem boundaryInterior_subset_coordinateBox (R : ℕ) :
    boundaryInterior R ⊆ coordinateBox R := by
  intro z hz
  exact (mem_closedDisc R z).mp (mem_boundaryInterior.mp hz).1 |>.1

/-- The first-hit clause in `walkHitBeforeExit` only chooses the least among
all admissible hit times; it does not change the union event. -/
theorem mem_walkHitBeforeExit_iff_exists
    (D : Finset Point) (target : Point) (s : WalkPath) :
    s ∈ walkHitBeforeExit D target ↔
      ∃ n, (∀ k ≤ n, s k ∈ D) ∧ s n = target := by
  constructor
  · intro h
    simp only [walkHitBeforeExit, mem_iUnion, mem_setOf_eq] at h
    obtain ⟨n, hn⟩ := h
    exact ⟨n, hn.1.1, hn.1.2⟩
  · rintro ⟨n, hstay, htarget⟩
    let P : ℕ → Prop := fun k ↦ s k = target
    have hP : ∃ k, P k := ⟨n, htarget⟩
    let first := Nat.find hP
    have hfirstLe : first ≤ n := Nat.find_min' hP htarget
    have hfirstTarget : s first = target := Nat.find_spec hP
    simp only [walkHitBeforeExit, mem_iUnion, mem_setOf_eq]
    refine ⟨first, ⟨⟨?_, hfirstTarget⟩, ?_⟩⟩
    · intro k hk
      exact hstay k (hk.trans hfirstLe)
    · intro k hk hktarget
      exact (Nat.find_min hP hk) hktarget

theorem mem_walkHitBeforeBoundary_iff_exists
    (boundary : Set Point) (target : Point) (s : WalkPath) :
    s ∈ walkHitBeforeBoundary boundary target ↔
      ∃ n, s n = target ∧ ∀ k < n, s k ∉ boundary := by
  simp only [walkHitBeforeBoundary, mem_iUnion, mem_setOf_eq]

private theorem trajectoryFrom_stays_boundaryInterior_until
    {R n : ℕ} {start target : Point} (omega : StepPath)
    (hstart : start ∈ boundaryInterior R)
    (htarget : target ∈ boundaryInterior R)
    (hnTarget : trajectoryFrom start omega n = target)
    (hnAvoid : ∀ k < n,
      trajectoryFrom start omega k ∉
        ThickPoint.discBoundary 0 (R : ℝ)) :
    ∀ k ≤ n, trajectoryFrom start omega k ∈ boundaryInterior R := by
  intro k hk
  induction k with
  | zero => simpa only [trajectoryFrom_zero] using hstart
  | succ k ih =>
      by_cases hkn : k + 1 = n
      · rw [hkn, hnTarget]
        exact htarget
      · have hklt : k + 1 < n := lt_of_le_of_ne hk hkn
        have hkprev : k ≤ n := (Nat.le_succ k).trans hk
        have hprev := ih hkprev
        have hcases :
            neighbor (trajectoryFrom start omega k) (omega k) ∈
                boundaryInterior R ∨
              neighbor (trajectoryFrom start omega k) (omega k) ∈
                ThickPoint.discBoundary 0 (R : ℝ) :=
          neighbor_mem_boundaryInterior_or_discBoundary hprev (omega k)
        have hstep : trajectoryFrom start omega (k + 1) =
            neighbor (trajectoryFrom start omega k) (omega k) := by
          rw [trajectoryFrom_succ]
          rfl
        have hnot : neighbor (trajectoryFrom start omega k) (omega k) ∉
            ThickPoint.discBoundary 0 (R : ℝ) := by
          rw [← hstep]
          exact hnAvoid (k + 1) hklt
        rw [hstep]
        exact hcases.resolve_right hnot

/-- On every canonical nearest-neighbor trajectory, hitting `target` before
the literal boundary is exactly hitting it before exiting the graph
interior. -/
theorem trajectoryFrom_mem_walkHitBeforeBoundary_iff
    {R : ℕ} {start target : Point}
    (hstart : start ∈ boundaryInterior R)
    (htarget : target ∈ boundaryInterior R) (omega : StepPath) :
    trajectoryFrom start omega ∈
        walkHitBeforeBoundary (ThickPoint.discBoundary 0 (R : ℝ)) target ↔
      trajectoryFrom start omega ∈
        walkHitBeforeExit (boundaryInterior R) target := by
  rw [mem_walkHitBeforeExit_iff_exists]
  constructor
  · intro h
    rw [mem_walkHitBeforeBoundary_iff_exists] at h
    obtain ⟨n, hnTarget, hnAvoid⟩ := h
    exact ⟨n,
      trajectoryFrom_stays_boundaryInterior_until omega hstart htarget
        hnTarget hnAvoid,
      hnTarget⟩
  · rintro ⟨n, hstay, hnTarget⟩
    rw [mem_walkHitBeforeBoundary_iff_exists]
    refine ⟨n, hnTarget, ?_⟩
    intro k hk hkBoundary
    exact (mem_boundaryInterior.mp (hstay k hk.le)).2 hkBoundary

/-- Exact probability bridge from the literal half-open boundary convention
to the killed Green domain.  This is an equality, not the false comparison
with exit from the full closed disc. -/
theorem boundaryStoppedHitKernel_eq_boundaryInteriorHitKernel
    (R : ℕ) {start target : Point}
    (hstart : start ∈ boundaryInterior R)
    (htarget : target ∈ boundaryInterior R) :
    boundaryStoppedHitKernel
        (ThickPoint.discBoundary 0 (R : ℝ)) target start =
      (simpleRandomWalkFrom start
        (walkHitBeforeExit (boundaryInterior R) target)).toReal := by
  apply congrArg ENNReal.toReal
  unfold simpleRandomWalkFrom
  rw [Measure.map_apply (measurable_trajectoryFrom start)
      (measurableSet_walkHitBeforeBoundary _ _),
    Measure.map_apply (measurable_trajectoryFrom start)
      (measurableSet_walkHitBeforeExit _ _)]
  congr 1
  ext omega
  exact trajectoryFrom_mem_walkHitBeforeBoundary_iff hstart htarget omega

/-! ## Translation to a terminal disc with arbitrary center -/

theorem latticeDistance_translate (center z : Point) :
    ThickPoint.latticeDistance center z =
      ThickPoint.latticeDistance 0 (z - center) := by
  unfold ThickPoint.latticeDistance ThickPoint.squaredDistance
  congr 1
  rcases center with ⟨c1, c2⟩
  rcases z with ⟨z1, z2⟩
  norm_num

theorem mem_disc_translate (center : Point) (r : ℝ) (z : Point) :
    z ∈ ThickPoint.disc center r ↔
      z - center ∈ ThickPoint.disc 0 r := by
  change ThickPoint.latticeDistance center z ≤ r ↔
    ThickPoint.latticeDistance 0 (z - center) ≤ r
  constructor
  · intro h
    rw [latticeDistance_translate center z] at h
    exact h
  · intro h
    rw [latticeDistance_translate center z]
    exact h

theorem adjacent_translate (center z w : Point) :
    ThickPoint.Adjacent z w ↔
      ThickPoint.Adjacent (z - center) (w - center) := by
  rcases center with ⟨c1, c2⟩
  rcases z with ⟨z1, z2⟩
  rcases w with ⟨w1, w2⟩
  unfold ThickPoint.Adjacent
  change (z1 - w1).natAbs + (z2 - w2).natAbs = 1 ↔
    ((z1 - c1) - (w1 - c1)).natAbs +
      ((z2 - c2) - (w2 - c2)).natAbs = 1
  have hfirst : z1 - w1 = (z1 - c1) - (w1 - c1) := by ring
  have hsecond : z2 - w2 = (z2 - c2) - (w2 - c2) := by ring
  rw [← hfirst, ← hsecond]

theorem mem_discBoundary_translate (center : Point) (r : ℝ) (z : Point) :
    z ∈ ThickPoint.discBoundary center r ↔
      z - center ∈ ThickPoint.discBoundary 0 r := by
  unfold ThickPoint.discBoundary ThickPoint.innerBoundary
  simp only [mem_setOf_eq]
  constructor
  · rintro ⟨hz, w, hw, hzw⟩
    refine ⟨(mem_disc_translate center r z).mp hz, w - center, ?_, ?_⟩
    · exact fun hw' ↦ hw ((mem_disc_translate center r w).mpr hw')
    · exact (adjacent_translate center z w).mp hzw
  · rintro ⟨hz, w, hw, hzw⟩
    refine ⟨(mem_disc_translate center r z).mpr hz, w + center, ?_, ?_⟩
    · intro hwOriginal
      apply hw
      have htranslated :=
        (mem_disc_translate center r (w + center)).mp hwOriginal
      simpa using htranslated
    · apply (adjacent_translate center z (w + center)).mpr
      simpa using hzw

theorem trajectoryFrom_sub_center
    (start center : Point) (omega : StepPath) (n : ℕ) :
    trajectoryFrom start omega n - center =
      trajectoryFrom (start - center) omega n := by
  unfold trajectoryFrom
  abel

theorem trajectoryFrom_mem_centered_walkHitBeforeBoundary_iff
    (R : ℕ) (center start : Point) (omega : StepPath) :
    trajectoryFrom start omega ∈
        walkHitBeforeBoundary
          (ThickPoint.discBoundary center (R : ℝ)) center ↔
      trajectoryFrom (start - center) omega ∈
        walkHitBeforeBoundary
          (ThickPoint.discBoundary 0 (R : ℝ)) 0 := by
  rw [mem_walkHitBeforeBoundary_iff_exists,
    mem_walkHitBeforeBoundary_iff_exists]
  constructor
  · rintro ⟨n, hn, havoid⟩
    refine ⟨n, ?_, ?_⟩
    · have hsub := congrArg (fun z : Point ↦ z - center) hn
      simpa only [trajectoryFrom_sub_center, sub_self] using hsub
    · intro k hk hkBoundary
      apply havoid k hk
      apply (mem_discBoundary_translate center (R : ℝ) _).mpr
      simpa only [trajectoryFrom_sub_center] using hkBoundary
  · rintro ⟨n, hn, havoid⟩
    refine ⟨n, ?_, ?_⟩
    · have hsub : trajectoryFrom start omega n - center = 0 := by
        simpa only [trajectoryFrom_sub_center] using hn
      exact sub_eq_zero.mp hsub
    · intro k hk hkBoundary
      apply havoid k hk
      have htranslated :=
        (mem_discBoundary_translate center (R : ℝ) _).mp hkBoundary
      simpa only [trajectoryFrom_sub_center] using htranslated

/-- Translation reduces the literal boundary-stopped kernel around an
arbitrary target to the origin-centered kernel used below. -/
theorem boundaryStoppedHitKernel_centered_eq_zero
    (R : ℕ) (center start : Point) :
    boundaryStoppedHitKernel
        (ThickPoint.discBoundary center (R : ℝ)) center start =
      boundaryStoppedHitKernel
        (ThickPoint.discBoundary 0 (R : ℝ)) 0 (start - center) := by
  apply congrArg ENNReal.toReal
  unfold simpleRandomWalkFrom
  rw [Measure.map_apply (measurable_trajectoryFrom start)
      (measurableSet_walkHitBeforeBoundary _ _),
    Measure.map_apply (measurable_trajectoryFrom (start - center))
      (measurableSet_walkHitBeforeBoundary _ _)]
  congr 1
  ext omega
  exact trajectoryFrom_mem_centered_walkHitBeforeBoundary_iff
    R center start omega

/-! ## Boundary-reference Green estimate for an arbitrary finite domain -/

/-- The sharp boundary-reference Green estimate does not depend on the domain
being the full closed disc.  An interior correction is bounded by a finite
constant times the killed survival mass, which tends to zero in a coordinate
box. -/
theorem abs_infiniteGreen_toReal_sub_boundaryReference_le_of_subset_coordinateBox
    (D : Finset Point) (boxRadius : ℕ) {x target q : Point}
    (hx : x ∈ D) (hD : D ⊆ coordinateBox boxRadius)
    {epsilon : ℝ} (hepsilon0 : 0 ≤ epsilon)
    (hepsilon : ∀ z, z ∈ outerBoundary D →
      |planarPotentialKernel (z - target) -
        planarPotentialKernel (q - target)| ≤ epsilon) :
    |(infiniteGreen D x target).toReal -
        (planarPotentialKernel (q - target) -
          planarPotentialKernel (x - target))| ≤ epsilon := by
  let K : ℝ := ∑ z ∈ D,
    |planarPotentialKernel (z - target) -
      planarPotentialKernel (q - target)|
  let difference : Point → ℝ := fun z ↦
    planarPotentialKernel (z - target) -
      planarPotentialKernel (q - target)
  let envelope : Point → ℝ := fun z ↦
    epsilon + K * (if z ∈ D then 1 else 0)
  have hK0 : 0 ≤ K := Finset.sum_nonneg fun z _ ↦ abs_nonneg _
  have hpoint (z : Point) (hz : z ∈ D ∨ z ∈ outerBoundary D) :
      |difference z| ≤ envelope z := by
    rcases hz with hzD | hzBoundary
    · have hsingle : |planarPotentialKernel (z - target) -
          planarPotentialKernel (q - target)| ≤ K := by
        dsimp only [K]
        exact Finset.single_le_sum
          (fun w _ ↦ abs_nonneg
            (planarPotentialKernel (w - target) -
              planarPotentialKernel (q - target))) hzD
      simp only [difference, envelope, hzD, if_true, mul_one]
      linarith
    · have hzNotD : z ∉ D := (mem_outerBoundary D z).mp hzBoundary |>.1
      simpa only [difference, envelope, hzNotD, if_false, mul_zero, add_zero]
        using hepsilon z hzBoundary
  have hupperPoint (z : Point) (hz : z ∈ D ∨ z ∈ outerBoundary D) :
      difference z ≤ envelope z :=
    (le_abs_self _).trans (hpoint z hz)
  have hlowerPoint (z : Point) (hz : z ∈ D ∨ z ∈ outerBoundary D) :
      -envelope z ≤ difference z :=
    by
      have hp := hpoint z hz
      have ha := neg_abs_le (difference z)
      linarith
  have hupperFinite (N : ℕ) :
      stoppedExpectation D (N + 1) difference x ≤
        stoppedExpectation D (N + 1) envelope x :=
    stoppedExpectation_mono_of_mem_or_outerBoundary D hupperPoint (N + 1)
      (Or.inl hx)
  have hlowerFinite (N : ℕ) :
      stoppedExpectation D (N + 1) (fun z ↦ -envelope z) x ≤
        stoppedExpectation D (N + 1) difference x :=
    stoppedExpectation_mono_of_mem_or_outerBoundary D hlowerPoint (N + 1)
      (Or.inl hx)
  have hfinite : infiniteGreen D x target ≠ ⊤ :=
    infiniteGreen_ne_top_of_subset_coordinateBox D boxRadius x target hD
  have hpotential := tendsto_stoppedExpectation_potential_of_finite
    D x target hfinite
  have hdifference : Tendsto
      (fun N ↦ stoppedExpectation D (N + 1) difference x) atTop
      (nhds (planarPotentialKernel (x - target) +
        (infiniteGreen D x target).toReal -
          planarPotentialKernel (q - target))) := by
    have hconst : Tendsto
        (fun _N : ℕ ↦ planarPotentialKernel (q - target)) atTop
        (nhds (planarPotentialKernel (q - target))) := tendsto_const_nhds
    have hsub := hpotential.sub hconst
    convert hsub using 1
    funext N
    simp only [difference, stoppedExpectation_sub, stoppedExpectation_const]
  have hsurvive :=
    tendsto_planarKilledMass_toReal_of_subset_coordinateBox_zero
      D boxRadius x hD
  have henvelope : Tendsto
      (fun N ↦ stoppedExpectation D (N + 1) envelope x) atTop
      (nhds epsilon) := by
    have hraw : Tendsto
        (fun N ↦ epsilon + K *
          (planarKilledMass D (N + 1) x).toReal) atTop
        (nhds (epsilon + K * 0)) :=
      tendsto_const_nhds.add
        ((hsurvive.comp (tendsto_add_atTop_nat 1)).const_mul K)
    convert hraw using 1
    · funext N
      simp only [envelope, stoppedExpectation_add,
        stoppedExpectation_const, stoppedExpectation_const_mul,
        stoppedExpectation_interiorIndicator_eq_planarKilledMass]
    · ring_nf
  have hnegativeEnvelope : Tendsto
      (fun N ↦ stoppedExpectation D (N + 1) (fun z ↦ -envelope z) x)
      atTop (nhds (-epsilon)) := by
    have hneg := henvelope.neg
    refine hneg.congr' (Filter.Eventually.of_forall fun N ↦ ?_)
    rw [show (fun z ↦ -envelope z) = fun z ↦ (-1 : ℝ) * envelope z by
      funext z
      ring]
    change -stoppedExpectation D (N + 1) envelope x =
      stoppedExpectation D (N + 1) (fun z ↦ (-1 : ℝ) * envelope z) x
    rw [stoppedExpectation_const_mul]
    ring
  have hupper := le_of_tendsto_of_tendsto'
    hdifference henvelope hupperFinite
  have hlower := le_of_tendsto_of_tendsto'
    hnegativeEnvelope hdifference hlowerFinite
  rw [abs_le]
  constructor <;> linarith

theorem simpleRandomWalkFrom_hitBeforeExit_toReal_eq_green_div_of_subset_coordinateBox
    (D : Finset Point) (boxRadius : ℕ) (x target : Point)
    (hD : D ⊆ coordinateBox boxRadius) (htarget : target ∈ D) :
    (simpleRandomWalkFrom x (walkHitBeforeExit D target)).toReal =
      (infiniteGreen D x target).toReal /
        (infiniteGreen D target target).toReal := by
  rw [simpleRandomWalkFrom_hitBeforeExit_eq_green_div_of_subset_coordinateBox
    D boxRadius x target hD htarget, ENNReal.toReal_div]

theorem one_le_infiniteGreen_diagonal_toReal_of_subset_coordinateBox
    (D : Finset Point) (boxRadius : ℕ) {target : Point}
    (hD : D ⊆ coordinateBox boxRadius) (htarget : target ∈ D) :
    1 ≤ (infiniteGreen D target target).toReal := by
  have hone : (1 : ℝ≥0∞) ≤ infiniteGreen D target target := by
    have hzero : killedPower planarKernel D 0 target target ≤
        ∑' n, killedPower planarKernel D n target target := ENNReal.le_tsum 0
    simpa [infiniteGreen, killedPower, htarget] using hzero
  exact ENNReal.toReal_mono
    (infiniteGreen_ne_top_of_subset_coordinateBox
      D boxRadius target target hD) hone

/-- Multiplicative Harnack comparison in an arbitrary finite killed domain,
using only potential oscillation on its actual one-step exit boundary. -/
theorem hitBeforeExit_compare_of_boundaryReference
    (D : Finset Point) (boxRadius : ℕ) {target x y q : Point}
    (htarget : target ∈ D) (hx : x ∈ D) (hy : y ∈ D)
    (hD : D ⊆ coordinateBox boxRadius)
    {boundaryError startError lower : ℝ}
    (hboundaryNonneg : 0 ≤ boundaryError)
    (hboundary : ∀ z, z ∈ outerBoundary D →
      |planarPotentialKernel (z - target) -
        planarPotentialKernel (q - target)| ≤ boundaryError)
    (hstartNonneg : 0 ≤ startError)
    (hstart : |planarPotentialKernel (y - target) -
      planarPotentialKernel (x - target)| ≤ startError)
    (hlower : 0 < lower)
    (href : lower ≤ planarPotentialKernel (q - target) -
      planarPotentialKernel (x - target) - boundaryError) :
    let error := 2 * boundaryError + startError
    (1 - error / lower) *
        (simpleRandomWalkFrom x (walkHitBeforeExit D target)).toReal ≤
      (simpleRandomWalkFrom y (walkHitBeforeExit D target)).toReal ∧
    (simpleRandomWalkFrom y (walkHitBeforeExit D target)).toReal ≤
      (1 + error / lower) *
        (simpleRandomWalkFrom x (walkHitBeforeExit D target)).toReal := by
  dsimp only
  let gx := (infiniteGreen D x target).toReal
  let gy := (infiniteGreen D y target).toReal
  let diagonal := (infiniteGreen D target target).toReal
  have hxApprox :=
    abs_infiniteGreen_toReal_sub_boundaryReference_le_of_subset_coordinateBox
      D boxRadius hx hD hboundaryNonneg hboundary
  have hyApprox :=
    abs_infiniteGreen_toReal_sub_boundaryReference_le_of_subset_coordinateBox
      D boxRadius hy hD hboundaryNonneg hboundary
  have hxBounds := abs_le.mp hxApprox
  have hyBounds := abs_le.mp hyApprox
  have hxLower :
      (planarPotentialKernel (q - target) - boundaryError) -
          planarPotentialKernel (x - target) ≤ gx := by
    dsimp only [gx]
    linarith
  have hxUpper : gx ≤
      (planarPotentialKernel (q - target) + boundaryError) -
        planarPotentialKernel (x - target) := by
    dsimp only [gx]
    linarith
  have hyLower :
      (planarPotentialKernel (q - target) - boundaryError) -
          planarPotentialKernel (y - target) ≤ gy := by
    dsimp only [gy]
    linarith
  have hyUpper : gy ≤
      (planarPotentialKernel (q - target) + boundaryError) -
        planarPotentialKernel (y - target) := by
    dsimp only [gy]
    linarith
  have hdiff : |gy - gx| ≤ 2 * boundaryError + startError := by
    dsimp only [gx, gy]
    rw [abs_le] at hstart ⊢
    constructor <;> linarith
  have herror : 0 ≤ 2 * boundaryError + startError := by linarith
  have hgreenLower : lower ≤ gx := by
    dsimp only [gx]
    exact href.trans (by linarith [hxBounds.1])
  have hmult := AnnulusHarnack.multiplicative_compare_of_additive
    herror hlower hgreenLower hdiff
  have hdiagonal : 0 < diagonal := by
    dsimp only [diagonal]
    exact lt_of_lt_of_le zero_lt_one
      (one_le_infiniteGreen_diagonal_toReal_of_subset_coordinateBox
        D boxRadius hD htarget)
  have hpx :=
    simpleRandomWalkFrom_hitBeforeExit_toReal_eq_green_div_of_subset_coordinateBox
      D boxRadius x target hD htarget
  have hpy :=
    simpleRandomWalkFrom_hitBeforeExit_toReal_eq_green_div_of_subset_coordinateBox
      D boxRadius y target hD htarget
  dsimp only [gx, gy, diagonal] at hmult ⊢
  rw [hpx, hpy]
  constructor
  · calc
      (1 - (2 * boundaryError + startError) / lower) *
          ((infiniteGreen D x target).toReal /
            (infiniteGreen D target target).toReal) =
        ((1 - (2 * boundaryError + startError) / lower) *
          (infiniteGreen D x target).toReal) /
            (infiniteGreen D target target).toReal := by ring
      _ ≤ (infiniteGreen D y target).toReal /
            (infiniteGreen D target target).toReal :=
        div_le_div_of_nonneg_right hmult.1 hdiagonal.le
  · calc
      (infiniteGreen D y target).toReal /
            (infiniteGreen D target target).toReal ≤
        ((1 + (2 * boundaryError + startError) / lower) *
          (infiniteGreen D x target).toReal) /
            (infiniteGreen D target target).toReal :=
        div_le_div_of_nonneg_right hmult.2 hdiagonal.le
      _ = (1 + (2 * boundaryError + startError) / lower) *
          ((infiniteGreen D x target).toReal /
            (infiniteGreen D target target).toReal) := by ring

/-! ## Literal Euclidean-boundary specialization -/

/-- A literal inner vertex boundary of the radius-`R` disc lies in the
unit-thick shell `(R-1,R]`. -/
theorem discBoundary_zero_euclideanRadius_bounds_nat
    {R : ℕ} (hR : 1 ≤ R) {z : Point}
    (hz : z ∈ ThickPoint.discBoundary 0 (R : ℝ)) :
    ((R - 1 : ℕ) : ℝ) < euclideanRadius z ∧
      euclideanRadius z ≤ R := by
  have hRdecomp : R - 1 + 1 = R := Nat.sub_add_cancel hR
  have hcast : ((R : ℝ)) = ((R - 1 : ℕ) : ℝ) + 1 := by
    exact_mod_cast hRdecomp.symm
  have hz' : z ∈ ThickPoint.discBoundary 0
      (((R - 1 : ℕ) : ℝ) + 1) := by
    rwa [← hcast]
  have hbounds :=
    discBoundary_zero_euclideanRadius_bounds (rho := R - 1) hz'
  simpa only [hcast] using hbounds

theorem zero_mem_boundaryInterior {R : ℕ} (hR : 1 ≤ R) :
    (0 : Point) ∈ boundaryInterior R := by
  rw [mem_boundaryInterior]
  constructor
  · rw [mem_closedDisc_iff_radiusSqInt_le]
    simp [radiusSqInt]
  · intro hzeroBoundary
    have hlower :=
      (discBoundary_zero_euclideanRadius_bounds_nat hR hzeroBoundary).1
    have hnonneg : (0 : ℝ) ≤ (R - 1 : ℕ) := by positivity
    have hzeroRadius : euclideanRadius (0 : Point) = 0 := by
      simp [PotentialEuclideanGeometry.euclideanRadius,
        PotentialEuclideanGeometry.euclideanRadiusSq]
    rw [hzeroRadius] at hlower
    linarith

/-- The potential oscillation error on the literal vertex boundary. -/
def literalBoundaryError (R : ℕ) : ℝ :=
  euclideanShellError (R - 1)

theorem literalBoundaryError_nonneg (R : ℕ) :
    0 ≤ literalBoundaryError R :=
  euclideanShellError_nonneg (R - 1)

/-- Uniform radial potential oscillation on the actual vertex boundary at
which the terminal segment stops. -/
theorem discBoundary_potential_oscillation_le_literalBoundaryError
    {R : ℕ} (hR : 5 ≤ R) {q : Point}
    (hq : q ∈ ThickPoint.discBoundary 0 (R : ℝ)) :
    ∀ z, z ∈ ThickPoint.discBoundary 0 (R : ℝ) →
      |planarPotentialKernel z - planarPotentialKernel q| ≤
        literalBoundaryError R := by
  intro z hz
  have hR1 : 1 ≤ R := hR.trans' (by norm_num)
  have hrho : 4 ≤ R - 1 := by omega
  have hwidth : (R : ℝ) = ((R - 1 : ℕ) : ℝ) + 1 := by
    exact_mod_cast (Nat.sub_add_cancel hR1).symm
  have hqBounds := discBoundary_zero_euclideanRadius_bounds_nat hR1 hq
  have hzBounds := discBoundary_zero_euclideanRadius_bounds_nat hR1 hz
  apply abs_planarPotentialKernel_sub_le_of_euclideanRadius_gap
  · exact hrho
  · exact hqBounds.1.le
  · exact hzBounds.1.le
  · rw [abs_le]
    constructor <;> linarith

/-- Sharp Harnack comparison for hitting the target before the next visit to
the literal boundary. -/
theorem boundaryStoppedHit_compare_of_euclideanShells
    (R rho : ℕ) {lower : ℝ} {x y q : Point}
    (hR : 5 ≤ R)
    (hq : q ∈ ThickPoint.discBoundary 0 (R : ℝ))
    (hx : x ∈ boundaryInterior R) (hy : y ∈ boundaryInterior R)
    (hrho : 4 ≤ rho)
    (hxrho : (rho : ℝ) ≤ euclideanRadius x)
    (hyrho : (rho : ℝ) ≤ euclideanRadius y)
    (hxygap : |euclideanRadius x - euclideanRadius y| ≤ 1)
    (hlower : 0 < lower)
    (href : lower ≤ planarPotentialKernel q - planarPotentialKernel x -
      literalBoundaryError R) :
    let error :=
      (2 * literalBoundaryError R + euclideanShellError rho) / lower
    (1 - error) *
        boundaryStoppedHitKernel
          (ThickPoint.discBoundary 0 (R : ℝ)) 0 x ≤
      boundaryStoppedHitKernel
        (ThickPoint.discBoundary 0 (R : ℝ)) 0 y ∧
    boundaryStoppedHitKernel
        (ThickPoint.discBoundary 0 (R : ℝ)) 0 y ≤
      (1 + error) *
        boundaryStoppedHitKernel
          (ThickPoint.discBoundary 0 (R : ℝ)) 0 x := by
  dsimp only
  have hzero : (0 : Point) ∈ boundaryInterior R :=
    zero_mem_boundaryInterior (hR.trans' (by norm_num))
  have hboundary : ∀ z, z ∈ outerBoundary (boundaryInterior R) →
      |planarPotentialKernel (z - 0) - planarPotentialKernel (q - 0)| ≤
        literalBoundaryError R := by
    intro z hz
    have hzBoundary :=
      outerBoundary_boundaryInterior_subset_discBoundary R hz
    simpa using
      discBoundary_potential_oscillation_le_literalBoundaryError hR hq z hzBoundary
  have hcompare := hitBeforeExit_compare_of_boundaryReference
    (boundaryInterior R) R hzero hx hy
    (boundaryInterior_subset_coordinateBox R)
    (literalBoundaryError_nonneg R) hboundary
    (euclideanShellError_nonneg rho)
    (by
      simpa using
        (abs_planarPotentialKernel_sub_le_of_euclideanRadius_gap
          hrho hxrho hyrho hxygap))
    hlower (by simpa using href)
  rw [← boundaryStoppedHitKernel_eq_boundaryInteriorHitKernel R hx hzero,
    ← boundaryStoppedHitKernel_eq_boundaryInteriorHitKernel R hy hzero]
    at hcompare
  simpa only [div_eq_mul_inv] using hcompare

/-- Literal boundary-stopped hit probability as a kernel on a finite
entrance space. -/
def literalBoundaryStoppedHitKernel {Entrance : Type*} (R : ℕ)
    (entrance : Entrance → Point) (u : Entrance) : ℝ :=
  boundaryStoppedHitKernel
    (ThickPoint.discBoundary 0 (R : ℝ)) 0 (entrance u)

def literalBoundaryHitError (R rho : ℕ) (lower : ℝ) : ℝ :=
  (2 * literalBoundaryError R + euclideanShellError rho) / lower

/-- Condition `(star)` directly for the half-open boundary-stopped
one-excursion kernel.  No closed-disc-to-boundary predicate remains. -/
theorem conditionStar_literalBoundaryStoppedHitKernel_of_euclideanShells
    {Entrance : Type*} [Fintype Entrance]
    (R rho : ℕ) {lower : ℝ} (q : Point) (entrance : Entrance → Point)
    (hR : 5 ≤ R)
    (hq : q ∈ ThickPoint.discBoundary 0 (R : ℝ))
    (hinside : ∀ u, entrance u ∈ boundaryInterior R)
    (hrho : 4 ≤ rho)
    (hradius : ∀ u, (rho : ℝ) ≤ euclideanRadius (entrance u))
    (hgap : ∀ u v,
      |euclideanRadius (entrance u) - euclideanRadius (entrance v)| ≤ 1)
    (hlower : 0 < lower)
    (href : ∀ u, lower ≤ planarPotentialKernel q -
      planarPotentialKernel (entrance u) - literalBoundaryError R) :
    AppendixDecoupling.ConditionStar
      (literalBoundaryHitError R rho lower)
      (literalBoundaryStoppedHitKernel R entrance) := by
  intro u v
  simpa [literalBoundaryHitError, literalBoundaryStoppedHitKernel] using
    boundaryStoppedHit_compare_of_euclideanShells
      R rho hR hq (hinside u) (hinside v) hrho
      (hradius u) (hradius v) (hgap u v) hlower (href u)

/-- If the inner terminal boundary is at least one full lattice step inside
the outer radius, every packaged terminal entrance belongs to the exact graph
interior. -/
theorem terminalEntrance_mem_boundaryInterior
    {R rho : ℕ} (hseparated : rho + 2 ≤ R)
    (u : terminalEntrance R rho) :
    terminalEntrancePoint u ∈ boundaryInterior R := by
  rw [mem_boundaryInterior]
  refine ⟨u.1.2, ?_⟩
  intro huOuter
  have hR1 : 1 ≤ R := by omega
  have houterLower :=
    (discBoundary_zero_euclideanRadius_bounds_nat hR1 huOuter).1
  have hinnerUpper :=
    (discBoundary_zero_euclideanRadius_bounds u.2).2
  have hcast : ((rho + 1 : ℕ) : ℝ) ≤ (R - 1 : ℕ) := by
    exact_mod_cast (show rho + 1 ≤ R - 1 by omega)
  have hinnerUpper' :
      euclideanRadius (terminalEntrancePoint u) ≤ (rho + 1 : ℕ) := by
    simpa [terminalEntrancePoint] using hinnerUpper
  linarith

/-- Fully specialized literal terminal-entrance Condition `(star)`.  The
inner/outer boundary separation discharges membership in the exact killed
domain, and the terminal entrance definition discharges the start-shell
geometry. -/
theorem conditionStar_terminalEntrance_boundaryStoppedHitKernel
    (R rho : ℕ) {lower : ℝ} (q : Point)
    (hR : 5 ≤ R) (hseparated : rho + 2 ≤ R)
    (hq : q ∈ ThickPoint.discBoundary 0 (R : ℝ))
    (hrho : 4 ≤ rho) (hlower : 0 < lower)
    (href : ∀ u : terminalEntrance R rho,
      lower ≤ planarPotentialKernel q -
        planarPotentialKernel (terminalEntrancePoint u) -
          literalBoundaryError R) :
    AppendixDecoupling.ConditionStar
      (literalBoundaryHitError R rho lower)
      (literalBoundaryStoppedHitKernel R
        (@terminalEntrancePoint R rho)) := by
  exact conditionStar_literalBoundaryStoppedHitKernel_of_euclideanShells
    R rho q (@terminalEntrancePoint R rho) hR hq
    (terminalEntrance_mem_boundaryInterior hseparated) hrho
    terminalEntrance_radius_lower terminalEntrance_radius_gap hlower href

/-! ## Arbitrary-center terminal kernel -/

/-- The literal terminal hit kernel without translating the path data. -/
def centeredBoundaryStoppedHitKernel {Entrance : Type*} (R : ℕ)
    (center : Point) (entrance : Entrance → Point) (u : Entrance) : ℝ :=
  boundaryStoppedHitKernel
    (ThickPoint.discBoundary center (R : ℝ)) center (entrance u)

/-- Centered version of the direct boundary-stopped Condition `(star)`.
All analytic hypotheses are expressed in coordinates relative to `center`,
while the conclusion is the literal unshifted walk kernel. -/
theorem conditionStar_centeredBoundaryStoppedHitKernel_of_euclideanShells
    {Entrance : Type*} [Fintype Entrance]
    (R rho : ℕ) {lower : ℝ} (center q : Point)
    (entrance : Entrance → Point)
    (hR : 5 ≤ R)
    (hq : q ∈ ThickPoint.discBoundary center (R : ℝ))
    (hinside : ∀ u, entrance u - center ∈ boundaryInterior R)
    (hrho : 4 ≤ rho)
    (hradius : ∀ u,
      (rho : ℝ) ≤ euclideanRadius (entrance u - center))
    (hgap : ∀ u v,
      |euclideanRadius (entrance u - center) -
        euclideanRadius (entrance v - center)| ≤ 1)
    (hlower : 0 < lower)
    (href : ∀ u, lower ≤ planarPotentialKernel (q - center) -
      planarPotentialKernel (entrance u - center) - literalBoundaryError R) :
    AppendixDecoupling.ConditionStar
      (literalBoundaryHitError R rho lower)
      (centeredBoundaryStoppedHitKernel R center entrance) := by
  have hq0 : q - center ∈ ThickPoint.discBoundary 0 (R : ℝ) :=
    (mem_discBoundary_translate center (R : ℝ) q).mp hq
  have hstar :=
    conditionStar_literalBoundaryStoppedHitKernel_of_euclideanShells
      R rho (q - center) (fun u ↦ entrance u - center)
      hR hq0 hinside hrho hradius hgap hlower href
  intro u v
  have huv := hstar u v
  unfold centeredBoundaryStoppedHitKernel
  rw [boundaryStoppedHitKernel_centered_eq_zero R center (entrance u),
    boundaryStoppedHitKernel_centered_eq_zero R center (entrance v)]
  simpa only [literalBoundaryStoppedHitKernel] using huv

theorem centeredInnerBoundary_shift_mem_boundaryInterior
    {R rho : ℕ} {center z : Point} (hseparated : rho + 2 ≤ R)
    (hz : z ∈ ThickPoint.discBoundary center ((rho : ℝ) + 1)) :
    z - center ∈ boundaryInterior R := by
  have hz0 : z - center ∈
      ThickPoint.discBoundary 0 ((rho : ℝ) + 1) :=
    (mem_discBoundary_translate center ((rho : ℝ) + 1) z).mp hz
  have hbounds :=
    discBoundary_zero_euclideanRadius_bounds (rho := rho) hz0
  have hrhoR : (rho + 1 : ℕ) ≤ R := by omega
  have hclosed : z - center ∈ closedDisc R := by
    apply mem_closedDisc_of_euclideanRadius_le
    have hcast : ((rho + 1 : ℕ) : ℝ) ≤ R := by exact_mod_cast hrhoR
    have hupper : euclideanRadius (z - center) ≤ (rho + 1 : ℕ) := by
      simpa only [Nat.cast_add, Nat.cast_one] using hbounds.2
    exact hupper.trans hcast
  let u : terminalEntrance R rho :=
    ⟨⟨z - center, hclosed⟩, by
      simpa only [Nat.cast_add, Nat.cast_one] using hz0⟩
  exact terminalEntrance_mem_boundaryInterior hseparated u

/-- Final terminal-boundary specialization.  Entrances lie on the literal
inner vertex boundary and the walk stops on the literal outer vertex
boundary, both around the same arbitrary target. -/
theorem conditionStar_centeredTerminalBoundaryStoppedHitKernel
    {Entrance : Type*} [Fintype Entrance]
    (R rho : ℕ) {lower : ℝ} (center q : Point)
    (entrance : Entrance → Point)
    (hR : 5 ≤ R) (hseparated : rho + 2 ≤ R)
    (hq : q ∈ ThickPoint.discBoundary center (R : ℝ))
    (hentrance : ∀ u,
      entrance u ∈ ThickPoint.discBoundary center ((rho : ℝ) + 1))
    (hrho : 4 ≤ rho) (hlower : 0 < lower)
    (href : ∀ u, lower ≤ planarPotentialKernel (q - center) -
      planarPotentialKernel (entrance u - center) - literalBoundaryError R) :
    AppendixDecoupling.ConditionStar
      (literalBoundaryHitError R rho lower)
      (centeredBoundaryStoppedHitKernel R center entrance) := by
  apply conditionStar_centeredBoundaryStoppedHitKernel_of_euclideanShells
    R rho center q entrance hR hq
  · intro u
    exact centeredInnerBoundary_shift_mem_boundaryInterior
      hseparated (hentrance u)
  · exact hrho
  · intro u
    have hu0 : entrance u - center ∈
        ThickPoint.discBoundary 0 ((rho : ℝ) + 1) :=
      (mem_discBoundary_translate center ((rho : ℝ) + 1) _).mp
        (hentrance u)
    exact (discBoundary_zero_euclideanRadius_bounds
      (rho := rho) hu0).1.le
  · intro u v
    have hu0 : entrance u - center ∈
        ThickPoint.discBoundary 0 ((rho : ℝ) + 1) :=
      (mem_discBoundary_translate center ((rho : ℝ) + 1) _).mp
        (hentrance u)
    have hv0 : entrance v - center ∈
        ThickPoint.discBoundary 0 ((rho : ℝ) + 1) :=
      (mem_discBoundary_translate center ((rho : ℝ) + 1) _).mp
        (hentrance v)
    have huBounds :=
      discBoundary_zero_euclideanRadius_bounds (rho := rho) hu0
    have hvBounds :=
      discBoundary_zero_euclideanRadius_bounds (rho := rho) hv0
    rw [abs_le]
    constructor <;> linarith
  · exact hlower
  · exact href

end

end Erdos1165.BoundaryStoppedHarnack
