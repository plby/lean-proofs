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
import ErdosProblems.Erdos1165.PoissonKernelHarnack
import ErdosProblems.Erdos1165.PoissonKernelMarkedAlgebra
import ErdosProblems.Erdos1165.AppendixPairMoment
import ErdosProblems.Erdos1165.TerminalParameterBounds
import ErdosProblems.Erdos1165.TerminalSkeletonWords

/-!
# Sharp marked Poisson-kernel Harnack

This file combines the exact regenerative marked-visit identities with the
pointwise Poisson-kernel comparison.  The zero-visit atom is handled by its
exact additive decomposition, so the resulting inequality remains valid
after multiplication by arbitrary future stopped-data weights.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace Erdos1165.PoissonKernelMarkedHarnack

open AppendixLocalTime BoundaryVisitLaw BoundaryVisitRegeneration
open MarkedBoundaryVisitKernel
open PoissonKernelMarkedAlgebra TerminalExcursionDisintegration
open SequentialAnnularKernel TerminalSequentialVisitLaw
open TerminalExcursionPathwise TerminalParameterBounds TerminalSkeletonWords

noncomputable section

/-- The exact event-defined marked kernel is the abstract regenerated kernel
after taking finite real probability masses.  Both the positive geometric
factorization and the zero-visit subtraction are included. -/
theorem boundaryVisitExitKernel_toReal_eq_regenerated
    (boundary : Set Point) (target start exit : Point)
    (htarget : target ∉ boundary) {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hp : p = escapeBeforePositiveReturnProbability
      (relativeBoundary boundary target)) (k : ℕ) :
    (boundaryVisitExitKernel boundary target start k exit).toReal =
      regeneratedMarkedKernel
        (fun u z ↦ (skeletonExitKernel boundary u z).toReal)
        target
        (fun u ↦ boundaryStoppedHitKernel boundary target u)
        p start k exit := by
  cases k with
  | zero =>
      have hadd := skeletonExitMarkKernel_eq_killedPunctured_add_hit_mul
        boundary ({exit} : Set Point) target start htarget
      have hadd' : skeletonExitKernel boundary start exit =
          killedPuncturedExitMarkKernel boundary target start {exit} +
            fairSteps (boundaryHitSteps boundary target start) *
              skeletonExitKernel boundary target exit := by
        simpa only [skeletonExitKernel] using hadd
      have hreal := congrArg ENNReal.toReal hadd'
      have hkilled : killedPuncturedExitMarkKernel
          boundary target start {exit} ≠ ⊤ := measure_ne_top fairSteps _
      have hproduct : fairSteps (boundaryHitSteps boundary target start) *
          skeletonExitKernel boundary target exit ≠ ⊤ :=
        ENNReal.mul_ne_top (measure_ne_top fairSteps _)
          (measure_ne_top fairSteps _)
      rw [ENNReal.toReal_add hkilled hproduct,
        ENNReal.toReal_mul,
        fairSteps_boundaryHitSteps_toReal] at hreal
      rw [boundaryVisitExitKernel_zero, regeneratedMarkedKernel_zero]
      linarith
  | succ k =>
      rw [boundaryVisitExitKernel, regeneratedMarkedKernel_succ]
      rw [boundaryVisitExitMarkKernel_succ_eq_hit_mul_return_pow_mul_escape_mul_skeleton
        boundary target start {exit} htarget k]
      simp only [ENNReal.toReal_mul, ENNReal.toReal_pow,
        fairSteps_boundaryHitSteps_toReal]
      rw [← hp]
      rw [ENNReal.toReal_ofReal (sub_nonneg.mpr hp1),
        ENNReal.toReal_ofReal hp0]
      change _ * _ ^ k * _ *
          (skeletonExitKernel boundary target exit).toReal = _
      ring

/-- Translation invariance of the canonical marked exit endpoint event. -/
theorem boundaryExitEndpointSteps_centered_eq_zero
    (R : ℕ) (center start exit : Point) :
    boundaryExitEndpointSteps (ThickPoint.discBoundary center (R : ℝ))
        start exit =
      boundaryExitEndpointSteps (ThickPoint.discBoundary 0 (R : ℝ))
        (start - center) (exit - center) := by
  ext omega
  simp only [boundaryExitEndpointSteps, mem_iUnion, mem_setOf_eq]
  constructor
  · rintro ⟨N, ⟨hboundary, hbefore⟩, hend⟩
    refine ⟨N, ⟨?_, ?_⟩, ?_⟩
    · have htranslated :=
        (BoundaryStoppedHarnack.mem_discBoundary_translate
          center (R : ℝ) _).mp hboundary
      simpa only [BoundaryStoppedHarnack.trajectoryFrom_sub_center] using
        htranslated
    · intro k hk hkBoundary
      apply hbefore k hk
      apply (BoundaryStoppedHarnack.mem_discBoundary_translate
        center (R : ℝ) _).mpr
      simpa only [BoundaryStoppedHarnack.trajectoryFrom_sub_center] using
        hkBoundary
    · simpa only [← BoundaryStoppedHarnack.trajectoryFrom_sub_center,
        hend]
  · rintro ⟨N, ⟨hboundary, hbefore⟩, hend⟩
    refine ⟨N, ⟨?_, ?_⟩, ?_⟩
    · apply (BoundaryStoppedHarnack.mem_discBoundary_translate
        center (R : ℝ) _).mpr
      simpa only [BoundaryStoppedHarnack.trajectoryFrom_sub_center] using
        hboundary
    · intro k hk hkBoundary
      apply hbefore k hk
      have htranslated :=
        (BoundaryStoppedHarnack.mem_discBoundary_translate
          center (R : ℝ) _).mp hkBoundary
      simpa only [BoundaryStoppedHarnack.trajectoryFrom_sub_center] using
        htranslated
    · apply sub_left_injective
      simpa only [BoundaryStoppedHarnack.trajectoryFrom_sub_center] using hend

/-- Translation invariance of the canonical terminal skeleton kernel. -/
theorem terminalSkeletonKernel_centered_eq_zero
    (R : ℕ) (center start exit : Point) :
    terminalSkeletonKernel (ThickPoint.discBoundary center (R : ℝ))
        start exit =
      terminalSkeletonKernel (ThickPoint.discBoundary 0 (R : ℝ))
        (start - center) (exit - center) := by
  unfold terminalSkeletonKernel
  rw [boundaryExitEndpointSteps_centered_eq_zero]

/-- Pointwise `1 plus-or-minus error` Poisson-kernel comparison on the exact supported
HLOZ terminal entrance and exit types.  This theorem is the literal-boundary
bridge used by the terminal stopped-data disintegration. -/
theorem terminalSkeletonKernel_terminalBoundary_toReal_two_sided
    (n S : ℕ) (center : Point)
    (hn : 1 ≤ n)
    (hS : n ^ 6 + 2 ≤ S)
    (hscale : S + 2 * n ^ 6 + 2 ≤ n ^ 9)
    (hcutOuter : S + 4 ≤ n ^ 9)
    (hlower : 0 < PoissonKernelGreenPole.greenPoleLower
      (n ^ 9) S (n ^ 6))
    (herror1 : PoissonKernelHarnack.poissonKernelRelativeError
      (n ^ 9) S (n ^ 6) ≤ 1)
    (u : TerminalEntrance n center) (z : TerminalExit n center) :
    (1 - PoissonKernelHarnack.poissonKernelRelativeError
          (n ^ 9) S (n ^ 6)) *
        (terminalSkeletonKernel (terminalOuterBoundary n center)
          u.1 z.1).toReal ≤
      (terminalSkeletonKernel (terminalOuterBoundary n center)
        center z.1).toReal ∧
    (terminalSkeletonKernel (terminalOuterBoundary n center)
        center z.1).toReal ≤
      (1 + PoissonKernelHarnack.poissonKernelRelativeError
          (n ^ 9) S (n ^ 6)) *
        (terminalSkeletonKernel (terminalOuterBoundary n center)
          u.1 z.1).toReal := by
  let R := n ^ 9
  let r := n ^ 6
  have hR : r + 2 ≤ R := by
    calc
      r + 2 ≤ S + 2 * r + 2 := by omega
      _ ≤ R := hscale
  have huBoundary : u.1 - center ∈
      ThickPoint.discBoundary 0 (r : ℝ) := by
    apply (BoundaryStoppedHarnack.mem_discBoundary_translate
      center (r : ℝ) u.1).mp
    simpa [r, terminalInnerBoundary, ThickPoint.scaleRadius_succ_self] using
      u.2
  have hzBoundary : z.1 - center ∈
      ThickPoint.discBoundary 0 (R : ℝ) := by
    apply (BoundaryStoppedHarnack.mem_discBoundary_translate
      center (R : ℝ) z.1).mp
    simpa [R, terminalOuterBoundary, ThickPoint.scaleRadius_of_le,
      ThickPoint.regularRadius_self] using z.2
  have huRadius :
      PotentialEuclideanGeometry.euclideanRadius (u.1 - center) ≤ r :=
    (BoundaryStoppedHarnack.discBoundary_zero_euclideanRadius_bounds_nat
      (show 1 ≤ r by
        dsimp only [r]
        have hnpos : 0 < n := by omega
        have hpow : 0 < n ^ 6 := pow_pos hnpos 6
        omega) huBoundary).2
  have hcenterRadius :
      PotentialEuclideanGeometry.euclideanRadius (center - center) ≤ r := by
    simp [PotentialEuclideanGeometry.euclideanRadius,
      PotentialEuclideanGeometry.euclideanRadiusSq]
  have huD := PoissonKernelHarnack.mem_boundaryInterior_of_euclideanRadius_le
    hR huRadius
  have hcenterD :=
    PoissonKernelHarnack.mem_boundaryInterior_of_euclideanRadius_le
      hR hcenterRadius
  have hcompare :=
    PoissonKernelHarnack.exitMass_boundaryInterior_toReal_two_sided
      R S r ({z.1 - center} : Finset Point)
      (by
        intro b hb
        rw [Finset.mem_singleton] at hb
        simpa [hb] using hzBoundary)
      hS hscale hcutOuter huRadius hcenterRadius hlower herror1
  have huKernel :
      terminalSkeletonKernel (terminalOuterBoundary n center) u.1 z.1 =
        AnnulusHarnack.exitMass (BoundaryStoppedHarnack.boundaryInterior R)
          {z.1 - center} (u.1 - center) := by
    have houter : terminalOuterBoundary n center =
        ThickPoint.discBoundary center (R : ℝ) := by
      simp [R, terminalOuterBoundary, ThickPoint.scaleRadius_of_le,
        ThickPoint.regularRadius_self]
    calc
      terminalSkeletonKernel (terminalOuterBoundary n center) u.1 z.1 =
          terminalSkeletonKernel (ThickPoint.discBoundary center (R : ℝ))
            u.1 z.1 := congrArg
              (fun boundary : Set Point ↦ terminalSkeletonKernel boundary u.1 z.1)
              houter
      _ = terminalSkeletonKernel (ThickPoint.discBoundary 0 (R : ℝ))
          (u.1 - center) (z.1 - center) :=
        terminalSkeletonKernel_centered_eq_zero R center u.1 z.1
      _ = AnnulusHarnack.exitMass
          (BoundaryStoppedHarnack.boundaryInterior R)
          {z.1 - center} (u.1 - center) :=
        terminalSkeletonKernel_discBoundary_eq_exitMass R huD hzBoundary
  have hcenterKernel :
      terminalSkeletonKernel (terminalOuterBoundary n center) center z.1 =
        AnnulusHarnack.exitMass (BoundaryStoppedHarnack.boundaryInterior R)
          {z.1 - center} (center - center) := by
    have houter : terminalOuterBoundary n center =
        ThickPoint.discBoundary center (R : ℝ) := by
      simp [R, terminalOuterBoundary, ThickPoint.scaleRadius_of_le,
        ThickPoint.regularRadius_self]
    calc
      terminalSkeletonKernel (terminalOuterBoundary n center) center z.1 =
          terminalSkeletonKernel (ThickPoint.discBoundary center (R : ℝ))
            center z.1 := congrArg
              (fun boundary : Set Point ↦
                terminalSkeletonKernel boundary center z.1) houter
      _ = terminalSkeletonKernel (ThickPoint.discBoundary 0 (R : ℝ))
          (center - center) (z.1 - center) :=
        terminalSkeletonKernel_centered_eq_zero R center center z.1
      _ = AnnulusHarnack.exitMass
          (BoundaryStoppedHarnack.boundaryInterior R)
          {z.1 - center} (center - center) :=
        terminalSkeletonKernel_discBoundary_eq_exitMass
          R hcenterD hzBoundary
  rw [huKernel, hcenterKernel]
  simpa [R, r] using hcompare

/-- The common relative error for all visit-count atoms.  The first entry of
the maximum is the product error for positive counts.  The second is the
odds-amplified error forced by subtracting the paths which hit the target in
the zero-count atom. -/
def markedPoissonLowerError (q hitError exitError : ℝ) : ℝ :=
  max (hitError + exitError - hitError * exitError)
    ((hitError + exitError + hitError * exitError) * q / (1 - q))

/-- Exact all-count lower comparison for the canonical event-defined marked
kernel.  This is already in the `MarkedKernelLower` form consumed by the
arbitrary stopped-skeleton disintegration. -/
theorem terminalMarkedKernel_markedKernelLower
    {Entrance Exit : Type*} (m : ℕ)
    (boundary : Set Point) (target : Point)
    (entrance : Entrance → Point) (endpoint : Exit → Point)
    (q p hitError exitError : ℝ)
    (htarget : target ∉ boundary)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hp : p = escapeBeforePositiveReturnProbability
      (relativeBoundary boundary target))
    (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hhitError0 : 0 ≤ hitError) (hexitError0 : 0 ≤ exitError)
    (hhitFactor0 : 0 ≤ 1 - hitError)
    (hexitFactor0 : 0 ≤ 1 - exitError)
    (hloss1 : markedPoissonLowerError q hitError exitError ≤ 1)
    (hhitLower : ∀ u,
      (1 - hitError) * q ≤
        boundaryStoppedHitKernel boundary target (entrance u))
    (hhitUpper : ∀ u,
      boundaryStoppedHitKernel boundary target (entrance u) ≤
        (1 + hitError) * q)
    (hexitLower : ∀ u z,
      (1 - exitError) *
          (terminalSkeletonKernel boundary (entrance u) (endpoint z)).toReal ≤
        (terminalSkeletonKernel boundary target (endpoint z)).toReal)
    (hexitUpper : ∀ u z,
      (terminalSkeletonKernel boundary target (endpoint z)).toReal ≤
        (1 + exitError) *
          (terminalSkeletonKernel boundary (entrance u) (endpoint z)).toReal) :
    MarkedTerminalDisintegration.MarkedKernelLower
      (fun _ : Fin m ↦ ENNReal.ofReal
        (1 - markedPoissonLowerError q hitError exitError))
      (fun _ k ↦ ENNReal.ofReal (visitMass q p k))
      (fun _ u z ↦ terminalSkeletonKernel boundary (entrance u) (endpoint z))
      (fun _ u k z ↦
        terminalMarkedKernel boundary target (entrance u) k (endpoint z)) := by
  intro _j u k z
  let outer : Point → Point → ℝ :=
    fun a b ↦ (skeletonExitKernel boundary a b).toReal
  let hit : Point → ℝ :=
    fun a ↦ boundaryStoppedHitKernel boundary target a
  let loss := markedPoissonLowerError q hitError exitError
  have hloss0 : 0 ≤ 1 - loss := sub_nonneg.mpr hloss1
  have hvisit0 (n : ℕ) : 0 ≤ visitMass q p n :=
    visitMass_nonneg hq0 (le_of_lt hq1) hp0 hp1 n
  have houter0 : 0 ≤ outer (entrance u) (endpoint z) :=
    ENNReal.toReal_nonneg
  have hcenter0 : 0 ≤ outer target (endpoint z) :=
    ENNReal.toReal_nonneg
  have hhitLower' : (1 - hitError) * q ≤ hit (entrance u) :=
    hhitLower u
  have hhitUpper' : hit (entrance u) ≤ (1 + hitError) * q :=
    hhitUpper u
  have hexitLower' :
      (1 - exitError) * outer (entrance u) (endpoint z) ≤
        outer target (endpoint z) := by
    simpa only [outer, terminalSkeletonKernel_eq_skeletonExitKernel] using
      hexitLower u z
  have hexitUpper' : outer target (endpoint z) ≤
      (1 + exitError) * outer (entrance u) (endpoint z) := by
    simpa only [outer, terminalSkeletonKernel_eq_skeletonExitKernel] using
      hexitUpper u z
  have hhit0 : 0 ≤ hit (entrance u) :=
    (mul_nonneg hhitFactor0 hq0).trans hhitLower'
  have hmarkedFinite : terminalMarkedKernel boundary target (entrance u) k
      (endpoint z) ≠ ⊤ := measure_ne_top fairSteps _
  have hskeletonFinite : terminalSkeletonKernel boundary (entrance u)
      (endpoint z) ≠ ⊤ := measure_ne_top fairSteps _
  have hregen :
      ENNReal.ofReal (regeneratedMarkedKernel outer target hit p
          (entrance u) k (endpoint z)) =
        terminalMarkedKernel boundary target (entrance u) k (endpoint z) := by
    calc
      ENNReal.ofReal (regeneratedMarkedKernel outer target hit p
          (entrance u) k (endpoint z)) =
          ENNReal.ofReal
            (boundaryVisitExitKernel boundary target (entrance u) k
              (endpoint z)).toReal := by
            congr 1
            exact (boundaryVisitExitKernel_toReal_eq_regenerated
              boundary target (entrance u) (endpoint z) htarget
              hp0 hp1 hp k).symm
      _ = boundaryVisitExitKernel boundary target (entrance u) k
          (endpoint z) := ENNReal.ofReal_toReal (measure_ne_top fairSteps _)
      _ = terminalMarkedKernel boundary target (entrance u) k
          (endpoint z) :=
        (terminalMarkedKernel_eq_boundaryVisitExitKernel
          boundary target (entrance u) (endpoint z) htarget k).symm
  have hskeletonOfReal : ENNReal.ofReal (outer (entrance u) (endpoint z)) =
      terminalSkeletonKernel boundary (entrance u) (endpoint z) := by
    dsimp only [outer]
    rw [← terminalSkeletonKernel_eq_skeletonExitKernel]
    exact ENNReal.ofReal_toReal hskeletonFinite
  change ENNReal.ofReal (1 - loss) * ENNReal.ofReal (visitMass q p k) *
      terminalSkeletonKernel boundary (entrance u) (endpoint z) ≤
    terminalMarkedKernel boundary target (entrance u) k (endpoint z)
  cases k with
  | zero =>
      have hzero := regeneratedMarkedKernel_zero_lower
        (outer := outer) (center := target) (u := entrance u)
        (w := endpoint z) (hit := hit) (escape := p) (q := q)
        (hitError := hitError) (exitError := exitError)
        houter0 hhit0 hcenter0 hhitUpper' hexitUpper'
        (mul_nonneg (by linarith) hq0) (by linarith) hq1
      have hlossZero :
          1 - loss ≤
            1 - (hitError + exitError + hitError * exitError) * q / (1 - q) := by
        unfold loss markedPoissonLowerError
        linarith [le_max_right
          (hitError + exitError - hitError * exitError)
          ((hitError + exitError + hitError * exitError) * q / (1 - q))]
      have hreal :
          (1 - loss) * visitMass q p 0 * outer (entrance u) (endpoint z) ≤
            regeneratedMarkedKernel outer target hit p
              (entrance u) 0 (endpoint z) := by
        apply le_trans _ hzero
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hlossZero (hvisit0 0)) houter0
      have hof := ENNReal.ofReal_le_ofReal hreal
      rw [← hregen, ← hskeletonOfReal]
      simpa only [ENNReal.ofReal_mul hloss0,
        ENNReal.ofReal_mul (mul_nonneg hloss0 (hvisit0 0))] using hof
  | succ k =>
      have hpositive := regeneratedMarkedKernel_succ_compare
        (outer := outer) (center := target) (u := entrance u)
        (w := endpoint z) (hit := hit) (escape := p) (q := q)
        (hitError := hitError) (exitError := exitError)
        hq0 hp0 hp1 houter0 hhitLower' hhitUpper'
        hexitLower' hexitUpper' hhitError0 hexitError0
        hhitFactor0 hexitFactor0 k
      have hlossPositive :
          1 - loss ≤ (1 - hitError) * (1 - exitError) := by
        unfold loss markedPoissonLowerError
        have hmax := le_max_left
          (hitError + exitError - hitError * exitError)
          ((hitError + exitError + hitError * exitError) * q / (1 - q))
        nlinarith
      have hreal :
          (1 - loss) * visitMass q p (k + 1) *
              outer (entrance u) (endpoint z) ≤
            regeneratedMarkedKernel outer target hit p
              (entrance u) (k + 1) (endpoint z) := by
        apply le_trans _ hpositive.1
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hlossPositive (hvisit0 (k + 1))) houter0
      have hof := ENNReal.ofReal_le_ofReal hreal
      rw [← hregen, ← hskeletonOfReal]
      simpa only [ENNReal.ofReal_mul hloss0,
        ENNReal.ofReal_mul (mul_nonneg hloss0 (hvisit0 (k + 1)))] using hof

/-- Common relative upper error for all count atoms. -/
def markedPoissonUpperError (q hitError exitError : ℝ) : ℝ :=
  max (hitError + exitError + hitError * exitError)
    ((hitError + exitError - hitError * exitError) * q / (1 - q))

/-- Exact all-count upper comparison for the same canonical marked kernels.
Together with `terminalMarkedKernel_markedKernelLower`, this is the checked
joint marked bridge comparison used by the one-point and pair adapters. -/
theorem terminalMarkedKernel_markedKernelUpper
    {Entrance Exit : Type*} (m : ℕ)
    (boundary : Set Point) (target : Point)
    (entrance : Entrance → Point) (endpoint : Exit → Point)
    (q p hitError exitError : ℝ)
    (htarget : target ∉ boundary)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hp : p = escapeBeforePositiveReturnProbability
      (relativeBoundary boundary target))
    (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hhitError0 : 0 ≤ hitError) (hexitError0 : 0 ≤ exitError)
    (hhitFactor0 : 0 ≤ 1 - hitError)
    (hexitFactor0 : 0 ≤ 1 - exitError)
    (hhitLower : ∀ u,
      (1 - hitError) * q ≤
        boundaryStoppedHitKernel boundary target (entrance u))
    (hhitUpper : ∀ u,
      boundaryStoppedHitKernel boundary target (entrance u) ≤
        (1 + hitError) * q)
    (hexitLower : ∀ u z,
      (1 - exitError) *
          (terminalSkeletonKernel boundary (entrance u) (endpoint z)).toReal ≤
        (terminalSkeletonKernel boundary target (endpoint z)).toReal)
    (hexitUpper : ∀ u z,
      (terminalSkeletonKernel boundary target (endpoint z)).toReal ≤
        (1 + exitError) *
          (terminalSkeletonKernel boundary (entrance u) (endpoint z)).toReal) :
    AppendixPairMoment.MarkedKernelUpper
      (fun _ : Fin m ↦ ENNReal.ofReal
        (1 + markedPoissonUpperError q hitError exitError))
      (fun _ k ↦ ENNReal.ofReal (visitMass q p k))
      (fun _ u z ↦ terminalSkeletonKernel boundary (entrance u) (endpoint z))
      (fun _ u k z ↦
        terminalMarkedKernel boundary target (entrance u) k (endpoint z)) := by
  intro _j u k z
  let outer : Point → Point → ℝ :=
    fun a b ↦ (skeletonExitKernel boundary a b).toReal
  let hit : Point → ℝ :=
    fun a ↦ boundaryStoppedHitKernel boundary target a
  let loss := markedPoissonUpperError q hitError exitError
  have hpositiveError0 :
      0 ≤ hitError + exitError + hitError * exitError := by positivity
  have hloss0 : 0 ≤ loss :=
    hpositiveError0.trans (le_max_left _ _)
  have honeLoss0 : 0 ≤ 1 + loss := by linarith
  have hvisit0 (n : ℕ) : 0 ≤ visitMass q p n :=
    visitMass_nonneg hq0 (le_of_lt hq1) hp0 hp1 n
  have houter0 : 0 ≤ outer (entrance u) (endpoint z) :=
    ENNReal.toReal_nonneg
  have hcenter0 : 0 ≤ outer target (endpoint z) :=
    ENNReal.toReal_nonneg
  have hhitLower' : (1 - hitError) * q ≤ hit (entrance u) :=
    hhitLower u
  have hhitUpper' : hit (entrance u) ≤ (1 + hitError) * q :=
    hhitUpper u
  have hexitLower' :
      (1 - exitError) * outer (entrance u) (endpoint z) ≤
        outer target (endpoint z) := by
    simpa only [outer, terminalSkeletonKernel_eq_skeletonExitKernel] using
      hexitLower u z
  have hexitUpper' : outer target (endpoint z) ≤
      (1 + exitError) * outer (entrance u) (endpoint z) := by
    simpa only [outer, terminalSkeletonKernel_eq_skeletonExitKernel] using
      hexitUpper u z
  have hskeletonFinite : terminalSkeletonKernel boundary (entrance u)
      (endpoint z) ≠ ⊤ := measure_ne_top fairSteps _
  have hskeletonOfReal : ENNReal.ofReal (outer (entrance u) (endpoint z)) =
      terminalSkeletonKernel boundary (entrance u) (endpoint z) := by
    dsimp only [outer]
    rw [← terminalSkeletonKernel_eq_skeletonExitKernel]
    exact ENNReal.ofReal_toReal hskeletonFinite
  have hregen :
      ENNReal.ofReal (regeneratedMarkedKernel outer target hit p
          (entrance u) k (endpoint z)) =
        terminalMarkedKernel boundary target (entrance u) k (endpoint z) := by
    calc
      ENNReal.ofReal (regeneratedMarkedKernel outer target hit p
          (entrance u) k (endpoint z)) =
          ENNReal.ofReal
            (boundaryVisitExitKernel boundary target (entrance u) k
              (endpoint z)).toReal := by
            congr 1
            exact (boundaryVisitExitKernel_toReal_eq_regenerated
              boundary target (entrance u) (endpoint z) htarget
              hp0 hp1 hp k).symm
      _ = boundaryVisitExitKernel boundary target (entrance u) k
          (endpoint z) := ENNReal.ofReal_toReal (measure_ne_top fairSteps _)
      _ = terminalMarkedKernel boundary target (entrance u) k
          (endpoint z) :=
        (terminalMarkedKernel_eq_boundaryVisitExitKernel
          boundary target (entrance u) (endpoint z) htarget k).symm
  change terminalMarkedKernel boundary target (entrance u) k (endpoint z) ≤
    ENNReal.ofReal (1 + loss) * ENNReal.ofReal (visitMass q p k) *
      terminalSkeletonKernel boundary (entrance u) (endpoint z)
  cases k with
  | zero =>
      have hzero := regeneratedMarkedKernel_zero_upper
        (outer := outer) (center := target) (u := entrance u)
        (w := endpoint z) (hit := hit) (escape := p) (q := q)
        (hitError := hitError) (exitError := exitError)
        houter0 hcenter0 hhitLower' hexitLower'
        (mul_nonneg hhitFactor0 hq0) hexitFactor0 hq1
      have hfactor :
          1 + (hitError + exitError - hitError * exitError) * q / (1 - q)
            ≤ 1 + loss := by
        unfold loss markedPoissonUpperError
        linarith [le_max_right
          (hitError + exitError + hitError * exitError)
          ((hitError + exitError - hitError * exitError) * q / (1 - q))]
      have hreal : regeneratedMarkedKernel outer target hit p
              (entrance u) 0 (endpoint z) ≤
          (1 + loss) * visitMass q p 0 * outer (entrance u) (endpoint z) := by
        apply le_trans hzero
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hfactor (hvisit0 0)) houter0
      have hof := ENNReal.ofReal_le_ofReal hreal
      rw [← hregen, ← hskeletonOfReal]
      simpa only [ENNReal.ofReal_mul honeLoss0,
        ENNReal.ofReal_mul (mul_nonneg honeLoss0 (hvisit0 0))] using hof
  | succ k =>
      have hpositive := regeneratedMarkedKernel_succ_compare
        (outer := outer) (center := target) (u := entrance u)
        (w := endpoint z) (hit := hit) (escape := p) (q := q)
        (hitError := hitError) (exitError := exitError)
        hq0 hp0 hp1 houter0 hhitLower' hhitUpper'
        hexitLower' hexitUpper' hhitError0 hexitError0
        hhitFactor0 hexitFactor0 k
      have hfactor :
          (1 + hitError) * (1 + exitError) ≤ 1 + loss := by
        unfold loss markedPoissonUpperError
        have hmax := le_max_left
          (hitError + exitError + hitError * exitError)
          ((hitError + exitError - hitError * exitError) * q / (1 - q))
        nlinarith
      have hreal : regeneratedMarkedKernel outer target hit p
              (entrance u) (k + 1) (endpoint z) ≤
          (1 + loss) * visitMass q p (k + 1) *
            outer (entrance u) (endpoint z) := by
        apply le_trans hpositive.2
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hfactor (hvisit0 (k + 1))) houter0
      have hof := ENNReal.ofReal_le_ofReal hreal
      rw [← hregen, ← hskeletonOfReal]
      simpa only [ENNReal.ofReal_mul honeLoss0,
        ENNReal.ofReal_mul (mul_nonneg honeLoss0 (hvisit0 (k + 1)))] using hof

/-! ## Exact HLOZ terminal boundary specialization -/

/-- The Poisson-kernel error at the exact terminal radii `n^6` and `n^9`. -/
def terminalPoissonExitError (n S : ℕ) : ℝ :=
  PoissonKernelHarnack.poissonKernelRelativeError (n ^ 9) S (n ^ 6)

/-- The common all-count lower error after combining terminal hit and
endpoint Poisson comparisons. -/
def terminalMarkedPoissonLowerError (n S : ℕ) (hitError : ℝ) : ℝ :=
  markedPoissonLowerError (terminalHitProbability n) hitError
    (terminalPoissonExitError n S)

theorem relativeBoundary_terminalOuterBoundary
    (n : ℕ) (center : Point) :
    relativeBoundary (terminalOuterBoundary n center) center =
      ThickPoint.discBoundary 0 ((n ^ 9 : ℕ) : ℝ) := by
  ext z
  change center + z ∈ terminalOuterBoundary n center ↔ _
  rw [show terminalOuterBoundary n center =
      ThickPoint.discBoundary center ((n ^ 9 : ℕ) : ℝ) by
    simp [terminalOuterBoundary, ThickPoint.scaleRadius_of_le,
      ThickPoint.regularRadius_self]]
  rw [BoundaryStoppedHarnack.mem_discBoundary_translate]
  simp

theorem terminalEscapeProbability_eq_relativeBoundary
    (n : ℕ) (center : Point) :
    terminalEscapeProbability n =
      escapeBeforePositiveReturnProbability
        (relativeBoundary (terminalOuterBoundary n center) center) := by
  rw [relativeBoundary_terminalOuterBoundary]
  rfl

theorem center_not_mem_terminalOuterBoundary
    (n : ℕ) (center : Point) (hn : 2 ≤ n) :
    center ∉ terminalOuterBoundary n center := by
  intro hcenter
  have hzero : (0 : Point) ∈
      ThickPoint.discBoundary 0 ((n ^ 9 : ℕ) : ℝ) := by
    simpa only [sub_self] using
      (BoundaryStoppedHarnack.mem_discBoundary_translate
        center ((n ^ 9 : ℕ) : ℝ) center).mp
        (by simpa [terminalOuterBoundary, ThickPoint.scaleRadius_of_le,
          ThickPoint.regularRadius_self] using hcenter)
  have hlower :=
    (BoundaryStoppedHarnack.discBoundary_zero_euclideanRadius_bounds_nat
      (Nat.one_le_pow 9 n (by omega)) hzero).1
  have hradius : PotentialEuclideanGeometry.euclideanRadius (0 : Point) = 0 := by
    simp [PotentialEuclideanGeometry.euclideanRadius,
      PotentialEuclideanGeometry.euclideanRadiusSq]
  rw [hradius] at hlower
  have hnonneg : (0 : ℝ) ≤ (n ^ 9 - 1 : ℕ) := by positivity
  linarith

/-- Exact supported all-count marked-kernel lower bound at HLOZ's terminal
radii.  The endpoint comparison is fully discharged; the two displayed hit
bounds are precisely the remaining input from the stopped hit Harnack. -/
theorem terminalMarkedKernel_terminalBoundary_markedKernelLower
    (m n S : ℕ) (center : Point) (hitError : ℝ)
    (hn : 2 ≤ n)
    (hS : n ^ 6 + 2 ≤ S)
    (hscale : S + 2 * n ^ 6 + 2 ≤ n ^ 9)
    (hcutOuter : S + 4 ≤ n ^ 9)
    (hlower : 0 < PoissonKernelGreenPole.greenPoleLower
      (n ^ 9) S (n ^ 6))
    (hexitError1 : terminalPoissonExitError n S ≤ 1)
    (hq1 : terminalHitProbability n < 1)
    (hhitError0 : 0 ≤ hitError)
    (hhitFactor0 : 0 ≤ 1 - hitError)
    (hloss1 : terminalMarkedPoissonLowerError n S hitError ≤ 1)
    (hhitLower : ∀ u : TerminalEntrance n center,
      (1 - hitError) * terminalHitProbability n ≤
        boundaryStoppedHitKernel
          (terminalOuterBoundary n center) center u.1)
    (hhitUpper : ∀ u : TerminalEntrance n center,
      boundaryStoppedHitKernel
          (terminalOuterBoundary n center) center u.1 ≤
        (1 + hitError) * terminalHitProbability n) :
    MarkedTerminalDisintegration.MarkedKernelLower
      (fun _ : Fin m ↦ ENNReal.ofReal
        (1 - terminalMarkedPoissonLowerError n S hitError))
      (fun _ k ↦ ENNReal.ofReal
        (visitMass (terminalHitProbability n)
          (terminalEscapeProbability n) k))
      (fun _ (u : TerminalEntrance n center) (z : TerminalExit n center) ↦
        terminalSkeletonKernel (terminalOuterBoundary n center) u.1 z.1)
      (fun _ (u : TerminalEntrance n center) k (z : TerminalExit n center) ↦
        terminalMarkedKernel (terminalOuterBoundary n center) center u.1 k z.1) := by
  apply terminalMarkedKernel_markedKernelLower
    (boundary := terminalOuterBoundary n center) (target := center)
    (entrance := fun u : TerminalEntrance n center ↦ u.1)
    (endpoint := fun z : TerminalExit n center ↦ z.1)
    (q := terminalHitProbability n) (p := terminalEscapeProbability n)
    (hitError := hitError) (exitError := terminalPoissonExitError n S)
  · exact center_not_mem_terminalOuterBoundary n center hn
  · exact (terminalEscapeProbability_pos n hn).le
  · exact terminalEscapeProbability_le_one n
  · exact terminalEscapeProbability_eq_relativeBoundary n center
  · exact terminalHitProbability_nonneg n
  · exact hq1
  · exact hhitError0
  · exact PoissonKernelHarnack.poissonKernelRelativeError_nonneg
      hS (by omega) hlower
  · exact hhitFactor0
  · exact sub_nonneg.mpr hexitError1
  · exact hloss1
  · exact hhitLower
  · exact hhitUpper
  · intro u z
    exact (terminalSkeletonKernel_terminalBoundary_toReal_two_sided
      n S center (by omega) hS hscale hcutOuter hlower hexitError1 u z).1
  · intro u z
    exact (terminalSkeletonKernel_terminalBoundary_toReal_two_sided
      n S center (by omega) hS hscale hcutOuter hlower hexitError1 u z).2

/-- The common all-count upper error at the exact terminal radii. -/
def terminalMarkedPoissonUpperError (n S : ℕ) (hitError : ℝ) : ℝ :=
  markedPoissonUpperError (terminalHitProbability n) hitError
    (terminalPoissonExitError n S)

/-- Exact supported all-count marked-kernel upper bound at HLOZ's terminal
radii, paired with `terminalMarkedKernel_terminalBoundary_markedKernelLower`.
-/
theorem terminalMarkedKernel_terminalBoundary_markedKernelUpper
    (m n S : ℕ) (center : Point) (hitError : ℝ)
    (hn : 2 ≤ n)
    (hS : n ^ 6 + 2 ≤ S)
    (hscale : S + 2 * n ^ 6 + 2 ≤ n ^ 9)
    (hcutOuter : S + 4 ≤ n ^ 9)
    (hlower : 0 < PoissonKernelGreenPole.greenPoleLower
      (n ^ 9) S (n ^ 6))
    (hexitError1 : terminalPoissonExitError n S ≤ 1)
    (hq1 : terminalHitProbability n < 1)
    (hhitError0 : 0 ≤ hitError)
    (hhitFactor0 : 0 ≤ 1 - hitError)
    (hhitLower : ∀ u : TerminalEntrance n center,
      (1 - hitError) * terminalHitProbability n ≤
        boundaryStoppedHitKernel
          (terminalOuterBoundary n center) center u.1)
    (hhitUpper : ∀ u : TerminalEntrance n center,
      boundaryStoppedHitKernel
          (terminalOuterBoundary n center) center u.1 ≤
        (1 + hitError) * terminalHitProbability n) :
    AppendixPairMoment.MarkedKernelUpper
      (fun _ : Fin m ↦ ENNReal.ofReal
        (1 + terminalMarkedPoissonUpperError n S hitError))
      (fun _ k ↦ ENNReal.ofReal
        (visitMass (terminalHitProbability n)
          (terminalEscapeProbability n) k))
      (fun _ (u : TerminalEntrance n center) (z : TerminalExit n center) ↦
        terminalSkeletonKernel (terminalOuterBoundary n center) u.1 z.1)
      (fun _ (u : TerminalEntrance n center) k (z : TerminalExit n center) ↦
        terminalMarkedKernel (terminalOuterBoundary n center) center u.1 k z.1) := by
  apply terminalMarkedKernel_markedKernelUpper
    (boundary := terminalOuterBoundary n center) (target := center)
    (entrance := fun u : TerminalEntrance n center ↦ u.1)
    (endpoint := fun z : TerminalExit n center ↦ z.1)
    (q := terminalHitProbability n) (p := terminalEscapeProbability n)
    (hitError := hitError) (exitError := terminalPoissonExitError n S)
  · exact center_not_mem_terminalOuterBoundary n center hn
  · exact (terminalEscapeProbability_pos n hn).le
  · exact terminalEscapeProbability_le_one n
  · exact terminalEscapeProbability_eq_relativeBoundary n center
  · exact terminalHitProbability_nonneg n
  · exact hq1
  · exact hhitError0
  · exact PoissonKernelHarnack.poissonKernelRelativeError_nonneg
      hS (by omega) hlower
  · exact hhitFactor0
  · exact sub_nonneg.mpr hexitError1
  · exact hhitLower
  · exact hhitUpper
  · intro u z
    exact (terminalSkeletonKernel_terminalBoundary_toReal_two_sided
      n S center (by omega) hS hscale hcutOuter hlower hexitError1 u z).1
  · intro u z
    exact (terminalSkeletonKernel_terminalBoundary_toReal_two_sided
      n S center (by omega) hS hscale hcutOuter hlower hexitError1 u z).2

end

end Erdos1165.PoissonKernelMarkedHarnack
