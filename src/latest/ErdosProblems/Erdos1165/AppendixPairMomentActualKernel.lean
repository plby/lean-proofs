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
import ErdosProblems.Erdos1165.PoissonKernelMarkedHarnack
import ErdosProblems.Erdos1165.MarkedSkeletonPartitionUpper
import ErdosProblems.Erdos1165.TerminalParameterBounds

/-!
# Actual marked-kernel adapter for the pair moment

This module connects the event-defined terminal visit/exit kernel to the
finite-product upper comparison in `AppendixPairMoment`.  Both Harnack
inputs are concrete: the first-hit kernel is compared on the literal inner
shell, and the exit-mark kernel is compared pointwise on the literal outer
boundary.  Consequently the result can be multiplied by an arbitrary
complete complementary-skeleton weight.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace Erdos1165.AppendixPairMomentActualKernel

open AppendixLocalTime AppendixPairMoment BoundaryStoppedHarnack
open MarkedBoundaryVisitKernel PoissonKernelHarnack
open PoissonKernelMarkedAlgebra PoissonKernelMarkedHarnack
open PotentialEuclideanGeometry
open TerminalParameterBounds
open TerminalExcursionDisintegration SequentialAnnularKernel

noncomputable section

/-- Coordinatewise version of the exact marked-kernel comparison.  The
boundary, target, reference parameters, and errors may vary with the stopped
coordinate.  This is the form needed for a complete multiscale skeleton. -/
theorem terminalMarkedKernel_family_markedKernelUpper
    {Entrance Exit : Type*} {m : ℕ}
    (boundary : Fin m → Set Point) (target : Fin m → Point)
    (entrance : Fin m → Entrance → Point)
    (endpoint : Fin m → Exit → Point)
    (q p hitError exitError : Fin m → ℝ)
    (htarget : ∀ j, target j ∉ boundary j)
    (hp0 : ∀ j, 0 ≤ p j) (hp1 : ∀ j, p j ≤ 1)
    (hp : ∀ j, p j =
      BoundaryVisitRegeneration.escapeBeforePositiveReturnProbability
        (BoundaryVisitLaw.relativeBoundary (boundary j) (target j)))
    (hq0 : ∀ j, 0 ≤ q j) (hq1 : ∀ j, q j < 1)
    (hhitError0 : ∀ j, 0 ≤ hitError j)
    (hexitError0 : ∀ j, 0 ≤ exitError j)
    (hhitFactor0 : ∀ j, 0 ≤ 1 - hitError j)
    (hexitFactor0 : ∀ j, 0 ≤ 1 - exitError j)
    (hhitLower : ∀ j u,
      (1 - hitError j) * q j ≤
        boundaryStoppedHitKernel (boundary j) (target j) (entrance j u))
    (hhitUpper : ∀ j u,
      boundaryStoppedHitKernel (boundary j) (target j) (entrance j u) ≤
        (1 + hitError j) * q j)
    (hexitLower : ∀ j u z,
      (1 - exitError j) *
          (terminalSkeletonKernel (boundary j) (entrance j u)
            (endpoint j z)).toReal ≤
        (terminalSkeletonKernel (boundary j) (target j)
          (endpoint j z)).toReal)
    (hexitUpper : ∀ j u z,
      (terminalSkeletonKernel (boundary j) (target j)
          (endpoint j z)).toReal ≤
        (1 + exitError j) *
          (terminalSkeletonKernel (boundary j) (entrance j u)
            (endpoint j z)).toReal) :
    MarkedKernelUpper
      (fun j ↦ ENNReal.ofReal
        (markedPoissonUpperLoss (q j) (hitError j) (exitError j)))
      (fun j k ↦ ENNReal.ofReal (visitMass (q j) (p j) k))
      (fun j u z ↦ terminalSkeletonKernel
        (boundary j) (entrance j u) (endpoint j z))
      (fun j u k z ↦ terminalMarkedKernel
        (boundary j) (target j) (entrance j u) k (endpoint j z)) := by
  intro j u k z
  have hlocal := terminalMarkedKernel_markedKernelUpper 1
    (boundary j) (target j) (entrance j) (endpoint j)
    (q j) (p j) (hitError j) (exitError j)
    (htarget j) (hp0 j) (hp1 j) (hp j)
    (hq0 j) (hq1 j) (hhitError0 j) (hexitError0 j)
    (hhitFactor0 j) (hexitFactor0 j)
    (hhitLower j) (hhitUpper j) (hexitLower j) (hexitUpper j)
  have hcoordinate := hlocal (0 : Fin 1) u k z
  have hloss : 1 + markedPoissonUpperError
      (q j) (hitError j) (exitError j) =
      markedPoissonUpperLoss (q j) (hitError j) (exitError j) := by
    unfold markedPoissonUpperError markedPoissonUpperLoss
    rw [add_max]
    congr 1 <;> ring
  simpa only [hloss] using hcoordinate

/-- Fully geometric literal-disc specialization.  Each coordinate may use
its own outer radius, cut radius, entrance radius, reference entrance, and
potential lower bound.  The conclusion is the exact event-defined joint
visit-count/exit-point kernel comparison, ready for the complete stopped
skeleton upper disintegration. -/
theorem literalDiscTerminalMarkedKernel_family_markedKernelUpper
    {Entrance Exit : Type*} [Fintype Entrance] {m : ℕ}
    (R S r rho : Fin m → ℕ)
    (entrance : Fin m → Entrance → Point)
    (endpoint : Fin m → Exit → Point)
    (referenceEntrance : Fin m → Entrance)
    (boundaryReference : Fin m → Point)
    (lower : Fin m → ℝ)
    (hR : ∀ j, 5 ≤ R j)
    (hreferenceBoundary : ∀ j, boundaryReference j ∈
      ThickPoint.discBoundary 0 (R j : ℝ))
    (hinside : ∀ j u, entrance j u ∈ boundaryInterior (R j))
    (hrho : ∀ j, 4 ≤ rho j)
    (hradiusLower : ∀ j u,
      (rho j : ℝ) ≤ euclideanRadius (entrance j u))
    (hradiusGap : ∀ j u v,
      |euclideanRadius (entrance j u) -
        euclideanRadius (entrance j v)| ≤ 1)
    (hlower : ∀ j, 0 < lower j)
    (hpotentialLower : ∀ j u, lower j ≤
      PotentialConvergence.planarPotentialKernel (boundaryReference j) -
        PotentialConvergence.planarPotentialKernel (entrance j u) -
          literalBoundaryError (R j))
    (hS : ∀ j, r j + 2 ≤ S j)
    (hscale : ∀ j, S j + 2 * r j + 2 ≤ R j)
    (hcutOuter : ∀ j, S j + 4 ≤ R j)
    (hentranceRadiusUpper : ∀ j u,
      euclideanRadius (entrance j u) ≤ r j)
    (hendpointBoundary : ∀ j z, endpoint j z ∈
      ThickPoint.discBoundary 0 (R j : ℝ))
    (hgreenLower : ∀ j,
      0 < PoissonKernelGreenPole.greenPoleLower (R j) (S j) (r j))
    (hhitError1 : ∀ j,
      literalBoundaryHitError (R j) (rho j) (lower j) ≤ 1)
    (hexitError1 : ∀ j,
      poissonKernelRelativeError (R j) (S j) (r j) ≤ 1)
    (hq1 : ∀ j,
      literalBoundaryStoppedHitKernel (R j) (entrance j)
        (referenceEntrance j) < 1) :
    MarkedKernelUpper
      (fun j ↦ ENNReal.ofReal
        (markedPoissonUpperLoss
          (literalBoundaryStoppedHitKernel (R j) (entrance j)
            (referenceEntrance j))
          (literalBoundaryHitError (R j) (rho j) (lower j))
          (poissonKernelRelativeError (R j) (S j) (r j))))
      (fun j k ↦ ENNReal.ofReal
        (visitMass
          (literalBoundaryStoppedHitKernel (R j) (entrance j)
            (referenceEntrance j))
          (literalEscapeProbability (R j)) k))
      (fun j u z ↦ terminalSkeletonKernel
        (ThickPoint.discBoundary 0 (R j : ℝ)) (entrance j u) (endpoint j z))
      (fun j u k z ↦ terminalMarkedKernel
        (ThickPoint.discBoundary 0 (R j : ℝ)) 0
          (entrance j u) k (endpoint j z)) := by
  let q : Fin m → ℝ := fun j ↦
    literalBoundaryStoppedHitKernel (R j) (entrance j) (referenceEntrance j)
  let p : Fin m → ℝ := fun j ↦ literalEscapeProbability (R j)
  let hitError : Fin m → ℝ := fun j ↦
    literalBoundaryHitError (R j) (rho j) (lower j)
  let exitError : Fin m → ℝ := fun j ↦
    poissonKernelRelativeError (R j) (S j) (r j)
  have hstar (j : Fin m) : AppendixDecoupling.ConditionStar
      (hitError j) (literalBoundaryStoppedHitKernel (R j) (entrance j)) := by
    exact conditionStar_literalBoundaryStoppedHitKernel_of_euclideanShells
      (R j) (rho j) (boundaryReference j) (entrance j)
      (hR j) (hreferenceBoundary j) (hinside j) (hrho j)
      (hradiusLower j) (hradiusGap j) (hlower j) (hpotentialLower j)
  apply terminalMarkedKernel_family_markedKernelUpper
    (boundary := fun j ↦ ThickPoint.discBoundary 0 (R j : ℝ))
    (target := fun _ ↦ 0) (entrance := entrance) (endpoint := endpoint)
    (q := q) (p := p) (hitError := hitError) (exitError := exitError)
  · intro j
    intro hzero
    have hbounds := discBoundary_zero_euclideanRadius_bounds_nat
      (show 1 ≤ R j from le_trans (by norm_num) (hR j)) hzero
    have hzeroRadius : euclideanRadius (0 : Point) = 0 := by
      simp [euclideanRadius, euclideanRadiusSq]
    rw [hzeroRadius] at hbounds
    exact (by linarith : False)
  · intro j
    exact literalEscapeProbability_nonneg (R j)
  · intro j
    exact literalEscapeProbability_le_one (R j)
  · intro j
    dsimp only [p, literalEscapeProbability]
    congr 1
    ext z
    simp [BoundaryVisitLaw.relativeBoundary]
  · intro j
    exact measureReal_nonneg
  · intro j
    exact hq1 j
  · intro j
    unfold hitError literalBoundaryHitError
    exact div_nonneg
      (add_nonneg
        (mul_nonneg (by norm_num) (literalBoundaryError_nonneg (R j)))
        (RadialHarnackSpecialization.euclideanShellError_nonneg (rho j)))
      (hlower j).le
  · intro j
    have hscalej := hscale j
    exact poissonKernelRelativeError_nonneg (hS j)
      (show r j + 2 ≤ R j by omega) (hgreenLower j)
  · intro j
    exact sub_nonneg.mpr (hhitError1 j)
  · intro j
    exact sub_nonneg.mpr (hexitError1 j)
  · intro j u
    exact (hstar j (referenceEntrance j) u).1
  · intro j u
    exact (hstar j (referenceEntrance j) u).2
  · intro j u z
    have hcmp := exitMass_boundaryInterior_toReal_two_sided
      (R j) (S j) (r j) {endpoint j z}
      (by
        intro b hb
        rw [Finset.mem_singleton.mp hb]
        exact hendpointBoundary j z)
      (x := entrance j u) (y := 0)
      (hS j) (hscale j) (hcutOuter j)
      (hentranceRadiusUpper j u)
      (by norm_num [euclideanRadius, euclideanRadiusSq])
      (hgreenLower j) (hexitError1 j)
    rw [terminalSkeletonKernel_discBoundary_eq_exitMass
        (R j) (hinside j u) (hendpointBoundary j z),
      terminalSkeletonKernel_discBoundary_eq_exitMass
        (R j) (zero_mem_boundaryInterior (R := R j)
          (show 1 ≤ R j from le_trans (by norm_num) (hR j)))
        (hendpointBoundary j z)]
    exact hcmp.1
  · intro j u z
    have hcmp := exitMass_boundaryInterior_toReal_two_sided
      (R j) (S j) (r j) {endpoint j z}
      (by
        intro b hb
        rw [Finset.mem_singleton.mp hb]
        exact hendpointBoundary j z)
      (x := entrance j u) (y := 0)
      (hS j) (hscale j) (hcutOuter j)
      (hentranceRadiusUpper j u)
      (by norm_num [euclideanRadius, euclideanRadiusSq])
      (hgreenLower j) (hexitError1 j)
    rw [terminalSkeletonKernel_discBoundary_eq_exitMass
        (R j) (hinside j u) (hendpointBoundary j z),
      terminalSkeletonKernel_discBoundary_eq_exitMass
        (R j) (zero_mem_boundaryInterior (R := R j)
          (show 1 ≤ R j from le_trans (by norm_num) (hR j)))
        (hendpointBoundary j z)]
    exact hcmp.2

end

end Erdos1165.AppendixPairMomentActualKernel
