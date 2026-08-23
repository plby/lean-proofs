/- leanprover/lean4:v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import ErdosProblems.Erdos721.HunterKernel

/-!
# Resonant phase distribution implies quantitative orbit hits

This file joins the three independently checked ingredients of Hunter's
orbit argument: low-dimensional bounded resonances, phase-distributed center
blocks, and the explicit finite Fourier cutoff.  The conclusion is stated as
an exact torus identity with a controlled Euclidean displacement from one
center in each block.
-/

namespace Erdos721.HunterOrbitCenters

open Function Set
open scoped BigOperators

open HunterTorus HunterPhase HunterLattice HunterCenters HunterDistributedCenters
  HunterDiophantine HunterFourierCutoff HunterKernel

/-- A coordinate box in the torus has a small centered Euclidean lift. -/
lemma centeredLift_norm_le {D : ℕ} {z : Torus D} {radius : ℝ}
    (hradius : 0 ≤ radius) (hz : z ∈ centeredBox D radius) :
    ‖centeredLift z‖ ≤ Real.sqrt D * radius := by
  have hcoord : ∀ i : Fin D, |centeredCoord (z i)| ≤ radius := by
    intro i
    rw [HunterPhase.abs_centeredCoord_eq_norm]
    have hi := hz i (Set.mem_univ i)
    simpa [Metric.mem_closedBall, dist_eq_norm] using hi
  have hsq : ‖centeredLift z‖ ^ 2 ≤ (D : ℝ) * radius ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    change (∑ i : Fin D, |centeredCoord (z i)| ^ 2) ≤ _
    calc
      (∑ i : Fin D, |centeredCoord (z i)| ^ 2) ≤
          ∑ _i : Fin D, radius ^ 2 := by
        apply Finset.sum_le_sum
        intro i _hi
        exact (sq_le_sq₀ (abs_nonneg _) hradius).2 (hcoord i)
      _ = (D : ℝ) * radius ^ 2 := by simp
  have hsqrt0 : 0 ≤ Real.sqrt (D : ℝ) := Real.sqrt_nonneg _
  have hsqrt_sq : Real.sqrt (D : ℝ) ^ 2 = (D : ℝ) :=
    Real.sq_sqrt (by positivity)
  have hnorm0 : 0 ≤ ‖centeredLift z‖ := norm_nonneg _
  apply (sq_le_sq₀ hnorm0 (mul_nonneg hsqrt0 hradius)).1
  rw [mul_pow, hsqrt_sq]
  exact hsq

/-- Every bounded resonant character annihilates the target displacement
provided by the phase-distributed center family. -/
lemma phase_annihilates_center_displacement
    {D H R Y S : ℕ} {phaseRadius epsilon : ℝ}
    {x : CenterFamily Y S D}
    (hdist : PhaseDistributed (H := H) (R := R) phaseRadius x)
    {alpha : Torus D}
    (hrank : Module.finrank ℚ
      (resonanceSubspace (H := H) epsilon alpha) < R)
    (b : Fin Y) (xStar : Torus D) :
    ∃ s : Fin S, ∃ u : EuclideanSpace ℝ (Fin D),
      ‖u‖ ≤ 2 * Real.sqrt R * phaseRadius ∧
        ∀ a : FrequencyCode D H,
          ‖integerDot (decodeFrequency a) alpha‖ ≤ epsilon →
            integerDot (decodeFrequency a)
              (x b s + project u - xStar) = 0 := by
  obtain ⟨xi, hxi⟩ :=
    exists_codedSubspace_eq_resonanceSubspace hrank
  obtain ⟨s, u, hu, hphase⟩ := hdist xi b xStar
  refine ⟨s, u, hu, fun a ha ↦ hphase (decodeFrequency a) ?_⟩
  rw [hxi]
  exact castIntVector_mem_resonanceSubspace
    (show a ∈ resonantCodes epsilon alpha from ha)

/-- A phase-compatible center in each block is hit by a difference of two
initial orbit points.  The cutoff-box error is lifted to Euclidean space and
absorbed into the center correction. -/
theorem exists_orbit_hit_center
    {D H R Y S L : ℕ}
    {phaseRadius cutoffRadius massBound epsilon : ℝ}
    {x : CenterFamily Y S D}
    (hdist : PhaseDistributed (H := H) (R := R) phaseRadius x)
    {alpha : Torus D}
    (hrank : Module.finrank ℚ
      (resonanceSubspace (H := H) epsilon alpha) < R)
    (F : FourierCutoff D H cutoffRadius massBound)
    (hcutoffRadius : 0 ≤ cutoffRadius)
    (hepsilon : 0 < epsilon)
    (hlarge : massBound * (2 * epsilon)⁻¹ ^ 2 < (L : ℝ) ^ 2)
    (b : Fin Y) (xStar : Torus D) :
    ∃ s : Fin S, ∃ i j : Fin L,
      ∃ w : EuclideanSpace ℝ (Fin D),
        ‖w‖ ≤ 2 * Real.sqrt R * phaseRadius +
          Real.sqrt D * cutoffRadius ∧
        i.val • alpha - j.val • alpha + xStar =
          x b s + project w := by
  obtain ⟨s, u, hu, hphase⟩ :=
    phase_annihilates_center_displacement hdist hrank b xStar
  let y : Torus D := x b s + project u - xStar
  obtain ⟨i, j, hij⟩ := exists_orbit_difference_mem_box
    F hepsilon alpha y hphase hlarge
  let z : Torus D := i.val • alpha - j.val • alpha - y
  let v : EuclideanSpace ℝ (Fin D) := centeredLift z
  have hv : ‖v‖ ≤ Real.sqrt D * cutoffRadius :=
    centeredLift_norm_le hcutoffRadius hij
  refine ⟨s, i, j, u + v, (norm_add_le _ _).trans (add_le_add hu hv), ?_⟩
  have hz : project v = z := project_centeredLift z
  dsimp [z, y] at hz
  rw [project_add, hz]
  abel

end Erdos721.HunterOrbitCenters
