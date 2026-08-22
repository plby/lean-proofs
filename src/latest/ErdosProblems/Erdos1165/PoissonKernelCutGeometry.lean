/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
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

import ErdosProblems.Erdos1165.BoundaryStoppedHarnack

/-!
# A finite radial cut for the boundary-stopped disc

For a radius `S`, we remove the two-unit open Euclidean shell `(S,S+2)`
from the graph interior of the radius-`R` disc.  A nearest-neighbor edge
changes Euclidean radius by at most one, so the remaining finite domain has
no path from the component of radius at most `S` to the component of radius
at least `S+2`.

The final two theorems record this separation directly for the killed powers
and the infinite killed Green function.  They are deliberately stated for
arbitrary inner and outer endpoints, so in a last-exit argument the outer
endpoint may be either the boundary predecessor or any other point beyond
the cut.
-/

open scoped BigOperators ENNReal

namespace Erdos1165.PoissonKernelCutGeometry

open BoundaryStoppedHarnack GreenFunction GreenProbability
open PotentialEuclideanGeometry PotentialRadialAsymptotic

noncomputable section

/-- The finite two-unit radial barrier inside the literal boundary-stopped
disc.  Intersecting with `boundaryInterior R` makes finiteness explicit and
ensures that deleting the cut is an operation on the killed domain itself. -/
noncomputable def thickRadialCut (R S : ℕ) : Finset Point :=
  (boundaryInterior R).filter fun z ↦
    (S : ℝ) < euclideanRadius z ∧ euclideanRadius z < S + 2

/-- The boundary-stopped graph interior with the radial barrier removed. -/
noncomputable def cutBoundaryInterior (R S : ℕ) : Finset Point :=
  boundaryInterior R \ thickRadialCut R S

@[simp] theorem mem_thickRadialCut {R S : ℕ} {z : Point} :
    z ∈ thickRadialCut R S ↔
      z ∈ boundaryInterior R ∧
        (S : ℝ) < euclideanRadius z ∧ euclideanRadius z < S + 2 := by
  simp [thickRadialCut]

@[simp] theorem mem_cutBoundaryInterior {R S : ℕ} {z : Point} :
    z ∈ cutBoundaryInterior R S ↔
      z ∈ boundaryInterior R ∧
        ¬ ((S : ℝ) < euclideanRadius z ∧ euclideanRadius z < S + 2) := by
  rw [cutBoundaryInterior, Finset.mem_sdiff, mem_thickRadialCut]
  tauto

theorem thickRadialCut_subset_boundaryInterior (R S : ℕ) :
    thickRadialCut R S ⊆ boundaryInterior R := by
  intro z hz
  exact (mem_thickRadialCut.mp hz).1

theorem cutBoundaryInterior_subset_boundaryInterior (R S : ℕ) :
    cutBoundaryInterior R S ⊆ boundaryInterior R := by
  intro z hz
  exact (mem_cutBoundaryInterior.mp hz).1

/-- A neighbor of an inner-side point which survives deletion of the cut is
still on the inner side.  This is the local separation fact iterated by the
killed kernel below. -/
theorem euclideanRadius_le_of_neighbor_mem_cutBoundaryInterior
    {R S : ℕ} {x z : Point}
    (hx : euclideanRadius x ≤ S)
    (hz : z ∈ cutBoundaryInterior R S)
    (hneighbor : ∃ d : Direction, z = x + directionVector d) :
    euclideanRadius z ≤ S := by
  obtain ⟨d, rfl⟩ := hneighbor
  have hgap :=
    abs_euclideanRadius_sub_neighbor_le (x + directionVector d) d
  rw [add_sub_cancel_right] at hgap
  by_contra hnot
  have hSlt : (S : ℝ) < euclideanRadius (x + directionVector d) :=
    lt_of_not_ge hnot
  have hupper :
      euclideanRadius (x + directionVector d) < (S : ℝ) + 2 := by
    have hstep :
        euclideanRadius (x + directionVector d) - euclideanRadius x ≤ 1 :=
      (abs_le.mp hgap).2
    have hx' : euclideanRadius x ≤ (S : ℝ) := by exact_mod_cast hx
    linarith
  exact (mem_cutBoundaryInterior.mp hz).2 ⟨hSlt, hupper⟩

/-- Removing the thick radial cut kills every fixed-length path from its
inner component to its outer component. -/
theorem killedPower_cutBoundaryInterior_eq_zero
    {R S n : ℕ} {x y : Point}
    (hx : euclideanRadius x ≤ S)
    (hy : (S : ℝ) + 2 ≤ euclideanRadius y) :
    killedPower planarKernel (cutBoundaryInterior R S) n x y = 0 := by
  induction n generalizing x with
  | zero =>
      have hxy : x ≠ y := by
        intro h
        subst y
        have hx' : euclideanRadius x ≤ (S : ℝ) := by exact_mod_cast hx
        linarith
      exact killedPower_zero_ne planarKernel (cutBoundaryInterior R S) hxy
  | succ n ih =>
      rw [killedPower_succ]
      by_cases hxD : x ∈ cutBoundaryInterior R S
      · rw [if_pos hxD]
        apply Finset.sum_eq_zero
        intro z hz
        by_cases hneighbor : ∃ d : Direction, z = x + directionVector d
        · have hzInner : euclideanRadius z ≤ S :=
            euclideanRadius_le_of_neighbor_mem_cutBoundaryInterior hx hz
              hneighbor
          rw [ih hzInner, mul_zero]
        · have hkernel : planarKernel x z = 0 := by
            apply planarKernel_eq_zero_of_not_neighbor
            intro d hzx
            exact hneighbor ⟨d, hzx⟩
          rw [hkernel, zero_mul]
      · rw [if_neg hxD]

/-- Consequently the infinite killed Green function across the radial cut is
identically zero. -/
theorem infiniteGreen_cutBoundaryInterior_eq_zero
    {R S : ℕ} {x y : Point}
    (hx : euclideanRadius x ≤ S)
    (hy : (S : ℝ) + 2 ≤ euclideanRadius y) :
    infiniteGreen (cutBoundaryInterior R S) x y = 0 := by
  simp [infiniteGreen, killedPower_cutBoundaryInterior_eq_zero hx hy]

end

end Erdos1165.PoissonKernelCutGeometry
