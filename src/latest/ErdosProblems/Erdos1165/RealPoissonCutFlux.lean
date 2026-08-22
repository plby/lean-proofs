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

import ErdosProblems.Erdos1165.PoissonKernelExitFlux

/-!
# Real radial cuts and literal-boundary exit flux

This module isolates the two geometric facts needed to transfer a Green
comparison through a real-radius Poisson kernel.

First, deleting the open two-unit shell `(S, S + 2)` from an arbitrary finite
domain separates every point of radius at most `S` from every point of radius
at least `S + 2`.  Second, a point with nonzero one-step flux into the literal
inner boundary of the real disc of radius `R` has radius at least `R - 2`.

All radii in these statements are real.  No rounding is used.
-/

open scoped BigOperators ENNReal

namespace Erdos1165.RealPoissonCutFlux

open BoundaryStoppedHarnack GreenFunction GreenProbability
open PoissonKernelExitFlux PotentialEuclideanGeometry
open PotentialRadialAsymptotic ThickPoint
open RadialHarnackSpecialization

noncomputable section

/-! ## A real radial cut in an arbitrary finite domain -/

/-- The part of a finite domain lying in the open real radial shell
`(S, S + 2)`. -/
noncomputable def realThickRadialCut (D : Finset Point) (S : ℝ) : Finset Point :=
  D.filter fun z ↦ S < euclideanRadius z ∧ euclideanRadius z < S + 2

/-- The finite domain left after removing the open real radial shell. -/
noncomputable def realCut (D : Finset Point) (S : ℝ) : Finset Point :=
  D \ realThickRadialCut D S

@[simp] theorem mem_realThickRadialCut
    {D : Finset Point} {S : ℝ} {z : Point} :
    z ∈ realThickRadialCut D S ↔
      z ∈ D ∧ S < euclideanRadius z ∧ euclideanRadius z < S + 2 := by
  simp [realThickRadialCut]

@[simp] theorem mem_realCut
    {D : Finset Point} {S : ℝ} {z : Point} :
    z ∈ realCut D S ↔
      z ∈ D ∧ ¬ (S < euclideanRadius z ∧ euclideanRadius z < S + 2) := by
  rw [realCut, Finset.mem_sdiff, mem_realThickRadialCut]
  tauto

theorem realThickRadialCut_subset (D : Finset Point) (S : ℝ) :
    realThickRadialCut D S ⊆ D := by
  intro z hz
  exact (mem_realThickRadialCut.mp hz).1

theorem realCut_subset (D : Finset Point) (S : ℝ) :
    realCut D S ⊆ D := by
  intro z hz
  exact (mem_realCut.mp hz).1

/-- A nearest neighbor of an inner-side point which survives deletion of the
cut is still on the inner side. -/
theorem euclideanRadius_le_of_neighbor_mem_realCut
    {D : Finset Point} {S : ℝ} {x z : Point}
    (hx : euclideanRadius x ≤ S)
    (hz : z ∈ realCut D S)
    (hneighbor : ∃ d : Direction, z = x + directionVector d) :
    euclideanRadius z ≤ S := by
  obtain ⟨d, rfl⟩ := hneighbor
  have hgap :=
    abs_euclideanRadius_sub_neighbor_le (x + directionVector d) d
  rw [add_sub_cancel_right] at hgap
  by_contra hnot
  have hSlower : S < euclideanRadius (x + directionVector d) :=
    lt_of_not_ge hnot
  have hupper : euclideanRadius (x + directionVector d) < S + 2 := by
    linarith [(abs_le.mp hgap).2]
  exact (mem_realCut.mp hz).2 ⟨hSlower, hupper⟩

/-- Every fixed-length killed path across the deleted real shell has zero
mass.  The ambient finite domain `D` is completely arbitrary. -/
theorem killedPower_realCut_eq_zero
    {D : Finset Point} {S : ℝ} {n : ℕ} {x y : Point}
    (hx : euclideanRadius x ≤ S)
    (hy : S + 2 ≤ euclideanRadius y) :
    killedPower planarKernel (realCut D S) n x y = 0 := by
  induction n generalizing x with
  | zero =>
      have hxy : x ≠ y := by
        intro h
        subst y
        linarith
      exact killedPower_zero_ne planarKernel _ hxy
  | succ n ih =>
      rw [killedPower_succ]
      by_cases hxD : x ∈ realCut D S
      · rw [if_pos hxD]
        apply Finset.sum_eq_zero
        intro z hz
        by_cases hneighbor : ∃ d : Direction, z = x + directionVector d
        · have hzInner : euclideanRadius z ≤ S :=
            euclideanRadius_le_of_neighbor_mem_realCut hx hz hneighbor
          rw [ih hzInner, mul_zero]
        · have hkernel : planarKernel x z = 0 := by
            apply planarKernel_eq_zero_of_not_neighbor
            intro d hzx
            exact hneighbor ⟨d, hzx⟩
          rw [hkernel, zero_mul]
      · rw [if_neg hxD]

/-- The infinite killed Green function vanishes across the deleted real
shell. -/
theorem infiniteGreen_realCut_eq_zero
    {D : Finset Point} {S : ℝ} {x y : Point}
    (hx : euclideanRadius x ≤ S)
    (hy : S + 2 ≤ euclideanRadius y) :
    infiniteGreen (realCut D S) x y = 0 := by
  simp [infiniteGreen, killedPower_realCut_eq_zero hx hy]

/-! ## Literal real-disc boundary and exit-flux support -/

/-- The literal inner vertex boundary of the real-radius disc is contained
in the exact shell `(R - 1, R]`. -/
theorem discBoundary_zero_euclideanRadius_bounds_real
    {R : ℝ} {z : Point}
    (hz : z ∈ ThickPoint.discBoundary 0 R) :
    R - 1 < euclideanRadius z ∧ euclideanRadius z ≤ R := by
  rcases hz with ⟨hzIn, y, hyOut, hzy⟩
  have hzUpper : euclideanRadius z ≤ R := by
    simpa [ThickPoint.disc, latticeDistance_zero_eq_euclideanRadius] using hzIn
  have hyLower : R < euclideanRadius y := by
    simpa [ThickPoint.disc, latticeDistance_zero_eq_euclideanRadius] using hyOut
  have hgap := abs_euclideanRadius_sub_le_of_adjacent hzy
  exact ⟨by linarith [(abs_le.mp hgap).1], hzUpper⟩

/-- Nonzero one-step flux into a subset of the literal real-radius boundary
can only come from within one further lattice step of that boundary. -/
theorem real_sub_two_le_euclideanRadius_of_exitFlux_ne_zero
    {R : ℝ} (B : Finset Point)
    (hB : ∀ b ∈ B, b ∈ ThickPoint.discBoundary 0 R)
    {a : Point} (hflux : exitFlux B a ≠ 0) :
    R - 2 ≤ euclideanRadius a := by
  obtain ⟨b, hbB, hbKernel⟩ :=
    Finset.exists_ne_zero_of_sum_ne_zero (s := B) (f := planarKernel a) hflux
  have hneighbor : ∃ d : Direction, b = a + directionVector d := by
    by_contra h
    have hzero : planarKernel a b = 0 := by
      apply planarKernel_eq_zero_of_not_neighbor
      intro d hd
      exact h ⟨d, hd⟩
    exact hbKernel hzero
  obtain ⟨d, rfl⟩ := hneighbor
  have hlower :=
    (discBoundary_zero_euclideanRadius_bounds_real
      (hB (a + directionVector d) hbB)).1
  have hgap :=
    abs_euclideanRadius_sub_neighbor_le (a + directionVector d) d
  rw [add_sub_cancel_right] at hgap
  linarith [(abs_le.mp hgap).2]

/-- With `S + 4 ≤ R`, every point carrying nonzero flux into the radius-`R`
literal boundary lies on the outer side of the two-unit cut at radius `S`. -/
theorem cutOuter_le_euclideanRadius_of_exitFlux_ne_zero
    {R S : ℝ} (hSR : S + 4 ≤ R) (B : Finset Point)
    (hB : ∀ b ∈ B, b ∈ ThickPoint.discBoundary 0 R)
    {a : Point} (hflux : exitFlux B a ≠ 0) :
    S + 2 ≤ euclideanRadius a := by
  have hradius :=
    real_sub_two_le_euclideanRadius_of_exitFlux_ne_zero B hB hflux
  linarith

end

end Erdos1165.RealPoissonCutFlux
