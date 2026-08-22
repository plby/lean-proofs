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

import ErdosProblems.Erdos1165.RealBoundaryInterior

/-!
# A finite graph annulus at literal real radii

The radii occurring in the HLOZ appendix are real numbers.  This file realizes
the annulus between two such radii as a finite graph without changing either
radius: `boxRadius` supplies only a finite carrier.  The outer disc's inner
vertex boundary is removed, as is the whole inner disc.  Consequently every
one-step graph exit lies on the literal inner vertex boundary of exactly one
of the two discs.
-/

open Set

namespace Erdos1165.LiteralRealAnnulus

open Annulus PotentialEuclideanGeometry RadialHarnackSpecialization
open RealBoundaryInterior ThickPoint

noncomputable section

/-! ## The finite literal annulus -/

/-- The exact graph annulus between `rInner` and `rOuter`.  The natural number
`boxRadius` is used only to make the carrier finite. -/
noncomputable def literalRealAnnulus
    (rInner rOuter : ℝ) (boxRadius : ℕ) : Finset Point := by
  classical
  exact (realBoundaryInterior rOuter boxRadius).filter fun z ↦
    z ∉ ThickPoint.disc 0 rInner

@[simp] theorem mem_literalRealAnnulus_raw
    {rInner rOuter : ℝ} {boxRadius : ℕ} {z : Point} :
    z ∈ literalRealAnnulus rInner rOuter boxRadius ↔
      z ∈ coordinateBox boxRadius ∧
        z ∈ ThickPoint.disc 0 rOuter ∧
          z ∉ ThickPoint.discBoundary 0 rOuter ∧
            z ∉ ThickPoint.disc 0 rInner := by
  simp only [literalRealAnnulus, Finset.mem_filter,
    mem_realBoundaryInterior_raw]
  tauto

/-- Exact membership.  Under containment of the outer disc in the coordinate
box, the auxiliary finite carrier disappears from the statement. -/
@[simp] theorem mem_literalRealAnnulus_iff
    {rInner rOuter : ℝ} {boxRadius : ℕ}
    (hrOuter : 0 ≤ rOuter) (hOuterBox : rOuter ≤ (boxRadius : ℝ))
    {z : Point} :
    z ∈ literalRealAnnulus rInner rOuter boxRadius ↔
      z ∈ ThickPoint.disc 0 rOuter ∧
        z ∉ ThickPoint.discBoundary 0 rOuter ∧
          z ∉ ThickPoint.disc 0 rInner := by
  rw [mem_literalRealAnnulus_raw]
  constructor
  · exact fun hz ↦ hz.2
  · intro hz
    exact ⟨disc_zero_subset_coordinateBox hrOuter hOuterBox hz.1, hz⟩

theorem literalRealAnnulus_subset_coordinateBox
    (rInner rOuter : ℝ) (boxRadius : ℕ) :
    literalRealAnnulus rInner rOuter boxRadius ⊆ coordinateBox boxRadius := by
  intro z hz
  exact (mem_literalRealAnnulus_raw.mp hz).1

/-! ## Exact exit-boundary partition -/

/-- Exits through the deleted inner disc. -/
noncomputable def literalRealAnnulusInnerExit
    (rInner rOuter : ℝ) (boxRadius : ℕ) : Finset Point := by
  classical
  exact
    (outerBoundary (literalRealAnnulus rInner rOuter boxRadius)).filter fun z ↦
      z ∈ ThickPoint.disc 0 rInner

/-- All other exits; these will be exactly exits through the outer disc's
literal inner vertex boundary. -/
noncomputable def literalRealAnnulusOuterExit
    (rInner rOuter : ℝ) (boxRadius : ℕ) : Finset Point :=
  outerBoundary (literalRealAnnulus rInner rOuter boxRadius) \
    literalRealAnnulusInnerExit rInner rOuter boxRadius

@[simp] theorem mem_literalRealAnnulusInnerExit
    (rInner rOuter : ℝ) (boxRadius : ℕ) (z : Point) :
    z ∈ literalRealAnnulusInnerExit rInner rOuter boxRadius ↔
      z ∈ outerBoundary (literalRealAnnulus rInner rOuter boxRadius) ∧
        z ∈ ThickPoint.disc 0 rInner := by
  simp [literalRealAnnulusInnerExit]

@[simp] theorem mem_literalRealAnnulusOuterExit
    (rInner rOuter : ℝ) (boxRadius : ℕ) (z : Point) :
    z ∈ literalRealAnnulusOuterExit rInner rOuter boxRadius ↔
      z ∈ outerBoundary (literalRealAnnulus rInner rOuter boxRadius) ∧
        z ∉ ThickPoint.disc 0 rInner := by
  unfold literalRealAnnulusOuterExit
  rw [Finset.mem_sdiff]
  constructor
  · rintro ⟨hzOuter, hzNotInnerExit⟩
    refine ⟨hzOuter, ?_⟩
    intro hzInnerDisc
    exact hzNotInnerExit ((mem_literalRealAnnulusInnerExit
      rInner rOuter boxRadius z).mpr ⟨hzOuter, hzInnerDisc⟩)
  · rintro ⟨hzOuter, hzNotInnerDisc⟩
    refine ⟨hzOuter, ?_⟩
    intro hzInnerExit
    exact hzNotInnerDisc ((mem_literalRealAnnulusInnerExit
      rInner rOuter boxRadius z).mp hzInnerExit).2

private theorem adjacent_neighbor_reverse (x : Point) (d : Direction) :
    ThickPoint.Adjacent (neighbor x d) x := by
  rcases x with ⟨x₁, x₂⟩
  fin_cases d <;> simp [ThickPoint.Adjacent, neighbor, directionVector]

/-- Every inner-side graph exit lies on the literal boundary of the inner
real-radius disc. -/
theorem literalRealAnnulusInnerExit_subset_discBoundary
    {rInner rOuter : ℝ} {boxRadius : ℕ} :
    ↑(literalRealAnnulusInnerExit rInner rOuter boxRadius) ⊆
      ThickPoint.discBoundary 0 rInner := by
  intro z hz
  have hzData := (mem_literalRealAnnulusInnerExit
    rInner rOuter boxRadius z).mp hz
  rw [mem_outerBoundary] at hzData
  obtain ⟨_hzNot, x, hx, d, rfl⟩ := hzData.1
  have hxNotInner : x ∉ ThickPoint.disc 0 rInner :=
    (mem_literalRealAnnulus_raw.mp hx).2.2.2
  exact ⟨hzData.2, x, hxNotInner, adjacent_neighbor_reverse x d⟩

/-- Every outer-side graph exit lies on the literal boundary of the outer
real-radius disc. -/
theorem literalRealAnnulusOuterExit_subset_discBoundary
    {rInner rOuter : ℝ} {boxRadius : ℕ}
    (hrOuter : 0 ≤ rOuter) (hOuterBox : rOuter ≤ (boxRadius : ℝ)) :
    ↑(literalRealAnnulusOuterExit rInner rOuter boxRadius) ⊆
      ThickPoint.discBoundary 0 rOuter := by
  classical
  intro z hz
  have hzData := (mem_literalRealAnnulusOuterExit
    rInner rOuter boxRadius z).mp hz
  rw [mem_outerBoundary] at hzData
  obtain ⟨hzNot, x, hx, d, rfl⟩ := hzData.1
  have hxInterior : x ∈ realBoundaryInterior rOuter boxRadius := by
    change x ∈ (realBoundaryInterior rOuter boxRadius).filter
      (fun z ↦ z ∉ ThickPoint.disc 0 rInner) at hx
    exact (Finset.mem_filter.mp hx).1
  have hcases := neighbor_mem_realBoundaryInterior_or_discBoundary
    hrOuter hOuterBox hxInterior d
  exact hcases.resolve_left fun hneighborInterior ↦ hzNot
    (Finset.mem_filter.mpr ⟨hneighborInterior, hzData.2⟩)

theorem literalRealAnnulus_exit_union
    (rInner rOuter : ℝ) (boxRadius : ℕ) :
    literalRealAnnulusInnerExit rInner rOuter boxRadius ∪
        literalRealAnnulusOuterExit rInner rOuter boxRadius =
      outerBoundary (literalRealAnnulus rInner rOuter boxRadius) := by
  unfold literalRealAnnulusOuterExit
  apply Finset.union_sdiff_of_subset
  intro z hz
  exact (mem_literalRealAnnulusInnerExit
    rInner rOuter boxRadius z).mp hz |>.1

theorem literalRealAnnulus_exit_disjoint
    (rInner rOuter : ℝ) (boxRadius : ℕ) :
    Disjoint (literalRealAnnulusInnerExit rInner rOuter boxRadius)
      (literalRealAnnulusOuterExit rInner rOuter boxRadius) := by
  rw [Finset.disjoint_left]
  intro z hzInner hzOuter
  exact (mem_literalRealAnnulusOuterExit
    rInner rOuter boxRadius z).mp hzOuter |>.2
      ((mem_literalRealAnnulusInnerExit
        rInner rOuter boxRadius z).mp hzInner |>.2)

/-! ## Intermediate boundaries start inside the annulus -/

/-- A point on a literal real-radius disc boundary lies in the unit shell
immediately inside that radius. -/
theorem discBoundary_zero_euclideanRadius_bounds_real
    {R : ℝ} {z : Point} (hz : z ∈ ThickPoint.discBoundary 0 R) :
    R - 1 < euclideanRadius z ∧ euclideanRadius z ≤ R := by
  rcases hz with ⟨hzIn, y, hyOut, hzy⟩
  have hzUpper : euclideanRadius z ≤ R := by
    simpa [ThickPoint.disc, latticeDistance_zero_eq_euclideanRadius] using hzIn
  have hyLower : R < euclideanRadius y := by
    simpa [ThickPoint.disc, latticeDistance_zero_eq_euclideanRadius] using hyOut
  have hgap := abs_euclideanRadius_sub_le_of_adjacent hzy
  exact ⟨by linarith [(abs_le.mp hgap).1], hzUpper⟩

/-- A point on an intermediate boundary belongs to the exact graph annulus
when both neighboring radii are separated from it by at least one lattice
step. -/
theorem mem_literalRealAnnulus_of_mem_intermediate_discBoundary
    {rInner rMiddle rOuter : ℝ} {boxRadius : ℕ}
    (hrOuter : 0 ≤ rOuter) (hOuterBox : rOuter ≤ (boxRadius : ℝ))
    (hInnerSep : rInner + 1 ≤ rMiddle)
    (hOuterSep : rMiddle + 1 ≤ rOuter)
    {z : Point} (hz : z ∈ ThickPoint.discBoundary 0 rMiddle) :
    z ∈ literalRealAnnulus rInner rOuter boxRadius := by
  have hzBounds := discBoundary_zero_euclideanRadius_bounds_real hz
  apply (mem_literalRealAnnulus_iff hrOuter hOuterBox).mpr
  refine ⟨?_, ?_, ?_⟩
  · simpa [ThickPoint.disc, latticeDistance_zero_eq_euclideanRadius] using
      hzBounds.2.trans (by linarith : rMiddle ≤ rOuter)
  · intro hzOuterBoundary
    have hzOuterBounds :=
      discBoundary_zero_euclideanRadius_bounds_real hzOuterBoundary
    linarith
  · intro hzInnerDisc
    have hzInnerUpper : euclideanRadius z ≤ rInner := by
      simpa [ThickPoint.disc, latticeDistance_zero_eq_euclideanRadius] using
        hzInnerDisc
    linarith

end

end Erdos1165.LiteralRealAnnulus
