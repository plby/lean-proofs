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

import ErdosProblems.Erdos1165.ThickPoint

/-!
# Finiteness of literal real-radius lattice discs

The HLOZ annular radii are real numbers, whereas the state space is
`\mathbb Z^2`.  This file supplies a finite coordinate carrier for the literal
sets `ThickPoint.disc center R` and `ThickPoint.discBoundary center R`, without
rounding either set in their definitions.  Filtering the carrier gives
canonical finsets whose membership theorems expose the original literal
sets.  The constructions work for every real radius (a negative-radius disc
is empty); in particular they apply under the customary hypothesis `0 ≤ R`.
-/

open Set

namespace Erdos1165.RealDiscFinite

open ThickPoint

noncomputable section

/-! ## Coordinate bounds -/

/-- Each Cartesian coordinate difference is bounded by the Euclidean lattice
distance. -/
theorem abs_fst_sub_le_latticeDistance (x y : Point) :
    |(((x.1 - y.1 : ℤ) : ℝ))| ≤ latticeDistance x y := by
  let a : ℝ := ((x.1 - y.1 : ℤ) : ℝ)
  let b : ℝ := ((x.2 - y.2 : ℤ) : ℝ)
  have hsum : 0 ≤ a ^ 2 + b ^ 2 := by positivity
  have hsqrt0 : 0 ≤ Real.sqrt (a ^ 2 + b ^ 2) := Real.sqrt_nonneg _
  have hsqrtSq := Real.sq_sqrt hsum
  have ha0 : 0 ≤ |a| := abs_nonneg _
  have haSq : |a| ^ 2 = a ^ 2 := sq_abs a
  unfold latticeDistance squaredDistance
  change |a| ≤ Real.sqrt (a ^ 2 + b ^ 2)
  nlinarith [sq_nonneg b]

/-- The second Cartesian coordinate difference is bounded by the Euclidean
lattice distance. -/
theorem abs_snd_sub_le_latticeDistance (x y : Point) :
    |(((x.2 - y.2 : ℤ) : ℝ))| ≤ latticeDistance x y := by
  let a : ℝ := ((x.1 - y.1 : ℤ) : ℝ)
  let b : ℝ := ((x.2 - y.2 : ℤ) : ℝ)
  have hsum : 0 ≤ a ^ 2 + b ^ 2 := by positivity
  have hsqrt0 : 0 ≤ Real.sqrt (a ^ 2 + b ^ 2) := Real.sqrt_nonneg _
  have hsqrtSq := Real.sq_sqrt hsum
  have hb0 : 0 ≤ |b| := abs_nonneg _
  have hbSq : |b| ^ 2 = b ^ 2 := sq_abs b
  unfold latticeDistance squaredDistance
  change |b| ≤ Real.sqrt (a ^ 2 + b ^ 2)
  nlinarith [sq_nonneg a]

/-! ## A finite carrier and exact finsets -/

/-- An integer coordinate radius large enough to contain the literal disc.
Taking the ceiling after `max R 0` also makes the carrier harmless for a
negative radius. -/
noncomputable def discBoxRadius (R : ℝ) : ℕ := ⌈max R 0⌉₊

theorem le_discBoxRadius (R : ℝ) :
    R ≤ (discBoxRadius R : ℝ) := by
  exact (le_max_left R 0).trans (Nat.le_ceil (max R 0))

/-- The finite square centered at `center` with coordinate radius
`discBoxRadius R`. -/
noncomputable def discBox (center : Point) (R : ℝ) : Finset Point :=
  (Finset.Icc (center.1 - (discBoxRadius R : ℤ))
      (center.1 + (discBoxRadius R : ℤ))).product
    (Finset.Icc (center.2 - (discBoxRadius R : ℤ))
      (center.2 + (discBoxRadius R : ℤ)))

@[simp] theorem mem_discBox {center z : Point} {R : ℝ} :
    z ∈ discBox center R ↔
      center.1 - (discBoxRadius R : ℤ) ≤ z.1 ∧
      z.1 ≤ center.1 + (discBoxRadius R : ℤ) ∧
      center.2 - (discBoxRadius R : ℤ) ≤ z.2 ∧
      z.2 ≤ center.2 + (discBoxRadius R : ℤ) := by
  simp [discBox, and_assoc]

/-- The literal real-radius disc is contained in its finite coordinate
carrier. -/
theorem disc_subset_discBox (center : Point) (R : ℝ) :
    disc center R ⊆ (discBox center R : Set Point) := by
  intro z hz
  have hRbox : R ≤ (discBoxRadius R : ℝ) := le_discBoxRadius R
  have hfstReal :
      |(((center.1 - z.1 : ℤ) : ℝ))| ≤ (discBoxRadius R : ℝ) :=
    (abs_fst_sub_le_latticeDistance center z).trans (hz.trans hRbox)
  have hsndReal :
      |(((center.2 - z.2 : ℤ) : ℝ))| ≤ (discBoxRadius R : ℝ) :=
    (abs_snd_sub_le_latticeDistance center z).trans (hz.trans hRbox)
  have hfstLowerReal :
      (-(discBoxRadius R : ℤ) : ℝ) ≤ ((center.1 - z.1 : ℤ) : ℝ) := by
    exact (neg_le_of_abs_le hfstReal)
  have hfstUpperReal :
      ((center.1 - z.1 : ℤ) : ℝ) ≤ ((discBoxRadius R : ℕ) : ℝ) := by
    exact (le_of_abs_le hfstReal)
  have hsndLowerReal :
      (-(discBoxRadius R : ℤ) : ℝ) ≤ ((center.2 - z.2 : ℤ) : ℝ) := by
    exact (neg_le_of_abs_le hsndReal)
  have hsndUpperReal :
      ((center.2 - z.2 : ℤ) : ℝ) ≤ ((discBoxRadius R : ℕ) : ℝ) := by
    exact (le_of_abs_le hsndReal)
  have hfstLower : -(discBoxRadius R : ℤ) ≤ center.1 - z.1 := by
    exact_mod_cast hfstLowerReal
  have hfstUpper : center.1 - z.1 ≤ (discBoxRadius R : ℤ) := by
    exact_mod_cast hfstUpperReal
  have hsndLower : -(discBoxRadius R : ℤ) ≤ center.2 - z.2 := by
    exact_mod_cast hsndLowerReal
  have hsndUpper : center.2 - z.2 ≤ (discBoxRadius R : ℤ) := by
    exact_mod_cast hsndUpperReal
  change z ∈ discBox center R
  rw [mem_discBox]
  omega

/-- Canonical finite enumeration of the literal disc. -/
noncomputable def discFinset (center : Point) (R : ℝ) : Finset Point :=
  by
    classical
    exact (discBox center R).filter fun z ↦ z ∈ disc center R

/-- Membership in `discFinset` is exactly membership in the original literal
real-radius disc; the coordinate box is only a finiteness witness. -/
@[simp] theorem mem_discFinset {center z : Point} {R : ℝ} :
    z ∈ discFinset center R ↔ z ∈ disc center R := by
  classical
  rw [discFinset, Finset.mem_filter]
  constructor
  · exact fun hz ↦ hz.2
  · exact fun hz ↦ ⟨disc_subset_discBox center R hz, hz⟩

/-- Canonical finite enumeration of the literal inner vertex boundary. -/
noncomputable def discBoundaryFinset (center : Point) (R : ℝ) : Finset Point :=
  by
    classical
    exact (discFinset center R).filter fun z ↦ z ∈ discBoundary center R

theorem discBoundary_subset_disc (center : Point) (R : ℝ) :
    discBoundary center R ⊆ disc center R := by
  intro z hz
  exact hz.1

/-- Membership in `discBoundaryFinset` is exactly membership in the literal
inner vertex boundary. -/
@[simp] theorem mem_discBoundaryFinset {center z : Point} {R : ℝ} :
    z ∈ discBoundaryFinset center R ↔ z ∈ discBoundary center R := by
  classical
  rw [discBoundaryFinset, Finset.mem_filter, mem_discFinset]
  constructor
  · exact fun hz ↦ hz.2
  · exact fun hz ↦ ⟨discBoundary_subset_disc center R hz, hz⟩

/-! ## Set finiteness and canonical finite subtypes -/

theorem finite_disc (center : Point) (R : ℝ) :
    (disc center R).Finite := by
  rw [← show (discFinset center R : Set Point) = disc center R by
    ext z
    simp]
  exact Finset.finite_toSet _

theorem finite_discBoundary (center : Point) (R : ℝ) :
    (discBoundary center R).Finite := by
  rw [← show (discBoundaryFinset center R : Set Point) =
      discBoundary center R by
    ext z
    simp]
  exact Finset.finite_toSet _

/-- The subtype of lattice points in the literal real-radius disc. -/
abbrev DiscPoint (center : Point) (R : ℝ) :=
  {z : Point // z ∈ disc center R}

/-- The subtype of lattice points on the literal inner vertex boundary. -/
abbrev DiscBoundaryPoint (center : Point) (R : ℝ) :=
  {z : Point // z ∈ discBoundary center R}

noncomputable instance discPointFintype (center : Point) (R : ℝ) :
    Fintype (DiscPoint center R) :=
  Fintype.ofFinset (discFinset center R) (fun _ ↦ mem_discFinset)

noncomputable instance discBoundaryPointFintype (center : Point) (R : ℝ) :
    Fintype (DiscBoundaryPoint center R) :=
  Fintype.ofFinset (discBoundaryFinset center R)
    (fun _ ↦ mem_discBoundaryFinset)

/-- Canonical enumeration of the finite disc subtype. -/
noncomputable def discPointFinset (center : Point) (R : ℝ) :
    Finset (DiscPoint center R) := Finset.univ

/-- Canonical enumeration of the finite boundary subtype. -/
noncomputable def discBoundaryPointFinset (center : Point) (R : ℝ) :
    Finset (DiscBoundaryPoint center R) := Finset.univ

@[simp] theorem mem_discPointFinset {center : Point} {R : ℝ}
    (z : DiscPoint center R) :
    z ∈ discPointFinset center R := by
  simp [discPointFinset]

@[simp] theorem mem_discBoundaryPointFinset {center : Point} {R : ℝ}
    (z : DiscBoundaryPoint center R) :
    z ∈ discBoundaryPointFinset center R := by
  simp [discBoundaryPointFinset]

end

end Erdos1165.RealDiscFinite
