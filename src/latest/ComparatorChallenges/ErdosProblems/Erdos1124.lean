/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

/-!
# Erdős Problem 1124

Tarski's circle-squaring problem asks whether a disk and a square of the same
area possess finite decompositions into pairwise congruent pieces.  Laczkovich
proved the stronger assertion that the motions can all be translations.

The mathematical reconstruction and a map of the formal proof are in
`tex/1124.tex`.
-/

open Set MeasureTheory Metric

namespace Erdos1124

noncomputable section

/-- The Euclidean plane used in the statement. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- The closed disk of radius `r` centered at the origin. -/
def disk (r : ℝ) : Set Plane := closedBall 0 r

/-- The side length of the square having the same area as `disk r`. -/
def squareSide (r : ℝ) : ℝ := Real.sqrt Real.pi * r

/-- The closed, origin-centered, axis-parallel square whose side length is
`sqrt π * r`.  `WithLp.ofLp` exposes the two coordinates of a point of the
Euclidean plane. -/
def square (r : ℝ) : Set Plane :=
  (@WithLp.ofLp 2 (Fin 2 → ℝ)) ⁻¹'
    Icc (fun _ ↦ -(squareSide r) / 2) (fun _ ↦ squareSide r / 2)

/-- Equidecomposability using translations only.  Mathlib's `Equidecomp`
stores a partial bijection and a finite set of acting group elements.  The
canonical action of `Multiplicative Plane` is vector addition. -/
def TranslationEquidecomposable (A B : Set Plane) : Prop :=
  ∃ e : Equidecomp Plane (Multiplicative Plane), e.source = A ∧ e.target = B

/-- The standard volume formula for the disk, in the exact normalization used
in the final statement. -/


theorem erdos_1124 (r : ℝ) (hr : 0 < r) :
    TranslationEquidecomposable (disk r) (square r) := by
  sorry

end

end Erdos1124
