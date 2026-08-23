/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos735

open scoped BigOperators

noncomputable section

/-- The concrete real affine plane used in Problem 735. -/
abbrev Point := EuclideanSpace ℝ (Fin 2)

/-- The affine orientation determinant of three planar points. -/
def orientationDet (p q r : Point) : ℝ :=
  (q 0 - p 0) * (r 1 - p 1) - (q 1 - p 1) * (r 0 - p 0)

/-- Three concrete planar points are collinear exactly when their
orientation determinant vanishes. -/
def Collinear3 (p q r : Point) : Prop := orientationDet p q r = 0

/-- The points on the affine line spanned by two distinct points. -/
noncomputable def lineFiber (P : Finset Point) (p q : Point) : Finset Point := by
  classical
  exact P.filter fun r ↦ Collinear3 p q r

/-- Positive point weights with one common sum on every spanned line. -/
def IsMagic (P : Finset Point) : Prop :=
  ∃ (w : Point → ℝ) (c : ℝ),
    (∀ p ∈ P, 0 < w p) ∧ 0 < c ∧
      ∀ p ∈ P, ∀ q ∈ P, p ≠ q → (∑ x ∈ lineFiber P p q, w x) = c

/-- Every spanned line contains all the points. -/
def IsCollinearConfig (P : Finset Point) : Prop :=
  ∀ p ∈ P, ∀ q ∈ P, p ≠ q → lineFiber P p q = P

/-- Every spanned line contains exactly its two spanning points. -/
def InGeneralPosition (P : Finset Point) : Prop :=
  ∀ p ∈ P, ∀ q ∈ P, p ≠ q → lineFiber P p q = {p, q}

/-- Exactly one point is off a genuine line containing all remaining points. -/
def IsNearPencil (P : Finset Point) : Prop :=
  ∃ z ∈ P,
    2 ≤ (P.erase z).card ∧
      (∀ p ∈ P.erase z, ∀ q ∈ P.erase z, p ≠ q →
        lineFiber P p q = P.erase z) ∧
      ∀ q ∈ P.erase z, lineFiber P z q = {z, q}

/-- Labels for the seven points of the failed Fano configuration. -/
abbrev FailedFanoLabel := Fin 7

/-- The nine lines spanned by the canonical failed Fano configuration. -/
def failedFanoBlocks : Finset (Finset FailedFanoLabel) :=
  { {0, 3, 4}, {0, 5, 6},
    {1, 3, 5}, {1, 4, 6},
    {2, 3, 6}, {2, 4, 5},
    {0, 1}, {0, 2}, {1, 2} }

/-- The canonical line fiber through two failed-Fano labels. -/
def failedFanoLine (i j : FailedFanoLabel) : Finset FailedFanoLabel :=
  Finset.univ.filter fun k ↦
    ∃ B ∈ failedFanoBlocks, i ∈ B ∧ j ∈ B ∧ k ∈ B

/-- An injectively labelled copy of the canonical failed Fano incidence table. -/
def IsFailedFano (P : Finset Point) : Prop :=
  ∃ e : FailedFanoLabel ↪ Point,
    P = Finset.univ.map e ∧
      ∀ i j : FailedFanoLabel, i ≠ j →
        lineFiber P (e i) (e j) = (failedFanoLine i j).map e

/-- The complete classification of finite magic planar configurations. -/
theorem erdos_735 (P : Finset Point) :
    IsMagic P ↔
      IsCollinearConfig P ∨ InGeneralPosition P ∨
        IsNearPencil P ∨ IsFailedFano P := by
  sorry

end

end Erdos735
