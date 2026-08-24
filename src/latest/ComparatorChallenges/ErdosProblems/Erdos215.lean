/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos215

abbrev Point : Type := EuclideanSpace ℝ (Fin 2)

abbrev IntPoint : Type := Fin 2 → ℤ

def intPoint (z : IntPoint) : Point :=
  WithLp.toLp 2 (fun i ↦ (z i : ℝ))

def integerLattice : Set Point := Set.range intPoint

def rotate (c s : ℝ) (p : Point) : Point :=
  WithLp.toLp 2 fun i : Fin 2 ↦
    if i = 0 then c * p 0 - s * p 1 else s * p 0 + c * p 1

def motion (t : Point) (c s : ℝ) (p : Point) : Point :=
  t + rotate c s p

def movedSet (S : Set Point) (t : Point) (c s : ℝ) : Set Point :=
  motion t c s '' S

def IsSteinhaus (S : Set Point) : Prop :=
  ∀ (t : Point) (c s : ℝ), c ^ 2 + s ^ 2 = 1 →
    ∃! z : Point, z ∈ integerLattice ∧ z ∈ movedSet S t c s

theorem erdos_215 : ∃ S : Set Point, IsSteinhaus S := by
  sorry

end Erdos215
