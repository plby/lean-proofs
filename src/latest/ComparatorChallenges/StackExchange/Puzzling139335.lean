/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib
import Wikipedia.SchoenfliesTheorem.CrosscutCells

open Set

namespace Puzzling139335

abbrev Plane := EuclideanSpace ℝ (Fin 2)

def unitSquare : Set Plane :=
  {p | p 0 ∈ Icc (0 : ℝ) 1 ∧ p 1 ∈ Icc (0 : ℝ) 1}

noncomputable def squareCenter : Plane := !₂[(1 / 2 : ℝ), (1 / 2 : ℝ)]

def IsJordanRegion (P : Set Plane) : Prop :=
  ∃ C : Set Plane, Schoenflies.IsJordanCurve C ∧ P = closure (Schoenflies.inside C)

def Congruent (P Q : Set Plane) : Prop :=
  ∃ e : Plane ≃ᵃⁱ[ℝ] Plane, e '' P = Q

structure SquareDissection where
  piece : Fin 4 → Set Plane
  jordan : ∀ i, IsJordanRegion (piece i)
  congruent : ∀ i j, Congruent (piece i) (piece j)
  covers : (⋃ i, piece i) = unitSquare
  disjoint_interiors : Pairwise fun i j => Disjoint (interior (piece i)) (interior (piece j))

theorem square_center_theorem :
    ∀ d : SquareDissection, ¬ ∃ i : Fin 4, squareCenter ∈ interior (d.piece i) := by
  sorry

end Puzzling139335
