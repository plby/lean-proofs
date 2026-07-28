import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

namespace Theorem87

abbrev Plane : Type := EuclideanSpace ℝ (Fin 2)

def IntersectsIn (A B A' B' P : Plane) : Prop :=
  Collinear ℝ ({A, B, P} : Set Plane) ∧
    Collinear ℝ ({A', B', P} : Set Plane)

def UniqueIntersection (A B A' B' P : Plane) : Prop :=
  IntersectsIn A B A' B' P ∧
    ∀ Q, IntersectsIn A B A' B' Q → Q = P

theorem desargues_plane
    {A B C A' B' C' O Pab Pbc Pca : Plane}
    (hO_AA' : Collinear ℝ ({A, A', O} : Set Plane))
    (hO_BB' : Collinear ℝ ({B, B', O} : Set Plane))
    (hO_CC' : Collinear ℝ ({C, C', O} : Set Plane))
    (hPab : UniqueIntersection A B A' B' Pab)
    (hPbc : UniqueIntersection B C B' C' Pbc)
    (hPca : UniqueIntersection C A C' A' Pca) :
    Collinear ℝ ({Pab, Pbc, Pca} : Set Plane) := by
  sorry

end Theorem87
