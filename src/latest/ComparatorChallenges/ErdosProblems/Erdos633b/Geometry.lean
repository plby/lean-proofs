import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.Geometry.Euclidean.Triangle
import Mathlib.LinearAlgebra.AffineSpace.Simplex.Basic
import Mathlib.Logic.Equiv.Fin.Basic

namespace Erdos633b

abbrev Plane := EuclideanSpace ℝ (Fin 2)

abbrev Triangle := Affine.Triangle ℝ Plane

namespace Triangle

def support (T : Triangle) : Set Plane := convexHull ℝ (Set.range T.points)

noncomputable def angle (T : Triangle) (i : Fin 3) : ℝ :=
  EuclideanGeometry.angle (T.points (i + 1)) (T.points i) (T.points (i + 2))

noncomputable def side (T : Triangle) (i : Fin 3) : ℝ :=
  dist (T.points (i + 1)) (T.points (i + 2))

end Triangle

structure Tiling (T : Triangle) (n : ℕ) where
  tile : Triangle
  place : Fin n → Plane ≃ᵃⁱ[ℝ] Plane
  covers : (⋃ i, place i '' tile.support) = T.support
  disjoint_interiors : Pairwise fun i j =>
    Disjoint (interior (place i '' tile.support)) (interior (place j '' tile.support))

end Erdos633b
