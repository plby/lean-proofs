/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open EuclideanGeometry

namespace Erdos898

section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

variable [hV : Fact (Module.finrank ℝ V = 2)]

noncomputable def dist_to_line (P A B : V) : ℝ :=
  dist P (orthogonalProjection (affineSpan ℝ ({A, B} : Set V)) P)

end

theorem erdos_898 {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [Fact (Module.finrank ℝ V = 2)] {A B C P : V}
    (h_triangle : ¬ Collinear ℝ ({A, B, C} : Set V))
    (h_interior : P ∈ interior (convexHull ℝ ({A, B, C} : Set V))) :
    dist P A + dist P B + dist P C ≥
      2 * (dist_to_line P B C + dist_to_line P A C + dist_to_line P A B) := by
  sorry

end Erdos898
