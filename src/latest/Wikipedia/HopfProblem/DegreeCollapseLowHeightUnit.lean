import Wikipedia.HopfProblem.DegreeCollapseLowHeightCylinder

/-!

# The exact height unit in the low-dimensional ambient coordinates

This is the actual height axis, with the same nesting and dimensions as the
constructed cylinder. Its length and scalar multiples are computed directly
from the original coordinate inner product.
-/

noncomputable section

open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.LowSurgery

open NoExoticSixSphere GLOrthonormalization StabilizedSpanningDisk

def heightUnit (d N : ℕ) : Vector (N + (1 + (1 + (d + 1)))) :=
  coordinates N (d + 1) ((0, 1), 0)

theorem smul_heightUnit (d N : ℕ) (t : ℝ) :
    t • heightUnit d N = coordinates N (d + 1) ((0, t), 0) := by
  rw [heightUnit, ← map_smul]
  congr 1
  simp

theorem norm_heightUnit (d N : ℕ) : ‖heightUnit d N‖ = 1 := by
  have hi : inner ℝ (heightUnit d N) (heightUnit d N) = 1 := by
    rw [heightUnit, inner_coordinates]
    norm_num
  rw [real_inner_self_eq_norm_sq] at hi
  nlinarith [norm_nonneg (heightUnit d N)]

end Wikipedia.HopfProblem.DegreeCollapse.LowSurgery
