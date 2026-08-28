import Wikipedia.NoExoticSixSphere.DiskNormalProjection

/-!
# The extension obstruction of a partial normal frame on a disk boundary

The ambient normal space is computed from the actual given injective
differential family. The number of prescribed columns leaves complement
dimension three. Parity zero is exactly extension through normal frames on
the entire closed four-ball, retaining all original boundary values.
-/

noncomputable section

namespace NoExoticSixSphere.Stiefel.DiskNormal

open GLOrthonormalization
open Wikipedia.HopfProblem.DegreeCollapse.DiskCylinder

variable (r : ℕ)
variable (D : C(Disk (E := Vector 4), Vector 4 →L[ℝ] Vector (r + 9)))
variable (hi : ∀ x, Function.Injective (D x))

theorem obstruction_rank :
    Module.finrank ℝ (projectionMap D hi ProjectionDisk.center).range = 3 + (r + 2) := by
  have h := finrank_normal D hi ProjectionDisk.center
  omega

variable (a : C(NoExoticSixSphere.Sphere 3, Space (r + 9) (r + 2)))
variable (ha : ∀ s, (a s).val.range ≤ (D (boundaryToDisk s)).rangeᗮ)

include ha in
theorem boundary_normal_range (s : NoExoticSixSphere.Sphere 3) :
    (a s).val.range ≤ (projectionMap D hi (boundaryToDisk s)).range := by
  rw [projectionMap_range]
  exact ha s

def parity : ZMod 2 :=
  ProjectionObstruction.parity r (projectionMap D hi) (projectionMap_idempotent D hi)
    (obstruction_rank r D hi) a (boundary_normal_range r D hi a ha)

theorem parity_zero_iff_extension : parity r D hi a ha = 0 ↔
    ∃ A : C(Disk (E := Vector 4), Space (r + 9) (r + 2)),
      (∀ x, (A x).val.range ≤ (D x).rangeᗮ) ∧
      ∀ s, A (boundaryToDisk s) = a s := by
  unfold parity
  rw [ProjectionObstruction.parity_zero_iff_extension]
  simp only [projectionMap_range]

end NoExoticSixSphere.Stiefel.DiskNormal
