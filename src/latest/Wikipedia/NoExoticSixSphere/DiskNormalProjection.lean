import Wikipedia.NoExoticSixSphere.ProjectionDiskObstruction
import Wikipedia.NoExoticSixSphere.SmoothProjection

/-!
# Actual normal spaces of an injective differential family on the four-ball

The normal planes are the orthogonal complements of the original linear-map
ranges. The Gram projection formula proves continuity. Their rank follows
from injectivity, so the intrinsic partial-frame obstruction has no rank or
trivialization hypothesis.
-/

noncomputable section

open scoped Manifold ContDiff

namespace NoExoticSixSphere.Stiefel.DiskNormal

open GLOrthonormalization
open Wikipedia.HopfProblem.DegreeCollapse.DiskCylinder

variable {N : ℕ}
variable (D : C(Disk (E := Vector 4), Vector 4 →L[ℝ] Vector N))
variable (hi : ∀ x, Function.Injective (D x))

def projection (x : Disk (E := Vector 4)) : Vector N →L[ℝ] Vector N :=
  (D x).rangeᗮ.starProjection

include hi in
theorem projection_eq (x : Disk (E := Vector 4)) :
    projection D x = 1 - gramProjection (D x) := by
  rw [projection, Submodule.starProjection_orthogonal', gramProjection_eq_starProjection _ (hi x)]

include hi in
theorem continuous_projection : Continuous (projection D) := by
  have hg : Continuous (fun x ↦ gramProjection (D x)) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    have h : ContinuousAt (gramProjection : (Vector 4 →L[ℝ] Vector N) →
        (Vector N →L[ℝ] Vector N)) (D x) :=
      (contMDiffAt_gramProjection (I := 𝓘(ℝ, Vector 4 →L[ℝ] Vector N))
        (A := id) contMDiffAt_id (hi x)).continuousAt
    exact h.comp D.continuous.continuousAt
  have he : projection D = fun x ↦ 1 - gramProjection (D x) := funext (projection_eq D hi)
  rw [he]
  exact continuous_const.sub hg

def projectionMap : C(Disk (E := Vector 4), Vector N →L[ℝ] Vector N) :=
  ⟨projection D, continuous_projection D hi⟩

theorem projectionMap_range (x : Disk (E := Vector 4)) :
    (projectionMap D hi x).range = (D x).rangeᗮ :=
  (D x).rangeᗮ.range_starProjection

theorem projectionMap_idempotent (x : Disk (E := Vector 4)) :
    IsIdempotentElem (projectionMap D hi x) := (D x).rangeᗮ.isIdempotentElem_starProjection

theorem finrank_normal (x : Disk (E := Vector 4)) :
    4 + Module.finrank ℝ (projectionMap D hi x).range = N := by
  rw [projectionMap_range]
  have h := (D x).range.finrank_add_finrank_orthogonal
  rw [LinearMap.finrank_range_of_inj (hi x), finrank_euclideanSpace_fin,
    finrank_euclideanSpace_fin] at h
  exact h

end NoExoticSixSphere.Stiefel.DiskNormal
