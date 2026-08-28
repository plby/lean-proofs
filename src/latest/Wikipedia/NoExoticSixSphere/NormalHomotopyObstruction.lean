import Wikipedia.NoExoticSixSphere.ProjectionHomotopyObstruction
import Wikipedia.NoExoticSixSphere.NormalDiskObstruction

/-!
# Normal-disk parity under a continuous family of injective differentials

The original derivative ranges determine the normal projections. Their
continuity follows from the Gram formula, and their ranks follow from
injectivity. Thus the projection-homotopy theorem applies without assuming
a normal trivialization or supplying an abstract plane family.
-/

noncomputable section

open scoped Manifold ContDiff

namespace NoExoticSixSphere.Stiefel.NormalHomotopy

open GLOrthonormalization ProjectionHomotopy
open Wikipedia.HopfProblem.DegreeCollapse.DiskCylinder

theorem continuous_normalProjection {X : Type*} [TopologicalSpace X] {n N : ℕ}
    (D : C(X, Vector n →L[ℝ] Vector N)) (hi : ∀ x, Function.Injective (D x)) :
    Continuous (fun x ↦ (D x).rangeᗮ.starProjection) := by
  have hg : Continuous (fun x ↦ gramProjection (D x)) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    have h : ContinuousAt (gramProjection : (Vector n →L[ℝ] Vector N) →
        (Vector N →L[ℝ] Vector N)) (D x) :=
      (contMDiffAt_gramProjection (I := 𝓘(ℝ, Vector n →L[ℝ] Vector N))
        (A := id) contMDiffAt_id (hi x)).continuousAt
    exact h.comp D.continuous.continuousAt
  have he : (fun x ↦ (D x).rangeᗮ.starProjection) = fun x ↦ 1 - gramProjection (D x) := by
    funext x
    rw [Submodule.starProjection_orthogonal', gramProjection_eq_starProjection _ (hi x)]
  rw [he]
  exact continuous_const.sub hg

def projection {X : Type*} [TopologicalSpace X] {n N : ℕ}
    (D : C(X, Vector n →L[ℝ] Vector N)) (hi : ∀ x, Function.Injective (D x)) :
    C(X, Vector N →L[ℝ] Vector N) :=
  ⟨fun x ↦ (D x).rangeᗮ.starProjection, continuous_normalProjection D hi⟩

theorem parity_endpoints (r : ℕ)
    (D : C(ProjectionCylinder.Base, Vector 4 →L[ℝ] Vector (r + 9)))
    (hi : ∀ q, Function.Injective (D q))
    (a : C(unitInterval × NoExoticSixSphere.Sphere 3, Space (r + 9) (r + 2)))
    (ha : ∀ q, (a q).val.range ≤ (D (q.1, boundaryToDisk q.2)).rangeᗮ) :
    DiskNormal.parity r (slice D 0) (fun x ↦ hi (0, x))
        (slice a 0) (fun s ↦ ha (0, s)) =
      DiskNormal.parity r (slice D 1) (fun x ↦ hi (1, x))
        (slice a 1) (fun s ↦ ha (1, s)) := by
  let P := projection D hi
  have hP (q : ProjectionCylinder.Base) : IsIdempotentElem (P q) :=
    (D q).rangeᗮ.isIdempotentElem_starProjection
  have hr (t : unitInterval) :
      Module.finrank ℝ (P (t, ProjectionDisk.center)).range = 3 + (r + 2) :=
    DiskNormal.obstruction_rank r (slice D t) (fun x ↦ hi (t, x))
  have haP (q : unitInterval × NoExoticSixSphere.Sphere 3) :
      (a q).val.range ≤ (P (q.1, boundaryToDisk q.2)).range := by
    change (a q).val.range ≤ ((D (q.1, boundaryToDisk q.2)).rangeᗮ.starProjection).range
    rw [Submodule.range_starProjection]
    exact ha q
  exact ProjectionHomotopy.parity_endpoints r P hP hr a haP

end NoExoticSixSphere.Stiefel.NormalHomotopy
