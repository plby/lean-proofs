import Wikipedia.NoExoticSixSphere.ProjectionCylinderFrame
import Wikipedia.NoExoticSixSphere.ProjectionDiskObstruction

/-!
# Projection-disk parity is invariant under actual continuous homotopies

A simultaneous full frame on the parameter–disk cylinder yields a genuine
homotopy of the boundary partial-frame coordinates. Free-homotopy invariance
of the native sphere obstruction then compares the two endpoint parities.
The chosen full frames in the endpoint definitions need not agree.
-/

noncomputable section

namespace NoExoticSixSphere.Stiefel.ProjectionHomotopy

open GLOrthonormalization
open Wikipedia.HopfProblem.DegreeCollapse.DiskCylinder

def slice {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(unitInterval × X, Y)) (t : unitInterval) : C(X, Y) :=
  ⟨fun x ↦ f (t, x), f.continuous.comp (continuous_const.prodMk continuous_id)⟩

def boundary : C(unitInterval × NoExoticSixSphere.Sphere 3, ProjectionCylinder.Base) :=
  ⟨fun q ↦ (q.1, boundaryToDisk q.2),
    continuous_fst.prodMk (boundaryToDisk.continuous.comp continuous_snd)⟩

theorem parity_endpoints {N : ℕ} (r : ℕ)
    (P : C(ProjectionCylinder.Base, Vector N →L[ℝ] Vector N))
    (hP : ∀ q, IsIdempotentElem (P q))
    (hr : ∀ t, Module.finrank ℝ (P (t, ProjectionDisk.center)).range = 3 + (r + 2))
    (a : C(unitInterval × NoExoticSixSphere.Sphere 3, Space N (r + 2)))
    (ha : ∀ q, (a q).val.range ≤ (P (q.1, boundaryToDisk q.2)).range) :
    ProjectionObstruction.parity r (slice P 0) (fun x ↦ hP (0, x)) (hr 0)
        (slice a 0) (fun s ↦ ha (0, s)) =
      ProjectionObstruction.parity r (slice P 1) (fun x ↦ hP (1, x)) (hr 1)
        (slice a 1) (fun s ↦ ha (1, s)) := by
  obtain ⟨T, hT⟩ := ProjectionCylinder.exists_frame P hP (hr 0)
  have hTa (q : unitInterval × NoExoticSixSphere.Sphere 3) :
      (a q).val.range ≤ (T (boundary q)).val.range :=
    (ha q).trans_eq (hT (boundary q)).symm
  let c := RangeCoordinates.map (T.comp boundary) a hTa
  have hpar (t : unitInterval) :
      ProjectionObstruction.parity r (slice P t) (fun x ↦ hP (t, x)) (hr t)
          (slice a t) (fun s ↦ ha (t, s)) = sphereThirdObstruction r (slice c t) := by
    calc
      _ = RangeObstruction.parity r (slice T t) (slice a t) (fun s ↦ hTa (t, s)) :=
        ProjectionObstruction.parity_eq_of_trivialization r (slice P t)
          (fun x ↦ hP (t, x)) (hr t) (slice a t) (fun s ↦ ha (t, s)) (slice T t)
          (fun x ↦ hT (t, x)) (fun s ↦ hTa (t, s))
      _ = _ := rfl
  rw [hpar 0, hpar 1]
  apply sphereThirdObstruction_homotopic
  exact ⟨{ toFun := c
           continuous_toFun := c.continuous
           map_zero_left := fun _ ↦ rfl
           map_one_left := fun _ ↦ rfl }⟩

end NoExoticSixSphere.Stiefel.ProjectionHomotopy
