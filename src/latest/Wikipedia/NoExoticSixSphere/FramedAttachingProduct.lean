import Wikipedia.NoExoticSixSphere.CurvedDiskCollar
import Wikipedia.NoExoticSixSphere.PrescribedCollarNormalFrame

/-!
# Actual framed attaching-product data in the original manifold

These data retain an embedded product in one higher dimension, the original-atlas
attaching tube, interior avoidance, and exact agreement of both map and full
normal frame on a whole collar. The disk is an actual constructed spanning
disk. This structure does not define an attached surgery trace or round its
remaining corners; its existence is proved separately for the candidate.
-/

noncomputable section

open Function Set Metric Topology
open scoped Manifold ContDiff
open Wikipedia.SmoothSixDPoincare.SphereBoundary

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization Stiefel StabilizedSpanningDisk

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector n) M]

structure FramedAttachingProduct (e : EuclideanEmbedding n M)
    (a : SmoothRangeFrame (𝓡 n) e.normalProjection e.NormalModel) (f : Sphere 3 → M) where
  disk : DiskData (pole 3) (e.toFun ∘ f)
  map : Vector 4 × Vector (n - 3) → Vector (e.ambientDimension + 6)
  map_core : ∀ x : Vector 4, map (x, 0) = disk.toFun x
  innerRadius : ℝ
  innerRadius_pos : 0 < innerRadius
  innerRadius_lt_one : innerRadius < 1
  radius : ℝ
  radius_pos : 0 < radius
  embedded : IsClosedEmbedding
    (fun p : closedBall (0 : Vector 4) 1 × closedBall (0 : Vector (n - 3)) radius ↦
      map (p.1.val, p.2.val))
  smooth : ∀ x ∈ closedBall (0 : Vector 4) 1, ∀ v ∈ closedBall (0 : Vector (n - 3)) radius,
    ContDiffAt ℝ ∞ map (x, v)
  immersive : ∀ x ∈ closedBall (0 : Vector 4) 1, ∀ v ∈ closedBall (0 : Vector (n - 3)) radius,
    Injective (fderiv ℝ map (x, v))
  tube : Sphere 3 × Vector (n - 3) → M
  tube_core : ∀ s : Sphere 3, tube (s, 0) = f s
  tube_embedded : IsClosedEmbedding
    (fun p : Sphere 3 × closedBall (0 : Vector (n - 3)) radius ↦ tube (p.1, p.2.val))
  tube_localDiffeomorph : ∀ s : Sphere 3, ∀ v ∈ closedBall (0 : Vector (n - 3)) radius,
    IsLocalDiffeomorphAt ((𝓡 3).prod (𝓡 (n - 3))) (𝓡 n) ∞ tube (s, v)
  collar_map : ∀ x ∈ closedBall (0 : Vector 4) 1, innerRadius ≤ ‖x‖ →
    ∀ v ∈ closedBall (0 : Vector (n - 3)) radius,
      map (x, v) = coordinates e.ambientDimension 4
        ((e.toFun (tube (SphereRadialRetraction.retract (pole 3) x, v)), definingFunction x), 0)
  interior_avoids : ∀ x ∈ ball (0 : Vector 4) 1, ∀ v ∈ closedBall (0 : Vector (n - 3)) radius,
    map (x, v) ∉ range (appendZeroMap e.ambientDimension 6)
  normalFrame : Vector 4 × Vector (n - 3) → Vector ((e.ambientDimension - n) + 5) →L[ℝ]
    Vector (e.ambientDimension + 6)
  normalFrame_smooth : ∀ x ∈ closedBall (0 : Vector 4) 1,
    ∀ v ∈ closedBall (0 : Vector (n - 3)) radius, ContDiffAt ℝ ∞ normalFrame (x, v)
  normalFrame_norm : ∀ x ∈ closedBall (0 : Vector 4) 1,
    ∀ v ∈ closedBall (0 : Vector (n - 3)) radius, ∀ w, ‖normalFrame (x, v) w‖ = ‖w‖
  normalFrame_range : ∀ x ∈ closedBall (0 : Vector 4) 1,
    ∀ v ∈ closedBall (0 : Vector (n - 3)) radius,
      (normalFrame (x, v)).range = (fderiv ℝ map (x, v)).rangeᗮ
  collar_frame : ∀ x ∈ closedBall (0 : Vector 4) 1, innerRadius ≤ ‖x‖ →
    ∀ v ∈ closedBall (0 : Vector (n - 3)) radius,
      normalFrame (x, v) = boundaryFrameOperator
        (a.orthonormal (tube (SphereRadialRetraction.retract (pole 3) x, v))).val

namespace FramedAttachingProduct

variable {e : EuclideanEmbedding n M}
  {a : SmoothRangeFrame (𝓡 n) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f)

theorem map_boundary (s : Sphere 3) (v : Vector (n - 3)) (hv : v ∈ closedBall 0 A.radius) :
    A.map (s.val, v) = appendZeroMap e.ambientDimension 6 (e.toFun (A.tube (s, v))) := by
  have hs : A.innerRadius ≤ ‖s.val‖ := by
    rw [ClosedHemisphere.unit_norm]
    exact A.innerRadius_lt_one.le
  rw [A.collar_map s.val (sphere_subset_closedBall s.property) hs v hv,
    SphereRadialRetraction.retract_coe,
    (definingFunction_eq_zero_iff s.val).mpr s.property, coordinates_old]

theorem normalFrame_boundary (s : Sphere 3) (v : Vector (n - 3))
    (hv : v ∈ closedBall 0 A.radius) : A.normalFrame (s.val, v) =
      boundaryFrameOperator (a.orthonormal (A.tube (s, v))).val := by
  have hs : A.innerRadius ≤ ‖s.val‖ := by
    rw [ClosedHemisphere.unit_norm]
    exact A.innerRadius_lt_one.le
  rw [A.collar_frame s.val (sphere_subset_closedBall s.property) hs v hv,
    SphereRadialRetraction.retract_coe]

end FramedAttachingProduct

end NoExoticSixSphere.EuclideanEmbedding
