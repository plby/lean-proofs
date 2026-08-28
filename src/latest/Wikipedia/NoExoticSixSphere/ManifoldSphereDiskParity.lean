import Wikipedia.NoExoticSixSphere.ManifoldSphereDisk
import Wikipedia.NoExoticSixSphere.SpanningDiskDimension

/-!
# Disk parity from the original six-manifold's normal framing

The actual embedding determines the codimension, and its given smooth normal
frame supplies the boundary columns by smooth Gram--Schmidt and restriction.
For a specified constructed spanning disk, zero parity is exactly smooth
extension of those columns and the five added graph axes.

This is not yet a quadratic function on homology: independence of the disk
and representative remains to be proved.
-/

noncomputable section

open Metric
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization Stiefel StabilizedSpanningDisk

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  (e : EuclideanEmbedding 6 M)
  (a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel)
  (f : Sphere 3 → M) (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f)
  {b : Sphere 3} (D : DiskData b (e.toFun ∘ f))

def sphereDiskParity : ZMod 2 :=
  D.parityOfDimension (Nat.sub_add_cancel (e.dimension_le_ambient (f b))).symm
    (e.smooth.comp hf) (e.normalFrameOnSphere a f)
    (e.contMDiff_normalFrameOnSphere a f hf) (e.normalFrameOnSphere_normal a f hf)

theorem sphereDiskParity_zero_iff_smooth_extension : e.sphereDiskParity a f hf D = 0 ↔
    ∃ T : Vector 4 → Vector ((e.ambientDimension - 6) + 5) →L[ℝ]
        Vector (e.ambientDimension + 6),
      (∀ x ∈ closedBall (0 : Vector 4) 1, ContDiffAt ℝ ∞ T x) ∧
      (∀ x ∈ closedBall (0 : Vector 4) 1, ∀ w, ‖T x w‖ = ‖w‖) ∧
      (∀ x ∈ closedBall (0 : Vector 4) 1, (T x).range ≤ (fderiv ℝ D.toFun x).rangeᗮ) ∧
      ∀ s : Sphere 3, T s.val = boundaryFrameOperator (e.normalFrameOnSphere a f s).val :=
  D.parityOfDimension_zero_iff_smooth_extension
    (Nat.sub_add_cancel (e.dimension_le_ambient (f b))).symm
    (e.smooth.comp hf) (e.normalFrameOnSphere a f)
    (e.contMDiff_normalFrameOnSphere a f hf) (e.normalFrameOnSphere_normal a f hf)

end NoExoticSixSphere.EuclideanEmbedding
