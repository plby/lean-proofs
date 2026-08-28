import Wikipedia.NoExoticSixSphere.RadialInternalSphereTube
import Wikipedia.NoExoticSixSphere.ManifoldHeightNormalFrame

/-!
# The prescribed original normal frame over the curved collar model

At each radial tube point take the actual original manifold normal frame and
the five graph axes. It is orthonormal, smooth on the genuine collar domain,
and normal to the lifted curved model with its scalar height. Its zero-section
value is exactly the original boundary frame used for the disk extension.
-/

noncomputable section

open Function
open scoped Manifold ContDiff
open Wikipedia.SmoothSixDPoincare.SphereBoundary

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization Stiefel StabilizedSpanningDisk

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  (e : EuclideanEmbedding 6 M)
  (a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel)
  (f : Sphere 3 → M) (C : Sphere 3 → Vector 3 →L[ℝ] Vector e.ambientDimension)
  (R : TubularRetraction e) (b : Sphere 3)

def collarNormalFrame : Vector 4 × Vector 3 →
    Vector ((e.ambientDimension - 6) + 5) →L[ℝ] Vector (e.ambientDimension + 6) :=
  e.stabilizedNormalFrame a (e.radialInternalSphereTube f C R b)

omit a in
def curvedCollarModel : Vector 4 × Vector 3 → Vector (e.ambientDimension + 6) :=
  e.stabilizedHeightMap (e.radialInternalSphereTube f C R b) (fun p ↦ definingFunction p.1)

theorem norm_collarNormalFrame (p : Vector 4 × Vector 3)
    (w : Vector ((e.ambientDimension - 6) + 5)) : ‖e.collarNormalFrame a f C R b p w‖ = ‖w‖ :=
  e.norm_stabilizedNormalFrame a _ p w

theorem collarNormalFrame_core (x : Vector 4) :
    e.collarNormalFrame a f C R b (x, 0) = boundaryFrameOperator
      (e.normalFrameOnSphere a f (SphereRadialRetraction.retract b x)).val := by
  unfold collarNormalFrame stabilizedNormalFrame
  rw [e.radialInternalSphereTube_core]
  rfl

theorem collarNormalFrame_coe (s : Sphere 3) (v : Vector 3) :
    e.collarNormalFrame a f C R b (s.val, v) =
      boundaryFrameOperator (a.orthonormal (e.internalSphereTube f C R (s, v))).val := by
  unfold collarNormalFrame stabilizedNormalFrame
  rw [e.radialInternalSphereTube_coe]

variable (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f)
  (hC : ContMDiff (𝓡 3) 𝓘(ℝ, Vector 3 →L[ℝ] Vector e.ambientDimension) ∞ C)
  {x : Vector 4} (hx : x ≠ 0) (v : Vector 3)
  (hp : (SphereRadialRetraction.retract b x, v) ∈ e.sphereTubeDomain f C R)

include hf hC hx hp in
theorem contDiffAt_collarNormalFrame :
    ContDiffAt ℝ ∞ (e.collarNormalFrame a f C R b) (x, v) :=
  e.contDiffAt_stabilizedNormalFrame a _
    (e.contMDiffAt_radialInternalSphereTube f C R b hf hC hx v hp)

omit a in
include hf hC hx hp in
theorem contDiffAt_curvedCollarModel :
    ContDiffAt ℝ ∞ (e.curvedCollarModel f C R b) (x, v) :=
  e.contDiffAt_stabilizedHeightMap _ _
    (e.contMDiffAt_radialInternalSphereTube f C R b hf hC hx v hp)
    (contDiff_definingFunction.contDiffAt.comp (x, v) contDiffAt_fst)

include hf hC hx hp in
theorem collarNormalFrame_normal_model :
    (e.collarNormalFrame a f C R b (x, v)).range ≤
      (fderiv ℝ (e.curvedCollarModel f C R b) (x, v)).rangeᗮ :=
  e.stabilizedNormalFrame_normal a _ _
    (e.contMDiffAt_radialInternalSphereTube f C R b hf hC hx v hp)
    (contDiff_definingFunction.contDiffAt.comp (x, v) contDiffAt_fst)

end NoExoticSixSphere.EuclideanEmbedding
