import Wikipedia.NoExoticSixSphere.CompactRadialSphereTube
import Wikipedia.NoExoticSixSphere.ManifoldHeightNormalFrame

/-!
# The prescribed original normal frame over the curved collar model

At each radial tube point take the actual original manifold normal frame and
the five graph axes. It is orthonormal, smooth on the genuine collar domain,
and normal to the lifted curved model with its scalar height. Its zero-section
value is exactly the original boundary frame used for the disk extension.
-/

noncomputable section

open Function Set
open scoped Manifold ContDiff
open Wikipedia.SmoothSixDPoincare.SphereBoundary

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization Stiefel StabilizedSpanningDisk

variable {n d : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector n) M]
  (e : EuclideanEmbedding n M)
  (a : SmoothRangeFrame (𝓡 n) e.normalProjection e.NormalModel)
  (f : Sphere 3 → M) (C : Sphere 3 → Vector d →L[ℝ] Vector e.ambientDimension)
  (R : e.RetractionNear (range f)) (b : Sphere 3)

def compactCollarNormalFrame : Vector 4 × Vector d →
    Vector ((e.ambientDimension - n) + 5) →L[ℝ] Vector (e.ambientDimension + 6) :=
  e.stabilizedNormalFrame a (e.radialCompactSphereTube f C R b)

omit a in
def compactCurvedCollarModel : Vector 4 × Vector d → Vector (e.ambientDimension + 6) :=
  e.stabilizedHeightMap (e.radialCompactSphereTube f C R b) (fun p ↦ definingFunction p.1)

theorem norm_compactCollarNormalFrame (p : Vector 4 × Vector d)
    (w : Vector ((e.ambientDimension - n) + 5)) :
    ‖e.compactCollarNormalFrame a f C R b p w‖ = ‖w‖ :=
  e.norm_stabilizedNormalFrame a _ p w

theorem compactCollarNormalFrame_core (x : Vector 4) :
    e.compactCollarNormalFrame a f C R b (x, 0) = boundaryFrameOperator
      (a.orthonormal (f (SphereRadialRetraction.retract b x))).val := by
  unfold compactCollarNormalFrame stabilizedNormalFrame
  rw [e.radialCompactSphereTube_core]

theorem compactCollarNormalFrame_coe (s : Sphere 3) (v : Vector d) :
    e.compactCollarNormalFrame a f C R b (s.val, v) =
      boundaryFrameOperator (a.orthonormal (e.compactSphereTube f C R (s, v))).val := by
  unfold compactCollarNormalFrame stabilizedNormalFrame
  rw [e.radialCompactSphereTube_coe]

variable (hf : ContMDiff (𝓡 3) (𝓡 n) ∞ f)
  (hC : ContMDiff (𝓡 3) 𝓘(ℝ, Vector d →L[ℝ] Vector e.ambientDimension) ∞ C)
  {x : Vector 4} (hx : x ≠ 0) (v : Vector d)
  (hp : (SphereRadialRetraction.retract b x, v) ∈ e.compactSphereTubeDomain f C R)

include hf hC hx hp in
theorem contDiffAt_compactCollarNormalFrame :
    ContDiffAt ℝ ∞ (e.compactCollarNormalFrame a f C R b) (x, v) :=
  e.contDiffAt_stabilizedNormalFrame a _
    (e.contMDiffAt_radialCompactSphereTube f C R b hf hC hx v hp)

omit a in
include hf hC hx hp in
theorem contDiffAt_compactCurvedCollarModel :
    ContDiffAt ℝ ∞ (e.compactCurvedCollarModel f C R b) (x, v) :=
  e.contDiffAt_stabilizedHeightMap _ _
    (e.contMDiffAt_radialCompactSphereTube f C R b hf hC hx v hp)
    (contDiff_definingFunction.contDiffAt.comp (x, v) contDiffAt_fst)

include hf hC hx hp in
theorem compactCollarNormalFrame_normal_model :
    (e.compactCollarNormalFrame a f C R b (x, v)).range ≤
      (fderiv ℝ (e.compactCurvedCollarModel f C R b) (x, v)).rangeᗮ :=
  e.stabilizedNormalFrame_normal a _ _
    (e.contMDiffAt_radialCompactSphereTube f C R b hf hC hx v hp)
    (contDiff_definingFunction.contDiffAt.comp (x, v) contDiffAt_fst)

end NoExoticSixSphere.EuclideanEmbedding
