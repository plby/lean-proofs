import Wikipedia.NoExoticSixSphere.FramedDiskThickening
import Wikipedia.NoExoticSixSphere.EuclideanBlockProjection

/-!
# The original-coordinate part of the actual boundary transverse frame

Restrict the constructed transverse frame to the boundary sphere and project
to the old ambient coordinates. Smoothness follows from the original sphere
inclusion and the actual disk-frame smoothness. Its tangency and full-range
properties are established separately using the prescribed boundary data.
-/

noncomputable section

open scoped Manifold ContDiff

namespace NoExoticSixSphere.DiskThickening.FramedProduct

open GLOrthonormalization

variable {N k q : ℕ} {D : Vector 4 → Vector (N + 6)}
  {T : Vector 4 → Vector k →L[ℝ] Vector (N + 6)} (A : FramedProduct D T q)

def boundaryTransverse (s : Sphere 3) : Vector q →L[ℝ] Vector N :=
  (oldProjection N 6).comp (A.transverse s.val)

theorem contMDiff_transverse_boundary :
    ContMDiff (𝓡 3) 𝓘(ℝ, Vector q →L[ℝ] Vector (N + 6)) ∞
      (fun s : Sphere 3 ↦ A.transverse s.val) := by
  let : Fact (Module.finrank ℝ (Vector 4) = 3 + 1) := ⟨finrank_euclideanSpace_fin⟩
  have hs : ContMDiff (𝓡 3) (𝓡 4) ∞ (fun s : Sphere 3 ↦ s.val) := contMDiff_coe_sphere
  intro s
  exact (A.smooth_transverse s.val (Metric.sphere_subset_closedBall s.property)).contMDiffAt.comp
    s hs.contMDiffAt

theorem contMDiff_boundaryTransverse :
    ContMDiff (𝓡 3) 𝓘(ℝ, Vector q →L[ℝ] Vector N) ∞ A.boundaryTransverse := by
  let : Fact (Module.finrank ℝ (Vector 4) = 3 + 1) := ⟨finrank_euclideanSpace_fin⟩
  have hs : ContMDiff (𝓡 3) (𝓡 4) ∞ (fun s : Sphere 3 ↦ s.val) := contMDiff_coe_sphere
  intro s
  exact contMDiffAt_const.clm_comp
    ((A.smooth_transverse s.val (Metric.sphere_subset_closedBall s.property)).contMDiffAt.comp
      s hs.contMDiffAt)

end NoExoticSixSphere.DiskThickening.FramedProduct
