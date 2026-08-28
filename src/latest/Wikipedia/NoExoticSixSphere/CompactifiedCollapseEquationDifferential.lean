import Wikipedia.NoExoticSixSphere.CompactifiedCollapseCoordinateGerm
import Wikipedia.NoExoticSixSphere.StereographicEquationDifferential

/-!
# The actual compactified collapse has the prescribed full block derivative

The original collapse germ, not just its zero set, identifies the finite
target derivative. The actual augmented stereographic differential then
gives the full sphere-level equation derivative, including the new radial
equation. The original Euclidean collapse derivative is retained exactly.
-/

noncomputable section

open Filter Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding.FramedCollapseData

open GLOrthonormalization StereographicEquator

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector n) M]
  {e : EuclideanEmbedding n M}
  {a : SmoothRangeFrame (𝓡 n) e.normalProjection e.NormalModel}
  (d : e.FramedCollapseData a)
  (g : C(Sphere e.ambientDimension, Sphere (e.ambientDimension - n)))
  (hg : ContMDiff (𝓡 e.ambientDimension) (𝓡 (e.ambientDimension - n)) ∞ g)
  (x : M)
  (hgerm : (g : Sphere e.ambientDimension → Sphere (e.ambientDimension - n))
    =ᶠ[𝓝 (e.compactifiedEmbedding x)] d.sphereMap)

include hgerm in
theorem smoothRepresentative_core :
    g (e.compactifiedEmbedding x) = sphereZero (e.ambientDimension - n) := by
  rw [hgerm.self_of_nhds]
  exact (d.sphereMap_zero_iff _).mpr ⟨x, rfl⟩

include hg hgerm in
theorem contMDiffAt_centered_smoothRepresentative :
    ContMDiffAt (𝓡 e.ambientDimension) 𝓘(ℝ, e.NormalModel) ∞
      (CenteredChartCoordinates.coordinates g
        (sphereProjectionDiffeomorph (e.ambientDimension - n))
        (sphereZero (e.ambientDimension - n))) (e.compactifiedEmbedding x) := by
  apply CenteredChartCoordinates.contMDiffAt_coordinates _ _ _ (hg _)
  rw [d.smoothRepresentative_core g x hgerm]
  exact sphereZero_mem_projection_source _

local instance : Fact (Module.finrank ℝ (Vector (e.ambientDimension + 1)) =
    e.ambientDimension + 1) := ⟨finrank_euclideanSpace_fin⟩

include hg hgerm in
theorem fderiv_radial_smoothRepresentative_comp (b : Sphere e.ambientDimension) :
    (fderiv ℝ (SphereLevelEquations.extend b (CenteredChartCoordinates.coordinates g
      (sphereProjectionDiffeomorph (e.ambientDimension - n))
      (sphereZero (e.ambientDimension - n))))
      (finiteAmbient e.ambientDimension (e.toFun x))).comp
        (fderiv ℝ (finiteAmbient e.ambientDimension) (e.toFun x)) =
          fderiv ℝ d.coordinates (e.toFun x) := by
  have hd := (d.radial_smoothRepresentative_finite_germ g x hgerm b).fderiv_eq (𝕜 := ℝ)
  have hr := (SphereLevelEquations.contDiffAt_extend b
    (d.contMDiffAt_centered_smoothRepresentative g hg x hgerm)).differentiableAt (by simp)
  have hc := fderiv_comp (e.toFun x) hr
    ((contDiff_finiteAmbient e.ambientDimension).differentiable (by simp) (e.toFun x))
  exact hc.symm.trans hd

include hg hgerm in
theorem fderiv_compactified_equations (b : Sphere e.ambientDimension)
    (w : Vector e.ambientDimension) (t : ℝ) :
    fderiv ℝ (SphereFiberNormalFrame.equationsWithTargetChart g
      (sphereZero (e.ambientDimension - n))
      (sphereProjectionDiffeomorph (e.ambientDimension - n)) b)
      (e.compactifiedEmbedding x).val
        (augmentedEquiv e.ambientDimension (e.toFun x) (w, t)) =
      WithLp.toLp 2 (2 * t, fderiv ℝ d.coordinates (e.toFun x) w) :=
  fderiv_equations_augmented b _ (e.toFun x)
    (d.contMDiffAt_centered_smoothRepresentative g hg x hgerm) _
    (d.fderiv_radial_smoothRepresentative_comp g hg x hgerm b) w t

end NoExoticSixSphere.EuclideanEmbedding.FramedCollapseData
