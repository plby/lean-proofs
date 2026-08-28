import Wikipedia.NoExoticSixSphere.LocalSphereCollapse
import Wikipedia.NoExoticSixSphere.SphereEquationChartChange
import Wikipedia.NoExoticSixSphere.StereographicProjectionCoordinates

/-!
# The actual compactified collapse retains its original finite coordinate germ

The supplied smooth representative agrees with the original collapse
near the compactified core. Pulling that agreement through the actual
finite source chart and the actual target projection recovers precisely
the original collapse coordinates. The radial extension fixes the sphere
pointwise, so the same assertion holds for its ambient composition.
-/

noncomputable section

open Filter Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere

theorem sphereProjection_finite (n : ℕ) (v : EuclideanSpace ℝ (Fin n)) :
    sphereProjection n (euclideanOnePointSphere n (v : OnePoint _)) = v := by
  rw [euclideanOnePointSphere_coe]
  exact (sphereProjection n).right_inv (by rw [sphereProjection_target]; trivial)

theorem sphereProjection_sphereZero (n : ℕ) : sphereProjection n (sphereZero n) = 0 :=
  sphereProjection_finite n 0

theorem sphereZero_mem_projection_source (n : ℕ) :
    sphereZero n ∈ (sphereProjectionDiffeomorph n).source := by
  change euclideanOnePointSphere n ((0 : EuclideanSpace ℝ (Fin n)) : OnePoint _) ∈
    (sphereProjection n).source
  rw [euclideanOnePointSphere_coe]
  exact (sphereProjection n).map_target (by rw [sphereProjection_target]; trivial)

namespace EuclideanEmbedding.FramedCollapseData

open GLOrthonormalization

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector n) M]
  {e : EuclideanEmbedding n M}
  {a : SmoothRangeFrame (𝓡 n) e.normalProjection e.NormalModel}
  (d : e.FramedCollapseData a)

theorem centered_sphereMap_finite (v : Vector e.ambientDimension) (hv : v ∈ d.neighborhood) :
    CenteredChartCoordinates.coordinates d.sphereMap
      (sphereProjectionDiffeomorph (e.ambientDimension - n))
      (sphereZero (e.ambientDimension - n))
      (euclideanOnePointSphere e.ambientDimension (v : OnePoint _)) = d.coordinates v := by
  change sphereProjection (e.ambientDimension - n)
    (d.sphereMap (euclideanOnePointSphere e.ambientDimension (v : OnePoint _))) -
      sphereProjection (e.ambientDimension - n) (sphereZero (e.ambientDimension - n)) = _
  rw [d.sphereMap_finite hv, sphereProjection_finite, sphereProjection_sphereZero, sub_zero]

variable (g : C(Sphere e.ambientDimension, Sphere (e.ambientDimension - n))) (x : M)
  (hgerm : (g : Sphere e.ambientDimension → Sphere (e.ambientDimension - n))
    =ᶠ[𝓝 (e.compactifiedEmbedding x)] d.sphereMap)

include hgerm in
theorem centered_smoothRepresentative_finite_germ :
    (fun v : Vector e.ambientDimension ↦ CenteredChartCoordinates.coordinates g
      (sphereProjectionDiffeomorph (e.ambientDimension - n))
      (sphereZero (e.ambientDimension - n))
      (euclideanOnePointSphere e.ambientDimension (v : OnePoint _)))
        =ᶠ[𝓝 (e.toFun x)] d.coordinates := by
  have ht : Tendsto (fun v : Vector e.ambientDimension ↦
      euclideanOnePointSphere e.ambientDimension (v : OnePoint _))
      (𝓝 (e.toFun x)) (𝓝 (e.compactifiedEmbedding x)) :=
    (contMDiff_euclideanOnePointSphere_coe e.ambientDimension).continuous.continuousAt
  filter_upwards [hgerm.comp_tendsto ht,
    d.open_neighborhood.mem_nhds (d.range_subset ⟨x, rfl⟩)] with v hgv hv
  change g (euclideanOnePointSphere e.ambientDimension (v : OnePoint _)) =
    d.sphereMap (euclideanOnePointSphere e.ambientDimension (v : OnePoint _)) at hgv
  change sphereProjection (e.ambientDimension - n)
    (g (euclideanOnePointSphere e.ambientDimension (v : OnePoint _))) -
      sphereProjection (e.ambientDimension - n) (sphereZero (e.ambientDimension - n)) = _
  rw [hgv]
  exact d.centered_sphereMap_finite v hv

include hgerm in
theorem radial_smoothRepresentative_finite_germ (b : Sphere e.ambientDimension) :
    SphereLevelEquations.extend b (CenteredChartCoordinates.coordinates g
      (sphereProjectionDiffeomorph (e.ambientDimension - n))
      (sphereZero (e.ambientDimension - n))) ∘ StereographicEquator.finiteAmbient e.ambientDimension
        =ᶠ[𝓝 (e.toFun x)] d.coordinates := by
  have he : SphereLevelEquations.extend b (CenteredChartCoordinates.coordinates g
      (sphereProjectionDiffeomorph (e.ambientDimension - n))
      (sphereZero (e.ambientDimension - n))) ∘
        StereographicEquator.finiteAmbient e.ambientDimension =
      (fun v : Vector e.ambientDimension ↦ CenteredChartCoordinates.coordinates g
        (sphereProjectionDiffeomorph (e.ambientDimension - n))
        (sphereZero (e.ambientDimension - n))
        (euclideanOnePointSphere e.ambientDimension (v : OnePoint _))) := by
    funext v
    change CenteredChartCoordinates.coordinates g
      (sphereProjectionDiffeomorph (e.ambientDimension - n))
      (sphereZero (e.ambientDimension - n))
      (SphereRadialRetraction.retract b
        (euclideanOnePointSphere e.ambientDimension (v : OnePoint _)).val) = _
    rw [SphereRadialRetraction.retract_coe]
  rw [he]
  exact d.centered_smoothRepresentative_finite_germ g x hgerm

end EuclideanEmbedding.FramedCollapseData
end NoExoticSixSphere
