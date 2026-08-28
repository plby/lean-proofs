import Wikipedia.NoExoticSixSphere.ManifoldFourDiskOperator
import Wikipedia.NoExoticSixSphere.ManifoldFrameBlockCoordinates

/-!
# Exact chart factorization of the original four-disk operator

The derivative in an original target chart is factored using equality of
germs, not a new smooth structure. The source is already Euclidean, so no
derivative of a singularity-ball parametrization enters this identity.
The factorization remains valid at singular points.
-/

noncomputable section

open Set Function Filter Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization FrameBlockCoordinates

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  (e : EuclideanEmbedding 7 M)
  (g : Vector 4 → M) (x : Vector 4)
  (hg : MDifferentiableAt (𝓡 4) (𝓡 7) g x)
  (c : PartialDiffeomorph (𝓡 7) (𝓡 7) M (Vector 7) ∞) (hc : g x ∈ c.source)

include hg

theorem fourDiskDerivative_in_chart :
    e.fourDiskDerivative g x =
      (e.chartEmbeddingDerivative c ⟨g x, hc⟩).comp (fderiv ℝ (c ∘ g) x) := by
  let F : Vector 4 → Vector 7 := c ∘ g
  let H : Vector 7 → Vector e.ambientDimension := e.toFun ∘ c.symm
  have hF : DifferentiableAt ℝ F x :=
    (((c.contMDiffOn_toFun.contMDiffAt
      (c.open_source.mem_nhds hc)).mdifferentiableAt (by simp)).comp x hg).differentiableAt
  have hH : DifferentiableAt ℝ H (F x) :=
    (e.smooth.contMDiffAt.comp _ (c.contMDiffOn_invFun.contMDiffAt
      (c.open_target.mem_nhds (c.map_source hc)))).contDiffAt.differentiableAt (by simp)
  have hNc : ∀ᶠ z in 𝓝 x, g z ∈ c.source :=
    hg.continuousAt.preimage_mem_nhds (c.open_source.mem_nhds hc)
  have he : e.toFun ∘ g =ᶠ[𝓝 x] H ∘ F := by
    filter_upwards [hNc] with z hz
    exact congrArg e.toFun (c.left_inv hz).symm
  rw [fourDiskDerivative, he.fderiv_eq, fderiv_comp x hH hF]
  rfl

theorem normalFourDiskOperator_in_chart
    (a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel) :
    e.normalFourDiskOperator a g x =
      (e.normalChartCoordinates a c ⟨g x, hc⟩).toContinuousLinearMap.comp
        (identityBlockOperator (e.ambientDimension - 7) (fderiv ℝ (c ∘ g) x)) := by
  apply ContinuousLinearMap.ext
  intro v
  change OperatorSum.operator (e.fourDiskNormalOperator a g x) (e.fourDiskDerivative g x) v =
    e.normalChartOperator a c ⟨g x, hc⟩
      (identityBlockOperator (e.ambientDimension - 7) (fderiv ℝ (c ∘ g) x) v)
  rw [OperatorSum.operator_apply, e.fourDiskDerivative_in_chart g x hg c hc,
    identityBlockOperator_apply, e.normalChartOperator_apply,
    ContinuousLinearEquiv.apply_symm_apply]
  rfl

end NoExoticSixSphere.EuclideanEmbedding
