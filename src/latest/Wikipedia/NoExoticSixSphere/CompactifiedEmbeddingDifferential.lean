import Wikipedia.NoExoticSixSphere.SphereCollapse

/-!
# The compactified Euclidean embedding remains an immersion

The finite part of the compactification is an actual inverse stereographic
chart. Its invertible differential preserves injectivity of the differential
of the given Euclidean embedding.
-/

open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] (e : EuclideanEmbedding n M)

theorem injective_mfderiv_compactifiedEmbedding (x : M) :
    Function.Injective (mfderiv (𝓡 n) (𝓡 e.ambientDimension) e.compactifiedEmbedding x) := by
  let c := (sphereProjectionDiffeomorph e.ambientDimension).symm
  have hx : e.toFun x ∈ c.source := by
    change e.toFun x ∈ (sphereProjection e.ambientDimension).target
    rw [sphereProjection_target]
    trivial
  have hc : IsLocalDiffeomorphAt (𝓡 e.ambientDimension) (𝓡 e.ambientDimension) ∞ c (e.toFun x) :=
    ⟨c, hx, fun _ _ ↦ rfl⟩
  have heq : e.compactifiedEmbedding = c ∘ e.toFun := by
    funext y
    exact euclideanOnePointSphere_coe e.ambientDimension (e.toFun y)
  rw [heq, mfderiv_comp x (hc.mdifferentiableAt (by simp)) (e.smooth.mdifferentiable (by simp) x)]
  exact (hc.mfderivToContinuousLinearEquiv (by simp)).injective.comp (e.injective_mfderiv x)

end NoExoticSixSphere.EuclideanEmbedding
