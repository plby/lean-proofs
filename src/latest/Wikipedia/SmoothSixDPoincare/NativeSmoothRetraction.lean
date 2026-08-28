import Wikipedia.SmoothSixDPoincare.NativeTubularNeighborhood

/-!
# A smooth neighborhood retraction to the original manifold

The inverse of the constructed Euclidean tubular neighborhood, followed by
normal-bundle projection, retracts an actual open Euclidean neighborhood onto
the original manifold. Its derivative is the inverse of the embedding
derivative on the actual tangent image.
-/

noncomputable section

open Set Bundle Function
open scoped Manifold ContDiff Topology Bundle

namespace Wikipedia.SmoothSixDPoincare.NativeEuclideanEmbedding

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] (e : NativeEuclideanEmbedding E M)

/-- An actual smooth retraction from an open neighborhood of the embedded manifold. -/
structure SmoothRetraction where
  domain : Set (EuclideanSpace ℝ (Fin e.ambientDimension))
  open_domain : IsOpen domain
  contains : range e.toFun ⊆ domain
  toFun : EuclideanSpace ℝ (Fin e.ambientDimension) → M
  smooth : ContMDiffOn (𝓡 e.ambientDimension) 𝓘(ℝ, E) ∞ toFun domain
  retract : ∀ x, toFun (e.toFun x) = x

/-- Compactness constructs the smooth neighborhood retraction, with no retraction assumption. -/
theorem nonempty_smoothRetraction [CompactSpace M] [Nonempty M] :
    Nonempty e.SmoothRetraction := by
  obtain ⟨Φ, hzero, hΦ, hrange⟩ := e.exists_tubularNeighborhood
  refine ⟨⟨Φ.target, Φ.open_target, hrange, fun y => (Φ.symm y).proj,
    (Bundle.contMDiff_proj e.NormalSpace).comp_contMDiffOn Φ.contMDiffOn_invFun, ?_⟩⟩
  intro x
  have hx : zeroSection e.NormalModel e.NormalSpace x ∈ Φ.source := hzero ⟨x, rfl⟩
  have heq : Φ (zeroSection e.NormalModel e.NormalSpace x) = e.toFun x := by
    rw [hΦ, e.normalDisplacement_zero]
  have hinv := Φ.left_inv' hx
  rw [heq] at hinv
  exact congrArg TotalSpace.proj hinv

namespace SmoothRetraction

variable {e} (r : e.SmoothRetraction)

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- Differentiating the exact retraction identity gives the true tangent left inverse. -/
theorem mfderiv_retract_comp (x : M) :
    (mfderiv (𝓡 e.ambientDimension) 𝓘(ℝ, E) r.toFun (e.toFun x)).comp
      (mfderiv 𝓘(ℝ, E) (𝓡 e.ambientDimension) e.toFun x) =
        ContinuousLinearMap.id ℝ (TangentSpace 𝓘(ℝ, E) x) := by
  have hr : r.toFun ∘ e.toFun = id := funext r.retract
  have hd := mfderiv_comp x
    ((r.smooth.contMDiffAt (r.open_domain.mem_nhds (r.contains ⟨x, rfl⟩))).mdifferentiableAt
      (by simp))
    (e.smooth.mdifferentiableAt (by simp))
  rw [hr, mfderiv_id] at hd
  exact hd.symm

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- Embedded differentiation after retraction fixes every actual manifold tangent vector. -/
theorem embedding_derivative_retract {x : M}
    {v : EuclideanSpace ℝ (Fin e.ambientDimension)} (hv : v ∈ e.tangentImage x) :
    (mvfderiv 𝓘(ℝ, E) e.toFun x)
      ((mfderiv (𝓡 e.ambientDimension) 𝓘(ℝ, E) r.toFun (e.toFun x)) v) = v := by
  obtain ⟨w, rfl⟩ := hv
  have h := congrArg (fun A => A w) (r.mfderiv_retract_comp x)
  exact congrArg (mvfderiv 𝓘(ℝ, E) e.toFun x) h

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- The retraction derivative is injective on the embedded tangent image. -/
theorem injOn_derivative_tangentImage (x : M) :
    InjOn (fun v : EuclideanSpace ℝ (Fin e.ambientDimension) =>
      (mfderiv (𝓡 e.ambientDimension) 𝓘(ℝ, E) r.toFun (e.toFun x)) v)
      (e.tangentImage x) := by
  intro v hv w hw h
  exact (r.embedding_derivative_retract hv).symm.trans
    ((congrArg (mvfderiv 𝓘(ℝ, E) e.toFun x) h).trans (r.embedding_derivative_retract hw))

end SmoothRetraction

end Wikipedia.SmoothSixDPoincare.NativeEuclideanEmbedding
