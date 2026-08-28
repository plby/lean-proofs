import Wikipedia.NoExoticSixSphere.ExtendedBoundaryOperatorParity

/-!
# The original sphere parity is detected by its actual collar boundary operator

The positive radial-height collar homotopy identifies the given combined
boundary operator with the original source-twisted raw sphere frame.
Consequently its disk extendability is equivalent to vanishing of the
original sphere parity. The operator need not come from an immersed disk.
-/

noncomputable section

open Function
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization Stiefel DiskBoundary
open SphereThreeTangentFrame CollaredDiskFrame SpanningDiskFrameCoordinates

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  (e : EuclideanEmbedding 6 M)
  (a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel)

theorem boundaryOperator_homotopic_raw_twisted
    (f : Sphere 3 → M) (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f)
    (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) f s))
    (F : Vector 4 → Vector e.ambientDimension × ℝ)
    (hF : ∀ x ∈ Metric.closedBall (0 : Vector 4) 1, ContDiffAt ℝ ∞ F x)
    (hb : ∀ s : Sphere 3, F s.val = (e.toFun (f s), 0))
    (B : C(Sphere 3,
      Monomorphism.Space (e.ambientDimension + 6) (((e.ambientDimension - 6) + 5) + 4)))
    (hB : ∀ s, (B s).val =
      combined ((ContinuousLinearMap.inl ℝ (Vector e.ambientDimension) ℝ).comp
        (a.ambient (f s))) (fderiv ℝ F s.val))
    (hheight : ∀ s : Sphere 3, 0 < (fderiv ℝ F s.val s.val).2) :
    B.Homotopic (twistedBlockMap (e.rawSphereFrameOperatorMap a f hf hd)) := by
  let aS : C(Sphere 3, e.NormalModel →L[ℝ] Vector e.ambientDimension) :=
    ⟨fun s ↦ a.ambient (f s), a.contMDiff_ambient.continuous.comp hf.continuous⟩
  let TS : C(Sphere 3, Vector 3 →L[ℝ] Vector e.ambientDimension) :=
    ⟨framedDerivative (e.toFun ∘ f), e.continuous_sphereTangentOperator f hf⟩
  let v := (ContinuousMap.fst : C(Vector e.ambientDimension × ℝ, _)).comp
    (radialDerivativeMap F hF)
  let c := (ContinuousMap.snd : C(Vector e.ambientDimension × ℝ, ℝ)).comp
    (radialDerivativeMap F hF)
  have haS : ∀ s, Injective (aS s) := fun s ↦ a.ambient_injective (f s)
  have hTS : ∀ s, Injective (TS s) := e.injective_sphereTangentOperator f hf hd
  have hrS : ∀ s, Disjoint (aS s).range (TS s).range :=
    e.rawSphereNormal_range_disjoint a f hf
  have he : sphereOperatorMap aS TS haS hTS hrS = e.rawSphereFrameOperatorMap a f hf hd := by
    apply ContinuousMap.ext
    intro s
    apply Subtype.ext
    rfl
  have hBC : B = collarMap aS TS v c haS hTS hrS hheight := by
    apply ContinuousMap.ext
    intro s
    apply Subtype.ext
    change (B s).val =
      combined ((ContinuousLinearMap.inl ℝ (Vector e.ambientDimension) ℝ).comp (aS s))
        (collarDerivative s (TS s) (v s) (c s))
    rw [hB, eq_collarDerivative_of_tangent_radial s (TS s) (fderiv ℝ F s.val) (v s) (c s)
      (boundary_tangent_derivative F hF (e.toFun ∘ f) (e.smooth.comp hf) hb s) rfl]
    rfl
  rw [hBC, ← he]
  exact ⟨collarHomotopy aS TS v c haS hTS hrS hheight⟩

theorem sphereParity_zero_iff_boundaryOperator_extends
    (f : Sphere 3 → M) (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f) (hi : Injective f)
    (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) f s))
    (F : Vector 4 → Vector e.ambientDimension × ℝ)
    (hF : ∀ x ∈ Metric.closedBall (0 : Vector 4) 1, ContDiffAt ℝ ∞ F x)
    (hb : ∀ s : Sphere 3, F s.val = (e.toFun (f s), 0))
    (B : C(Sphere 3,
      Monomorphism.Space (e.ambientDimension + 6) (((e.ambientDimension - 6) + 5) + 4)))
    (hB : ∀ s, (B s).val =
      combined ((ContinuousLinearMap.inl ℝ (Vector e.ambientDimension) ℝ).comp
        (a.ambient (f s))) (fderiv ℝ F s.val))
    (hheight : ∀ s : Sphere 3, 0 < (fderiv ℝ F s.val s.val).2) :
    e.sphereParity a f hf hi hd = 0 ↔ Extends B :=
  (e.sphereParity_zero_iff_raw_twisted_extension a f hf hd hi).trans
    (extends_homotopic_iff
      (e.boundaryOperator_homotopic_raw_twisted a f hf hd F hF hb B hB hheight)).symm

end NoExoticSixSphere.EuclideanEmbedding
