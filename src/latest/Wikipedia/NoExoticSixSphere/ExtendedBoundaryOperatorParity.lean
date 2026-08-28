import Wikipedia.NoExoticSixSphere.FramedCollaredDiskParity

/-!
# Original sphere parity from an extending boundary operator

The smooth disk need not be an immersion at interior points. It suffices
that its actual combined boundary operator, with the prescribed raw normal
columns, extends through injective operators. The native boundary chain
rule and positive collar height identify the same collar homotopy as
before, giving the original source-twisted sphere obstruction.
-/

noncomputable section

open Function
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization Stiefel DiskBoundary
open SphereThreeTangentFrame CollaredDiskFrame
open Wikipedia.HopfProblem.DegreeCollapse.DiskCylinder

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  (e : EuclideanEmbedding 6 M)
  (a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel)

theorem sphereParity_zero_of_extended_boundary_operator
    (f : Sphere 3 → M) (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f) (hi : Injective f)
    (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) f s))
    (F : Vector 4 → Vector e.ambientDimension × ℝ)
    (hF : ∀ x ∈ Metric.closedBall (0 : Vector 4) 1, ContDiffAt ℝ ∞ F x)
    (hb : ∀ s : Sphere 3, F s.val = (e.toFun (f s), 0))
    (G : C(Disk (E := Vector 4),
      Monomorphism.Space (e.ambientDimension + 6) (((e.ambientDimension - 6) + 5) + 4)))
    (hG : ∀ s, (G (boundaryToDisk s)).val =
      combined ((ContinuousLinearMap.inl ℝ (Vector e.ambientDimension) ℝ).comp
        (a.ambient (f s))) (fderiv ℝ F s.val))
    (hheight : ∀ s : Sphere 3, 0 < (fderiv ℝ F s.val s.val).2) :
    e.sphereParity a f hf hi hd = 0 := by
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
  have hExt : Extends (collarMap aS TS v c haS hTS hrS hheight) := by
    refine ⟨G, ?_⟩
    intro s
    apply Subtype.ext
    change (G (boundaryToDisk s)).val =
      combined ((ContinuousLinearMap.inl ℝ (Vector e.ambientDimension) ℝ).comp (aS s))
        (collarDerivative s (TS s) (v s) (c s))
    rw [hG, eq_collarDerivative_of_tangent_radial s (TS s) (fderiv ℝ F s.val) (v s) (c s)
      (boundary_tangent_derivative F hF (e.toFun ∘ f) (e.smooth.comp hf) hb s) rfl]
    rfl
  apply (e.sphereParity_zero_iff_raw_twisted_extension a f hf hd hi).mpr
  rw [← he]
  exact (extends_homotopic_iff ⟨collarHomotopy aS TS v c haS hTS hrS hheight⟩).mp hExt

end NoExoticSixSphere.EuclideanEmbedding
