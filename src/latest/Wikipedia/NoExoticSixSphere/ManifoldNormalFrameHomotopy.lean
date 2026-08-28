import Wikipedia.NoExoticSixSphere.ManifoldRawSphereFrame
import Wikipedia.NoExoticSixSphere.SmoothRangeFrameOfOperator

/-!+# Normal-frame homotopies preserve the original sphere parity

A continuous family of injective normal operators gives a homotopy of
the actual combined normal-and-tangent operators. The tangent columns
stay fixed. The common sphere-dependent source twist is retained, so
extension equivalence proves equality of the original geometric parity.
No nullhomotopy of the normal framing or of the source twist is assumed.
-/

noncomputable section

open Function unitInterval
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization Stiefel SpanningDiskFrameCoordinates DiskBoundary

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  (e : EuclideanEmbedding 6 M)
  (a b : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel)
  (A : C(I × M, e.NormalModel →L[ℝ] Vector e.ambientDimension))
  (hiA : ∀ p, Injective (A p))
  (hrA : ∀ p, (A p).range ≤ (e.normalProjection p.2).range)
  (hzero : ∀ x, A (0, x) = a.ambient x)
  (hone : ∀ x, A (1, x) = b.ambient x)

include hiA hrA hzero hone

theorem rawSphereFrameOperatorMap_homotopic_of_normal_family
    (f : Sphere 3 → M) (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f)
    (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) f s)) :
    (e.rawSphereFrameOperatorMap a f hf hd).Homotopic
      (e.rawSphereFrameOperatorMap b f hf hd) := by
  have hr (p : I × Sphere 3) : (A (p.1, f p.2)).range ≤ (a.ambient (f p.2)).range := by
    rw [a.ambient_range_eq]
    exact hrA (p.1, f p.2)
  refine ⟨{
    toFun := fun p ↦ ⟨OperatorSum.operator (A (p.1, f p.2))
      (SphereThreeTangentFrame.framedDerivative (e.toFun ∘ f) p.2),
        OperatorSum.injective_operator _ _ (hiA (p.1, f p.2))
          (e.injective_sphereTangentOperator f hf hd p.2)
          ((e.rawSphereNormal_range_disjoint a f hf p.2).mono_left (hr p))⟩
    continuous_toFun := ?_
    map_zero_left := ?_
    map_one_left := ?_ }⟩
  · exact (OperatorSum.continuous_operator _ _
      (A.continuous.comp (continuous_fst.prodMk (hf.continuous.comp continuous_snd)))
      ((e.continuous_sphereTangentOperator f hf).comp continuous_snd)).subtype_mk _
  · intro s
    apply Subtype.ext
    change OperatorSum.operator (A (0, f s))
      (SphereThreeTangentFrame.framedDerivative (e.toFun ∘ f) s) = _
    rw [hzero]
    rfl
  · intro s
    apply Subtype.ext
    change OperatorSum.operator (A (1, f s))
      (SphereThreeTangentFrame.framedDerivative (e.toFun ∘ f) s) = _
    rw [hone]
    rfl

theorem sphereParity_eq_of_normal_family
    (f : Sphere 3 → M) (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f) (hi : Injective f)
    (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) f s)) :
    e.sphereParity a f hf hi hd = e.sphereParity b f hf hi hd := by
  apply zmodTwo_eq_of_zero_iff
  rw [e.sphereParity_zero_iff_raw_twisted_extension a f hf hd hi,
    e.sphereParity_zero_iff_raw_twisted_extension b f hf hd hi]
  exact extends_homotopic_iff (twistedBlockMap_homotopic
    (e.rawSphereFrameOperatorMap_homotopic_of_normal_family a b A hiA hrA hzero hone f hf hd))

end NoExoticSixSphere.EuclideanEmbedding
