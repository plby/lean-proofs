import Wikipedia.NoExoticSixSphere.ManifoldSphereFrameOperator
import Wikipedia.NoExoticSixSphere.NormalColumnNormalization

/-!
# Computing sphere parity with the original, unnormalized normal frame

Only the normal columns are normalized. Their interpolation has the same
normal range bound, so the original tangent columns remain independent.
The resulting homotopy also transports the sphere-dependent source twist;
no extension or numerical invariance of that twist is assumed.
-/

noncomputable section

open Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization Stiefel SpanningDiskFrameCoordinates DiskBoundary

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  (e : EuclideanEmbedding 6 M)
  (a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel)
  (f : Sphere 3 → M) (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f)

include hf

omit a in
theorem continuous_sphereTangentOperator :
    Continuous (SphereThreeTangentFrame.framedDerivative (e.toFun ∘ f)) := by
  have hg : ContMDiff ((𝓘(ℝ, ℝ)).prod (𝓡 3)) (𝓡 6) ∞
      (uncurry (fun _ : ℝ ↦ f)) := hf.comp contMDiff_snd
  exact (e.contMDiff_familyTangentOperator (fun _ ↦ f) hg).continuous.comp
    ((continuous_const (y := (0 : ℝ))).prodMk continuous_id)

theorem rawSphereNormal_range_disjoint (s : Sphere 3) :
    Disjoint (a.ambient (f s)).range
      (SphereThreeTangentFrame.framedDerivative (e.toFun ∘ f) s).range := by
  have he : (a.ambient (f s)).range = (e.normalFrameOnSphere a f s).val.range :=
    (a.ambient_range (f s)).trans (a.orthonormal_range (f s)).symm
  let B := SphereThreeTangentFrame.framedDerivative (e.toFun ∘ f) s
  have hn : (a.ambient (f s)).range ≤ B.rangeᗮ := by
    rw [he, SphereThreeTangentFrame.range_framedDerivative _ (e.smooth.comp hf)]
    exact e.normalFrameOnSphere_normal a f hf s
  exact B.range.orthogonal_disjoint.symm.mono_left hn

omit a in
theorem injective_sphereTangentOperator
    (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) f s)) (s : Sphere 3) :
    Injective (SphereThreeTangentFrame.framedDerivative (e.toFun ∘ f) s) := by
  apply SphereThreeTangentFrame.injective_framedDerivative _ (e.smooth.comp hf)
  rw [mfderiv_comp s (e.smooth.mdifferentiableAt (by simp))
    (hf.mdifferentiableAt (by simp))]
  exact (e.injective_mfderiv (f s)).comp (hd s)

omit hf in
def rawSphereFrameOperator (s : Sphere 3) :
    Vector ((e.ambientDimension - 6) + 3) →L[ℝ] Vector e.ambientDimension :=
  OperatorSum.operator (a.ambient (f s))
    (SphereThreeTangentFrame.framedDerivative (e.toFun ∘ f) s)

variable (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) f s))

def rawSphereFrameOperatorMap :
    C(Sphere 3, Monomorphism.Space e.ambientDimension ((e.ambientDimension - 6) + 3)) where
  toFun s := ⟨e.rawSphereFrameOperator a f s,
    OperatorSum.injective_operator _ _ (a.ambient_injective (f s))
      (e.injective_sphereTangentOperator f hf hd s) (e.rawSphereNormal_range_disjoint a f hf s)⟩
  continuous_toFun := (OperatorSum.continuous_operator _ _
    (a.contMDiff_ambient.continuous.comp hf.continuous)
    (e.continuous_sphereTangentOperator f hf)).subtype_mk _

theorem rawSphereFrameOperatorMap_homotopic :
    (e.rawSphereFrameOperatorMap a f hf hd).Homotopic
      (e.sphereFrameOperatorMap a f hf hd) :=
  OperatorSum.homotopic_normalize_left (fun s ↦ a.ambient (f s))
    (SphereThreeTangentFrame.framedDerivative (e.toFun ∘ f))
    (a.contMDiff_ambient.continuous.comp hf.continuous)
    (e.continuous_sphereTangentOperator f hf) (fun s ↦ a.ambient_injective (f s))
    (e.injective_sphereTangentOperator f hf hd) (e.rawSphereNormal_range_disjoint a f hf)
    (e.rawSphereFrameOperatorMap a f hf hd) (e.sphereFrameOperatorMap a f hf hd)
    (fun _ ↦ rfl) (fun _ ↦ rfl)

theorem rawSphereFrameOperatorMap_twisted_homotopic :
    (twistedBlockMap (e.rawSphereFrameOperatorMap a f hf hd)).Homotopic
      (twistedBlockMap (e.sphereFrameOperatorMap a f hf hd)) :=
  twistedBlockMap_homotopic (e.rawSphereFrameOperatorMap_homotopic a f hf hd)

theorem sphereParity_zero_iff_raw_twisted_extension (hi : Injective f) :
    e.sphereParity a f hf hi hd = 0 ↔
      Extends (twistedBlockMap (e.rawSphereFrameOperatorMap a f hf hd)) := by
  rw [e.sphereParity_zero_iff_twisted_extension a f hf hd hi]
  exact (extends_homotopic_iff
    (e.rawSphereFrameOperatorMap_twisted_homotopic a f hf hd)).symm

end NoExoticSixSphere.EuclideanEmbedding
