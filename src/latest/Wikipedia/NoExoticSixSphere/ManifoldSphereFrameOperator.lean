import Wikipedia.NoExoticSixSphere.ManifoldSphereCombinedOperator
import Wikipedia.NoExoticSixSphere.SpanningDiskSourceTwist
import Wikipedia.NoExoticSixSphere.ManifoldFamilyGlobalFrame

/-!
# The original sphere-frame operator and its geometric parity comparison

The operator depends only on the original sphere map and normal frame, not
on a chosen homotopy or parity-ball system. Its common twisted stabilization
is exactly the combined operator of any compatible spanning disk. Thus a
homotopy of these sphere operators implies equality of geometric sphere parity.
No extension of the sphere-dependent source twist is assumed.
-/

noncomputable section

open Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization Stiefel StabilizedSpanningDisk DiskBoundary
open SpanningDiskFrameCoordinates

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  (e : EuclideanEmbedding 6 M)
  (a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel)
  (f : Sphere 3 → M)

def sphereFrameOperator (s : Sphere 3) :
    Vector ((e.ambientDimension - 6) + 3) →L[ℝ] Vector e.ambientDimension :=
  OperatorSum.operator (e.normalFrameOnSphere a f s).val
    (SphereThreeTangentFrame.framedDerivative (e.toFun ∘ f) s)

theorem sphereFrameOperator_family (g : ℝ → Sphere 3 → M) (t : ℝ) (s : Sphere 3) :
    e.sphereFrameOperator a (g t) s = e.normalSpatialOperator a g (t, s) := rfl

variable (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f)
  (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) f s))

include hf in
theorem contMDiff_sphereFrameOperator :
    ContMDiff (𝓡 3)
      𝓘(ℝ, Vector ((e.ambientDimension - 6) + 3) →L[ℝ] Vector e.ambientDimension) ∞
      (e.sphereFrameOperator a f) := by
  have he : e.sphereFrameOperator a f =
      fun s ↦ e.normalSpatialOperator a (fun _ : ℝ ↦ f) (0, s) :=
    funext (fun s ↦ e.sphereFrameOperator_family a (fun _ : ℝ ↦ f) 0 s)
  rw [he]
  have hg : ContMDiff ((𝓘(ℝ, ℝ)).prod (𝓡 3)) (𝓡 6) ∞
      (uncurry (fun _ : ℝ ↦ f)) := hf.comp contMDiff_snd
  exact (e.contMDiff_normalSpatialOperator a (fun _ ↦ f) hg).comp
    ((contMDiff_const (c := (0 : ℝ))).prodMk contMDiff_id)

include hf hd in
theorem injective_sphereFrameOperator (s : Sphere 3) : Injective (e.sphereFrameOperator a f s) := by
  have hg : ContMDiff ((𝓘(ℝ, ℝ)).prod (𝓡 3)) (𝓡 6) ∞
      (uncurry (fun _ : ℝ ↦ f)) := hf.comp contMDiff_snd
  exact e.injective_normalSpatialOperator a (fun _ ↦ f) hg (0, s) (hd s)

def sphereFrameOperatorMap :
    C(Sphere 3, Monomorphism.Space e.ambientDimension ((e.ambientDimension - 6) + 3)) where
  toFun s := ⟨e.sphereFrameOperator a f s, e.injective_sphereFrameOperator a f hf hd s⟩
  continuous_toFun := (e.contMDiff_sphereFrameOperator a f hf).continuous.subtype_mk _

theorem sphereCombinedMap_eq_twistedBlockMap {b : Sphere 3} (D : DiskData b (e.toFun ∘ f)) :
    e.sphereCombinedMap a f hf D = twistedBlockMap (e.sphereFrameOperatorMap a f hf hd) := by
  apply ContinuousMap.ext
  intro s
  apply Subtype.ext
  rw [e.sphereCombinedMap_value, twistedBlockMap_value]
  exact D.combinedOperator_factorization (e.smooth.comp hf) s (e.normalFrameOnSphere a f s).val

theorem sphereParity_zero_iff_twisted_extension (hi : Injective f) :
    e.sphereParity a f hf hi hd = 0 ↔
      Extends (twistedBlockMap (e.sphereFrameOperatorMap a f hf hd)) := by
  obtain ⟨D⟩ := e.nonempty_sphereDiskData f (pole 3) hf hi hd
  rw [e.sphereParity_zero_iff_combined_extension a f hf D hi hd,
    e.sphereCombinedMap_eq_twistedBlockMap a f hf hd D]

theorem sphereParity_eq_of_frameOperator_homotopic (hi : Injective f)
    (g : Sphere 3 → M) (hg : ContMDiff (𝓡 3) (𝓡 6) ∞ g)
    (hgd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) g s)) (hgi : Injective g)
    (H : (e.sphereFrameOperatorMap a f hf hd).Homotopic
      (e.sphereFrameOperatorMap a g hg hgd)) :
    e.sphereParity a f hf hi hd = e.sphereParity a g hg hgi hgd := by
  apply zmodTwo_eq_of_zero_iff
  rw [e.sphereParity_zero_iff_twisted_extension a f hf hd hi,
    e.sphereParity_zero_iff_twisted_extension a g hg hgd hgi]
  exact extends_homotopic_iff (twistedBlockMap_homotopic H)

end NoExoticSixSphere.EuclideanEmbedding
