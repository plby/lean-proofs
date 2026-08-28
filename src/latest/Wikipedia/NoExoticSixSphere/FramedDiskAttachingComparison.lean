import Wikipedia.NoExoticSixSphere.ManifoldSphereTransverseFrame
import Wikipedia.NoExoticSixSphere.InternalSphereTube

/-!
# Exact affine attaching-face comparison for the constructed disk product

The product face on `S³ × ℝ³` is exactly the stabilization of the original
ambient affine tube. Retracting that tube into the manifold gives the original
manifold neighborhood; its embedded map has the same native core derivative.
Equality of the whole affine face with the curved manifold neighborhood is
not asserted.
-/

noncomputable section

open Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization Stiefel StabilizedSpanningDisk

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  (e : EuclideanEmbedding 6 M)
  (a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel)
  (f : Sphere 3 → M) (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f)
  (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) f s))
  {b : Sphere 3} (D : DiskData b (e.toFun ∘ f))
  {T : Vector 4 → Vector ((e.ambientDimension - 6) + 5) →L[ℝ]
    Vector (e.ambientDimension + 6)}
  (A : DiskThickening.FramedProduct D.toFun T)
  (hTb : ∀ s : Sphere 3, T s.val = boundaryFrameOperator (e.normalFrameOnSphere a f s).val)

include hf hd hTb in
theorem thickening_boundary_affine (s : Sphere 3) (v : Vector 3) :
    DiskThickening.map D.toFun A.transverse (s.val, v) =
      appendZeroMap e.ambientDimension 6 (e.ambientSphereTube f A.boundaryTransverse (s, v)) := by
  change D.toFun s.val + A.transverse s.val v =
    appendZeroMap e.ambientDimension 6 (e.toFun (f s) + A.boundaryTransverse s v)
  rw [map_add, e.append_boundaryTransverse a f hf hd D A hTb s v]
  exact congrArg (fun w ↦ w + A.transverse s.val v) (D.boundary s)

include hf hd hTb in
theorem mfderiv_retracted_boundaryTube_core (r : TubularRetraction e) (s : Sphere 3) :
    mfderiv ((𝓡 3).prod (𝓡 3)) (𝓡 e.ambientDimension)
      (e.toFun ∘ e.internalSphereTube f A.boundaryTransverse r) (s, 0) =
    mfderiv ((𝓡 3).prod (𝓡 3)) (𝓡 e.ambientDimension)
      (e.ambientSphereTube f A.boundaryTransverse) (s, 0) :=
  e.mfderiv_embedded_internalSphereTube_core f A.boundaryTransverse r hf
    A.contMDiff_boundaryTransverse hd
    (fun s ↦ Stiefel.injective
      ⟨A.boundaryTransverse s, e.norm_boundaryTransverse a f hf hd D A hTb s⟩)
    (e.range_boundaryTransverse a f hf hd D A hTb) s

end NoExoticSixSphere.EuclideanEmbedding
