import Wikipedia.NoExoticSixSphere.ManifoldSphereTransverseFrame
import Wikipedia.NoExoticSixSphere.SpanningDiskRadialComplement
import Wikipedia.NoExoticSixSphere.TransverseRadialExtension

/-!
# Radial transverse data lie in the actual complementary disk planes

The original internal normal space identifies the boundary transverse range.
The retained disk collar and radial partial normal frame then put these same
radial transverse columns in the actual combined-operator complement.
-/

noncomputable section

open Function Set Metric
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
theorem range_transverseExtension_le_complement
    {V : Set (Vector 4)} (hV : IsOpen V)
    (hDV : EqOn D.toFun (collar b (e.toFun ∘ f)) V) {x : Vector 4} (hxV : x ∈ V)
    (hx : (1 / 2 : ℝ) < ‖x‖)
    (hTx : T x = boundaryFrameOperator
      (e.normalFrameOnSphere a f (SphereRadialRetraction.retract b x)).val) :
    (A.transverseExtension b x).range ≤
      (OperatorSum.operator (T x) (fderiv ℝ D.toFun x)).rangeᗮ := by
  let s := SphereRadialRetraction.retract b x
  have hW : e.sphereNormalSpace f s = (e.normalFrameOnSphere a f s).val.rangeᗮ ⊓
      (mfderiv (𝓡 3) (𝓡 e.ambientDimension) (e.toFun ∘ f) s).rangeᗮ := by
    rw [e.normalFrameOnSphere_range a f s]
    change e.sphereNormalSpace f s = (e.tangentImage (f s))ᗮᗮ ⊓ _
    rw [Submodule.orthogonal_orthogonal]
    rfl
  rw [A.transverseExtension_eq_radial b hx,
    e.transverse_range_boundary a f hf hd D A hTb, hTx]
  change (e.sphereNormalSpace f s).map _ ≤ _
  rw [hW]
  exact map_normal_le_combined_orthogonal_radial b (e.toFun ∘ f) (e.smooth.comp hf)
    hV hDV hxV hx (e.normalFrameOnSphere a f s).val

end NoExoticSixSphere.EuclideanEmbedding
