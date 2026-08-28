import Wikipedia.NoExoticSixSphere.StabilizedDiskCombinedOperator
import Wikipedia.NoExoticSixSphere.ManifoldSphereParity

/-!
# The original manifold sphere parity detects extension of its combined operator

The normal columns come from the original manifold's given smooth normal
frame. Every compatible actual spanning disk yields the exact same original
sphere-parity zero criterion, expressed as extension of its combined operator.
-/

noncomputable section

open Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization Stiefel StabilizedSpanningDisk DiskBoundary

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  (e : EuclideanEmbedding 6 M)
  (a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel)
  (f : Sphere 3 → M) (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f)
  {b : Sphere 3} (D : DiskData b (e.toFun ∘ f))

def sphereCombinedMap :
    C(Sphere 3, Monomorphism.Space (e.ambientDimension + 6) (((e.ambientDimension - 6) + 5) + 4)) :=
  D.combinedMap (e.smooth.comp hf) (e.normalFrameOnSphere a f)
    (e.contMDiff_normalFrameOnSphere a f hf) (e.normalFrameOnSphere_normal a f hf)

theorem sphereCombinedMap_value (s : Sphere 3) :
    (e.sphereCombinedMap a f hf D s).val =
      OperatorSum.operator (boundaryFrameOperator (e.normalFrameOnSphere a f s).val)
        (fderiv ℝ D.toFun s.val) := rfl

theorem sphereDiskParity_zero_iff_combined_extension :
    e.sphereDiskParity a f hf D = 0 ↔ Extends (e.sphereCombinedMap a f hf D) :=
  D.parityOfDimension_zero_iff_combined_extension (e.smooth.comp hf) (e.normalFrameOnSphere a f)
    (e.contMDiff_normalFrameOnSphere a f hf) (e.normalFrameOnSphere_normal a f hf)
    (Nat.sub_add_cancel (e.dimension_le_ambient (f b))).symm

theorem sphereParity_zero_iff_combined_extension (hi : Injective f)
    (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) f s)) :
    e.sphereParity a f hf hi hd = 0 ↔ Extends (e.sphereCombinedMap a f hf D) := by
  rw [e.sphereParity_eq a f hf hi hd D]
  exact e.sphereDiskParity_zero_iff_combined_extension a f hf D

end NoExoticSixSphere.EuclideanEmbedding
