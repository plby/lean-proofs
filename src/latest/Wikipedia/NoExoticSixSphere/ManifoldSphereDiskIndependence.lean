import Wikipedia.NoExoticSixSphere.SpanningDiskParityIndependence
import Wikipedia.NoExoticSixSphere.ManifoldSphereDiskParity

/-!
# Disk-independent parity for a fixed embedded sphere in the original manifold

The value uses the original smooth normal framing and the actual constructed
disk. The proved disk comparison makes it independent of which disk data
with the prescribed collar are chosen. The embedded sphere itself is still
fixed; descent to homology and the quadratic identity are later obligations.
-/

noncomputable section

open Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere

open GLOrthonormalization Stiefel StabilizedSpanningDisk

namespace StabilizedSpanningDisk.DiskData

theorem parityOfDimension_independent {N k : ℕ} {b : Sphere 3} {f : Sphere 3 → Vector N}
    (D₀ D₁ : DiskData b f) (hN : N = k + 6) (hf : ContMDiff (𝓡 3) (𝓡 N) ∞ f)
    (a : Sphere 3 → Space N k)
    (has : ContMDiff (𝓡 3) 𝓘(ℝ, Vector k →L[ℝ] Vector N) ∞ (fun s ↦ (a s).val))
    (ha : ∀ s, (a s).val.range ≤ (mfderiv (𝓡 3) (𝓡 N) f s).rangeᗮ) :
    D₀.parityOfDimension hN hf a has ha = D₁.parityOfDimension hN hf a has ha := by
  subst N
  exact D₀.parity_independent_of_disk D₁ hf a has ha

end StabilizedSpanningDisk.DiskData

namespace EuclideanEmbedding

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  (e : EuclideanEmbedding 6 M)
  (a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel)
  (f : Sphere 3 → M) (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f)

theorem sphereDiskParity_independent {b : Sphere 3} (D₀ D₁ : DiskData b (e.toFun ∘ f)) :
    e.sphereDiskParity a f hf D₀ = e.sphereDiskParity a f hf D₁ :=
  D₀.parityOfDimension_independent D₁
    (Nat.sub_add_cancel (e.dimension_le_ambient (f b))).symm
    (e.smooth.comp hf) (e.normalFrameOnSphere a f)
    (e.contMDiff_normalFrameOnSphere a f hf) (e.normalFrameOnSphere_normal a f hf)

def embeddedSphereParity (b : Sphere 3) (hi : Injective f)
    (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) f s)) : ZMod 2 :=
  e.sphereDiskParity a f hf (Classical.choice (e.nonempty_sphereDiskData f b hf hi hd))

theorem embeddedSphereParity_eq (b : Sphere 3) (hi : Injective f)
    (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) f s)) (D : DiskData b (e.toFun ∘ f)) :
    e.embeddedSphereParity a f hf b hi hd = e.sphereDiskParity a f hf D :=
  e.sphereDiskParity_independent a f hf _ D

end EuclideanEmbedding

end NoExoticSixSphere
