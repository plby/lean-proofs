import Wikipedia.NoExoticSixSphere.ManifoldSphereDiskIndependence
import Wikipedia.NoExoticSixSphere.SpanningDiskFallback

/-!
# Parity of a fixed embedded sphere, independent of disk and fallback point

The fixed sphere lies in the original six-manifold and uses its given smooth
normal framing. The value agrees with the actual normal-disk obstruction for
every compatible spanning disk, regardless of the auxiliary radial-extension
point. No representative-independence or homology-descent assertion is made.
-/

noncomputable section

open Function Metric
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization Stiefel StabilizedSpanningDisk

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  (e : EuclideanEmbedding 6 M)
  (a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel)
  (f : Sphere 3 → M) (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f)

theorem sphereDiskParity_changeFallback {b : Sphere 3}
    (D : DiskData b (e.toFun ∘ f)) (b' : Sphere 3) :
    e.sphereDiskParity a f hf (D.changeFallback b') = e.sphereDiskParity a f hf D := by
  exact D.parityOfDimension_changeFallback b'
    (Nat.sub_add_cancel (e.dimension_le_ambient (f b))).symm
    (e.smooth.comp hf) (e.normalFrameOnSphere a f)
    (e.contMDiff_normalFrameOnSphere a f hf) (e.normalFrameOnSphere_normal a f hf)

theorem sphereDiskParity_independent_all {b₀ b₁ : Sphere 3}
    (D₀ : DiskData b₀ (e.toFun ∘ f)) (D₁ : DiskData b₁ (e.toFun ∘ f)) :
    e.sphereDiskParity a f hf D₀ = e.sphereDiskParity a f hf D₁ := by
  calc
    e.sphereDiskParity a f hf D₀ =
        e.sphereDiskParity a f hf (D₀.changeFallback b₁) :=
      (e.sphereDiskParity_changeFallback a f hf D₀ b₁).symm
    _ = e.sphereDiskParity a f hf D₁ := e.sphereDiskParity_independent a f hf _ D₁

theorem embeddedSphereParity_independent_fallback (b₀ b₁ : Sphere 3) (hi : Injective f)
    (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) f s)) :
    e.embeddedSphereParity a f hf b₀ hi hd = e.embeddedSphereParity a f hf b₁ hi hd :=
  e.sphereDiskParity_independent_all a f hf _ _

/-- The actual disk obstruction of a fixed smooth embedded immersive three-sphere. -/
def sphereParity (hi : Injective f) (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) f s)) :
    ZMod 2 :=
  e.embeddedSphereParity a f hf (pole 3) hi hd

theorem sphereParity_eq (hi : Injective f)
    (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) f s)) {b : Sphere 3}
    (D : DiskData b (e.toFun ∘ f)) :
    e.sphereParity a f hf hi hd = e.sphereDiskParity a f hf D :=
  e.sphereDiskParity_independent_all a f hf _ D

theorem sphereParity_zero_iff_smooth_extension (hi : Injective f)
    (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) f s)) {b : Sphere 3}
    (D : DiskData b (e.toFun ∘ f)) :
    e.sphereParity a f hf hi hd = 0 ↔
      ∃ T : Vector 4 → Vector ((e.ambientDimension - 6) + 5) →L[ℝ]
          Vector (e.ambientDimension + 6),
        (∀ x ∈ closedBall (0 : Vector 4) 1, ContDiffAt ℝ ∞ T x) ∧
        (∀ x ∈ closedBall (0 : Vector 4) 1, ∀ w, ‖T x w‖ = ‖w‖) ∧
        (∀ x ∈ closedBall (0 : Vector 4) 1, (T x).range ≤ (fderiv ℝ D.toFun x).rangeᗮ) ∧
        ∀ s : Sphere 3, T s.val = boundaryFrameOperator (e.normalFrameOnSphere a f s).val := by
  rw [e.sphereParity_eq a f hf hi hd D]
  exact e.sphereDiskParity_zero_iff_smooth_extension a f hf D

end NoExoticSixSphere.EuclideanEmbedding
