import Wikipedia.NoExoticSixSphere.EmbeddedCurvedDiskProduct
import Wikipedia.NoExoticSixSphere.FramedCoreProduct

/-!
# A full normal framing of the actual curved disk product

The corrected product retains the original core derivative, so its core
normal frame is the already constructed disk frame. Projection and smooth
normalization extend that frame over a smaller embedded curved product.
Agreement with the original manifold's frame away from the boundary core
is not asserted here and remains a separate attaching-face obligation.
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
  (A : DiskThickening.FramedProduct D.toFun T) (R : TubularRetraction e)
  (χ : ContDiffBump (0 : Vector 4))
  (hTb : ∀ s : Sphere 3, T s.val = boundaryFrameOperator (e.normalFrameOnSphere a f s).val)

include a hf hd hTb in
theorem exists_framed_curvedDiskProduct (r : ℝ) (hr : 0 < r)
    (hdom : ∀ s : Sphere 3, ∀ v ∈ closedBall (0 : Vector 3) r,
      (s, v) ∈ e.sphereTubeDomain f A.boundaryTransverse R) :
    ∃ B : DiskThickening.FramedCoreProduct (e.curvedDiskProduct f D A R χ) T,
      B.radius ≤ r := by
  obtain ⟨ε, hε, hεr, hemb, hH⟩ :=
    e.exists_embedded_curvedDiskProduct a f hf hd D A R χ hTb r hr hdom
  have hTr (x : Vector 4) (hx : x ∈ closedBall (0 : Vector 4) 1) :
      (T x).range = (fderiv ℝ (e.curvedDiskProduct f D A R χ) (x, 0)).rangeᗮ := by
    rw [e.fderiv_curvedDiskProduct_core f D A R χ hf a hd hTb hx,
      ← A.normalFrame_core x hx]
    exact A.normalFrame_range x hx 0 (mem_closedBall_self A.radius_pos.le)
  have hN : ((e.ambientDimension - 6) + 5) + 4 + 3 = e.ambientDimension + 6 := by
    have := e.dimension_le_ambient (f b)
    omega
  obtain ⟨B, hB⟩ := DiskThickening.exists_framedCoreProduct
    (e.curvedDiskProduct f D A R χ) T ε hε hemb
    (fun x hx v hv ↦ (hH x hx v hv).1) (fun x hx v hv ↦ (hH x hx v hv).2)
    A.smooth_coreFrame A.norm_coreFrame hTr hN
  exact ⟨B, hB.trans hεr⟩

end NoExoticSixSphere.EuclideanEmbedding
