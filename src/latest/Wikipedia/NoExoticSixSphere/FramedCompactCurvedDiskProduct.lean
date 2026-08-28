import Wikipedia.NoExoticSixSphere.CompactCurvedDiskProduct
import Wikipedia.NoExoticSixSphere.EmbeddedCoreProduct
import Wikipedia.NoExoticSixSphere.FramedCoreProduct

/-!
# A full normal framing of the actual compact-tube curved product

The actual correction fixes the embedded disk and its derivative. Compact-core
injectivity constructs a thin embedded curved product inside the genuine local
tube domain. Projection and normalization extend the prescribed disk frame
over this product, retaining its exact core values. Matching this full frame
to the original manifold frame on the whole attaching collar is still separate.
-/

noncomputable section

open Function Set Metric Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization Stiefel StabilizedSpanningDisk

theorem exists_framed_compactCurvedDiskProduct {n k q : ℕ} {M : Type*}
    [TopologicalSpace M] [ChartedSpace (Vector n) M]
    (e : EuclideanEmbedding n M) (f : Sphere 3 → M)
    (hf : ContMDiff (𝓡 3) (𝓡 n) ∞ f)
    (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 n) f s))
    {b : Sphere 3} (D : DiskData b (e.toFun ∘ f))
    {T : Vector 4 → Vector k →L[ℝ] Vector (e.ambientDimension + 6)}
    (A : DiskThickening.FramedProduct D.toFun T q) (R : e.RetractionNear (range f))
    (χ : ContDiffBump (0 : Vector 4))
    (hiC : ∀ s, Injective (boundaryComplementOperator A.transverse s))
    (hCr : ∀ s, (boundaryComplementOperator A.transverse s).range = e.sphereNormalSpace f s)
    (hN : k + 4 + q = e.ambientDimension + 6) (r : ℝ) (hr : 0 < r)
    (hdom : ∀ s : Sphere 3, ∀ v ∈ closedBall (0 : Vector q) r,
      (s, v) ∈ e.compactSphereTubeDomain f (boundaryComplementOperator A.transverse) R) :
    ∃ B : DiskThickening.FramedCoreProduct (e.compactCurvedDiskProduct f D A R χ) T,
      B.radius ≤ r := by
  have hs (x : Vector 4) (hx : x ∈ closedBall (0 : Vector 4) 1)
      (v : Vector q) (hv : v ∈ closedBall (0 : Vector q) r) :
      ContDiffAt ℝ ∞ (e.compactCurvedDiskProduct f D A R χ) (x, v) :=
    e.contDiffAt_compactCurvedDiskProduct f D A R χ hf hx v
      (hdom (SphereRadialRetraction.retract b x) v hv)
  have hcore : InjOn (fun x ↦ e.compactCurvedDiskProduct f D A R χ (x, 0))
      (closedBall (0 : Vector 4) 1) := by
    intro x hx y hy he
    have hD : D.toFun x = D.toFun y := by
      simpa only [e.compactCurvedDiskProduct_core] using he
    exact congrArg Subtype.val
      (D.embedded.injective (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) hD)
  have hdi (x : Vector 4) (hx : x ∈ closedBall (0 : Vector 4) 1) :
      Injective (fderiv ℝ (e.compactCurvedDiskProduct f D A R χ) (x, 0)) := by
    rw [e.fderiv_compactCurvedDiskProduct_core f D A R χ hf hd hiC hCr hx]
    exact A.immersive x hx 0 (mem_closedBall_self A.radius_pos.le)
  obtain ⟨ε, hε, hεr, hemb, hH⟩ :=
    exists_embedded_core_product (e.compactCurvedDiskProduct f D A R χ) r hr hs hcore hdi
  have hTr (x : Vector 4) (hx : x ∈ closedBall (0 : Vector 4) 1) :
      (T x).range = (fderiv ℝ (e.compactCurvedDiskProduct f D A R χ) (x, 0)).rangeᗮ := by
    rw [e.fderiv_compactCurvedDiskProduct_core f D A R χ hf hd hiC hCr hx,
      ← A.normalFrame_core x hx]
    exact A.normalFrame_range x hx 0 (mem_closedBall_self A.radius_pos.le)
  obtain ⟨B, hB⟩ := DiskThickening.exists_framedCoreProduct
    (e.compactCurvedDiskProduct f D A R χ) T ε hε hemb
    (fun x hx v hv ↦ (hH x hx v hv).1) (fun x hx v hv ↦ (hH x hx v hv).2)
    A.smooth_coreFrame A.norm_coreFrame hTr hN
  exact ⟨B, hB.trans hεr⟩

end NoExoticSixSphere.EuclideanEmbedding
