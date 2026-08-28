import Wikipedia.HopfProblem.DegreeCollapseSevenCurvedDiskProduct
import Wikipedia.HopfProblem.DegreeCollapseGeneralCoreProduct

/-!
# SevenFramedCurvedProduct

The corrected product is embedded and immersive on a positive closed product. Its full smooth normal frame retains the prescribed original disk-core frame. Full collar-frame agreement is not asserted.
-/

noncomputable section

open Function Set Metric Topology
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery

open NoExoticSixSphere GLOrthonormalization Stiefel StabilizedSpanningDisk

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  (e : EuclideanEmbedding 7 M)
  (a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel)
  (f : Sphere 3 → M) (hf : ContMDiff (𝓡 3) (𝓡 7) ∞ f)
  (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 7) f s))
  {b : Sphere 3} (D : DiskData b (e.toFun ∘ f))
  {T : Vector 4 → Vector ((e.ambientDimension - 7) + 5) →L[ℝ]
    Vector (e.ambientDimension + 6)}
  (A : EightDimensionalFramedProduct.FramedProduct D.toFun T) (R : EuclideanEmbedding.TubularRetraction e)
  (χ : ContDiffBump (0 : Vector 4))
  (hTb : ∀ s : Sphere 3, T s.val = boundaryFrameOperator (SevenSurgery.normalFrameOnSphere e a f s).val)

include a hf hd hTb in
theorem exists_embedded_curvedDiskProduct (r : ℝ) (hr : 0 < r)
    (hdom : ∀ s : Sphere 3, ∀ v ∈ closedBall (0 : Vector 4) r,
      (s, v) ∈ SevenSurgery.sphereTubeDomain e f A.boundaryTransverse R) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ r ∧
      IsClosedEmbedding (fun p : closedBall (0 : Vector 4) 1 × closedBall (0 : Vector 4) ε ↦
        SevenSurgery.curvedDiskProduct e f D A R χ (p.1.val, p.2.val)) ∧
      ∀ x ∈ closedBall (0 : Vector 4) 1, ∀ v ∈ closedBall (0 : Vector 4) ε,
        ContDiffAt ℝ ∞ (SevenSurgery.curvedDiskProduct e f D A R χ) (x, v) ∧
          Injective (fderiv ℝ (SevenSurgery.curvedDiskProduct e f D A R χ) (x, v)) := by
  have hs (x : Vector 4) (hx : x ∈ closedBall (0 : Vector 4) 1)
      (v : Vector 4) (hv : v ∈ closedBall (0 : Vector 4) r) :
      ContDiffAt ℝ ∞ (SevenSurgery.curvedDiskProduct e f D A R χ) (x, v) :=
    SevenSurgery.contDiffAt_curvedDiskProduct e f D A R χ hf hx v
      (hdom (SphereRadialRetraction.retract b x) v hv)
  have hcore : InjOn (fun x ↦ SevenSurgery.curvedDiskProduct e f D A R χ (x, 0))
      (closedBall (0 : Vector 4) 1) := by
    intro x hx y hy he
    have hD : D.toFun x = D.toFun y := by simpa only [SevenSurgery.curvedDiskProduct_core e] using he
    exact congrArg Subtype.val
      (D.embedded.injective (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) hD)
  have hdi (x : Vector 4) (hx : x ∈ closedBall (0 : Vector 4) 1) :
      Injective (fderiv ℝ (SevenSurgery.curvedDiskProduct e f D A R χ) (x, 0)) := by
    rw [SevenSurgery.fderiv_curvedDiskProduct_core e f D A R χ hf a hd hTb hx]
    exact A.immersive x hx 0 (mem_closedBall_self A.radius_pos.le)
  exact GeneralDiskThickening.exists_embedded_core_product (SevenSurgery.curvedDiskProduct e f D A R χ) r hr hs hcore hdi

end Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery

noncomputable section

open Function Set Metric
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery

open NoExoticSixSphere GLOrthonormalization Stiefel StabilizedSpanningDisk

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  (e : EuclideanEmbedding 7 M)
  (a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel)
  (f : Sphere 3 → M) (hf : ContMDiff (𝓡 3) (𝓡 7) ∞ f)
  (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 7) f s))
  {b : Sphere 3} (D : DiskData b (e.toFun ∘ f))
  {T : Vector 4 → Vector ((e.ambientDimension - 7) + 5) →L[ℝ]
    Vector (e.ambientDimension + 6)}
  (A : EightDimensionalFramedProduct.FramedProduct D.toFun T) (R : EuclideanEmbedding.TubularRetraction e)
  (χ : ContDiffBump (0 : Vector 4))
  (hTb : ∀ s : Sphere 3, T s.val = boundaryFrameOperator (SevenSurgery.normalFrameOnSphere e a f s).val)

include a hf hd hTb in
theorem exists_framed_curvedDiskProduct (r : ℝ) (hr : 0 < r)
    (hdom : ∀ s : Sphere 3, ∀ v ∈ closedBall (0 : Vector 4) r,
      (s, v) ∈ SevenSurgery.sphereTubeDomain e f A.boundaryTransverse R) :
    ∃ B : GeneralDiskThickening.FramedCoreProduct (SevenSurgery.curvedDiskProduct e f D A R χ) T,
      B.radius ≤ r := by
  obtain ⟨ε, hε, hεr, hemb, hH⟩ :=
    SevenSurgery.exists_embedded_curvedDiskProduct e a f hf hd D A R χ hTb r hr hdom
  have hTr (x : Vector 4) (hx : x ∈ closedBall (0 : Vector 4) 1) :
      (T x).range = (fderiv ℝ (SevenSurgery.curvedDiskProduct e f D A R χ) (x, 0)).rangeᗮ := by
    rw [SevenSurgery.fderiv_curvedDiskProduct_core e f D A R χ hf a hd hTb hx,
      ← A.normalFrame_core x hx]
    exact A.normalFrame_range x hx 0 (mem_closedBall_self A.radius_pos.le)
  have hN : ((e.ambientDimension - 7) + 5) + 4 + 4 = e.ambientDimension + 6 := by
    have := e.dimension_le_ambient (f b)
    omega
  obtain ⟨B, hB⟩ := GeneralDiskThickening.exists_framedCoreProduct
    (SevenSurgery.curvedDiskProduct e f D A R χ) T ε hε hemb
    (fun x hx v hv ↦ (hH x hx v hv).1) (fun x hx v hv ↦ (hH x hx v hv).2)
    A.smooth_coreFrame A.norm_coreFrame hTr hN
  exact ⟨B, hB.trans hεr⟩

end Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery
