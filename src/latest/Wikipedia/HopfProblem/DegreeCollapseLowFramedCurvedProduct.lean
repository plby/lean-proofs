import Wikipedia.HopfProblem.DegreeCollapseLowCurvedDiskProduct
import Wikipedia.HopfProblem.DegreeCollapseLowCoreProduct

/-!

# Embedded curved low-surgery products with full normal frames

The actual corrected product is embedded and immersive on a positive closed
product. Its full smooth normal frame retains the original core frame.
Agreement of that frame on the whole native attaching collar is still a
separate relative-framing construction.
-/

noncomputable section

open Function Set Metric Topology
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.LowSurgery

open NoExoticSixSphere GLOrthonormalization Stiefel StabilizedSpanningDisk

variable {d : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  (e : EuclideanEmbedding 7 M)
  (a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel)
  (f : NoExoticSixSphere.Sphere d → M) (hf : ContMDiff (𝓡 d) (𝓡 7) ∞ f)
  (hd : ∀ s, Injective (mfderiv (𝓡 d) (𝓡 7) f s))
  {b : NoExoticSixSphere.Sphere d}
  (D : FramedDisk b (e.toFun ∘ f) (fun s => a.orthonormal (f s)))
  (A : LowFramedProduct.FramedProduct (q := 7 - d) D.map D.frame)
  (R : EuclideanEmbedding.TubularRetraction e) (χ : ContDiffBump (0 : Vector (d + 1)))

include hf hd in
theorem exists_embedded_curvedDiskProduct (r : ℝ) (hr : 0 < r)
    (hdom : ∀ s : NoExoticSixSphere.Sphere d, ∀ v ∈ closedBall (0 : Vector (7 - d)) r,
      (s, v) ∈ sphereTubeDomain e f A.boundaryTransverse R) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ r ∧
      IsClosedEmbedding (fun p : closedBall (0 : Vector (d + 1)) 1 ×
          closedBall (0 : Vector (7 - d)) ε ↦
        curvedDiskProduct e f D A R χ (p.1.val, p.2.val)) ∧
      ∀ x ∈ closedBall (0 : Vector (d + 1)) 1, ∀ v ∈ closedBall (0 : Vector (7 - d)) ε,
        ContDiffAt ℝ ∞ (curvedDiskProduct e f D A R χ) (x, v) ∧
          Injective (fderiv ℝ (curvedDiskProduct e f D A R χ) (x, v)) := by
  have hs (x : Vector (d + 1)) (hx : x ∈ closedBall (0 : Vector (d + 1)) 1)
      (v : Vector (7 - d)) (hv : v ∈ closedBall (0 : Vector (7 - d)) r) :
      ContDiffAt ℝ ∞ (curvedDiskProduct e f D A R χ) (x, v) :=
    contDiffAt_curvedDiskProduct e f D A R χ hf hx v
      (hdom (SphereRadialRetraction.retract b x) v hv)
  have hcore : InjOn (fun x ↦ curvedDiskProduct e f D A R χ (x, 0))
      (closedBall (0 : Vector (d + 1)) 1) := by
    intro x hx y hy he
    have hD : D.map x = D.map y := by simpa only [curvedDiskProduct_core e] using he
    exact congrArg Subtype.val
      (D.embedded.injective (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) hD)
  have hdi (x : Vector (d + 1)) (hx : x ∈ closedBall (0 : Vector (d + 1)) 1) :
      Injective (fderiv ℝ (curvedDiskProduct e f D A R χ) (x, 0)) := by
    rw [fderiv_curvedDiskProduct_core e f D A R χ hf hd hx]
    exact A.immersive x hx 0 (mem_closedBall_self A.radius_pos.le)
  exact LowDiskThickening.exists_embedded_core_product
    (curvedDiskProduct e f D A R χ) r hr hs hcore hdi

end Wikipedia.HopfProblem.DegreeCollapse.LowSurgery

noncomputable section

open Function Set Metric
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.LowSurgery

open NoExoticSixSphere GLOrthonormalization Stiefel StabilizedSpanningDisk

variable {d : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  (e : EuclideanEmbedding 7 M)
  (a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel)
  (f : NoExoticSixSphere.Sphere d → M) (hf : ContMDiff (𝓡 d) (𝓡 7) ∞ f)
  (hd : ∀ s, Injective (mfderiv (𝓡 d) (𝓡 7) f s))
  {b : NoExoticSixSphere.Sphere d}
  (D : FramedDisk b (e.toFun ∘ f) (fun s => a.orthonormal (f s)))
  (A : LowFramedProduct.FramedProduct (q := 7 - d) D.map D.frame)
  (R : EuclideanEmbedding.TubularRetraction e) (χ : ContDiffBump (0 : Vector (d + 1)))

include hf hd in
theorem exists_framed_curvedDiskProduct (r : ℝ) (hr : 0 < r)
    (hdom : ∀ s : NoExoticSixSphere.Sphere d, ∀ v ∈ closedBall (0 : Vector (7 - d)) r,
      (s, v) ∈ sphereTubeDomain e f A.boundaryTransverse R) :
    ∃ B : LowDiskThickening.FramedCoreProduct (curvedDiskProduct e f D A R χ) D.frame,
      B.radius ≤ r := by
  obtain ⟨ε, hε, hεr, hemb, hH⟩ :=
    exists_embedded_curvedDiskProduct e a f hf hd D A R χ r hr hdom
  have hTr (x : Vector (d + 1)) (hx : x ∈ closedBall (0 : Vector (d + 1)) 1) :
      (D.frame x).range = (fderiv ℝ (curvedDiskProduct e f D A R χ) (x, 0)).rangeᗮ := by
    rw [fderiv_curvedDiskProduct_core e f D A R χ hf hd hx,
      ← A.normalFrame_core x hx]
    exact A.normalFrame_range x hx 0 (mem_closedBall_self A.radius_pos.le)
  have hN : ((e.ambientDimension - 7) + (1 + (d + 1))) + (d + 1) + (7 - d) =
      e.ambientDimension + (1 + (1 + (d + 1))) := by
    have := e.dimension_le_ambient (f b)
    have := sphere_dimension_le_seven f hd b
    omega
  obtain ⟨B, hB⟩ := LowDiskThickening.exists_framedCoreProduct
    (curvedDiskProduct e f D A R χ) D.frame ε hε hemb
    (fun x hx v hv ↦ (hH x hx v hv).1) (fun x hx v hv ↦ (hH x hx v hv).2)
    A.smooth_coreFrame A.norm_coreFrame hTr hN
  exact ⟨B, hB.trans hεr⟩

end Wikipedia.HopfProblem.DegreeCollapse.LowSurgery
