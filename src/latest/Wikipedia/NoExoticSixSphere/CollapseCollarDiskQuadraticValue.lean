import Wikipedia.NoExoticSixSphere.RegularDiskEquationFrame
import Wikipedia.NoExoticSixSphere.FramedCollapseNormalComparison

/-!
# Immersed disks in regular equations with the original collapse collar

If the ambient defining equations agree near the boundary with the actual
normalized collapse coordinates, their differential calibrates the
original normal frame. The extending right inverse is constructed, and
the original geometric quadratic value vanishes. No separately chosen
boundary frame or disk-frame extension is an input.

This implication still requires a genuine immersed disk in the regular
zero set; it does not assert disk existence for boundary homology classes.
-/

noncomputable section

open Function Filter Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding.FramedCollapseData

open GLOrthonormalization

section Collar

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector n) M]
  {e : EuclideanEmbedding n M}
  {a : SmoothRangeFrame (𝓡 n) e.normalProjection e.NormalModel}
  (d : e.FramedCollapseData a)

theorem collar_equation_differential_frame
    (P : Vector e.ambientDimension × ℝ → e.NormalModel) (x : M)
    (hcollar : P =ᶠ[𝓝 (e.toFun x, (0 : ℝ))]
      (fun z : Vector e.ambientDimension × ℝ ↦ d.normalizedCoordinates z.1))
    (u : e.NormalModel) : fderiv ℝ P (e.toFun x, 0) (a.ambient x u, 0) = u := by
  have hc := (d.contDiffOn_normalizedCoordinates.contDiffAt
    (d.open_neighborhood.mem_nhds (d.range_subset ⟨x, rfl⟩))).differentiableAt
      (by simp)
  have hD := hc.hasFDerivAt.comp (e.toFun x, (0 : ℝ))
    (ContinuousLinearMap.fst ℝ (Vector e.ambientDimension) ℝ).hasFDerivAt
  change HasFDerivAt (fun z : Vector e.ambientDimension × ℝ ↦
    d.normalizedCoordinates z.1) _ _ at hD
  rw [hcollar.fderiv_eq, hD.fderiv]
  exact congrArg (fun L : e.NormalModel →L[ℝ] e.NormalModel ↦ L u)
    (d.normalizedCoordinates_differential_frame x)

end Collar

variable {M : Type} [TopologicalSpace M] [T2Space M] [ChartedSpace (Vector 6) M]
  [IsManifold (𝓡 6) ∞ M] [CompactSpace M] [SimplyConnectedSpace M]
  {e : EuclideanEmbedding 6 M}
  {a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel}
  (d : e.FramedCollapseData a)
  (r : TubularRetraction e) (m : M) [Subsingleton (π_ 2 M m)]

theorem quadraticValue_zero_of_regular_disk_with_collapse_collar
    (f : C(Sphere 3, M)) (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f) (hi : Injective f)
    (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) f s))
    (F : Vector 4 → Vector e.ambientDimension × ℝ)
    (hF : ∀ x ∈ Metric.closedBall (0 : Vector 4) 1, ContDiffAt ℝ ∞ F x)
    (hDF : ∀ x ∈ Metric.closedBall (0 : Vector 4) 1, Injective (fderiv ℝ F x))
    (hb : ∀ s : Sphere 3, F s.val = (e.toFun (f s), 0))
    (P : Vector e.ambientDimension × ℝ → e.NormalModel)
    (hP : ∀ x ∈ Metric.closedBall (0 : Vector 4) 1, ContDiffAt ℝ ∞ P (F x))
    (hzero : ∀ x ∈ Metric.closedBall (0 : Vector 4) 1, P (F x) = 0)
    (hs : ∀ x ∈ Metric.closedBall (0 : Vector 4) 1, Surjective (fderiv ℝ P (F x)))
    (hcollar : ∀ s : Sphere 3, P =ᶠ[𝓝 (e.toFun (f s), (0 : ℝ))]
      (fun z : Vector e.ambientDimension × ℝ ↦ d.normalizedCoordinates z.1))
    (hheight : (∀ s : Sphere 3, 0 < (fderiv ℝ F s.val s.val).2) ∨
      (∀ s : Sphere 3, (fderiv ℝ F s.val s.val).2 < 0)) :
    e.modTwoHomologyQuadraticForm a r m (SixSphereMiddleParity.sphereClass f) = 0 :=
  e.quadraticValue_zero_of_regular_disk_equations a r m f hf hi hd F hF hDF hb
    P hP hzero hs (fun s ↦ d.collar_equation_differential_frame P (f s) (hcollar s)) hheight

end NoExoticSixSphere.EuclideanEmbedding.FramedCollapseData
