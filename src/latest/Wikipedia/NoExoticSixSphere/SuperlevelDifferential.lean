import Wikipedia.NoExoticSixSphere.SuperlevelInclusion
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-!
# Tangent comparison for the superlevel inclusion

Even at boundary points, the differential of the actual superlevel inclusion
is an isomorphism onto the ambient tangent space. This concerns the full
tangent spaces of manifolds with boundary, not their inward tangent cones.
-/

open Set Topology Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SuperlevelAtlas

variable {B H M K : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [TopologicalSpace H] {I : ModelWithCorners ℝ B H}
  [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup K] [NormedSpace ℝ K]
  {f : M → ℝ} (A : SuperlevelAtlas (K := K) I f)

theorem bijective_mfderiv_subtype_val (x : {x : M // 0 ≤ f x}) :
    letI := A.chartedSpace;
    Bijective (mfderiv (ProductHalfSpace.model K) I
      ((↑) : {x : M // 0 ≤ f x} → M) x) := by
  let := A.chartedSpace
  let := A.isManifold
  have hn : IsLocalDiffeomorphAt I 𝓘(ℝ, ℝ × K) ∞ (A.normalForm x) x.val :=
    ⟨A.normalForm x, A.mem_source x, eqOn_refl _ _⟩
  have hninj := (hn.mfderivToContinuousLinearEquiv (by simp)).injective
  have hi := A.contMDiff_subtype_val.mdifferentiable (by simp) x
  have heq : (extChartAt (ProductHalfSpace.model K) x : {x : M // 0 ≤ f x} → ℝ × K)
      =ᶠ[𝓝 x] (A.normalForm x) ∘ ((↑) : {x : M // 0 ≤ f x} → M) := by
    filter_upwards [(A.chart x).open_source.mem_nhds (A.mem_chart_source x)] with y hy
    exact A.chart_apply_val x y hy
  have hc : Bijective (mfderiv (ProductHalfSpace.model K) 𝓘(ℝ, ℝ × K)
      (extChartAt (ProductHalfSpace.model K) x) x) := by
    rw [(hasMFDerivAt_extChartAt (I := ProductHalfSpace.model K)
      (A.mem_chart_source x)).mfderiv]
    exact (mdifferentiable_chart (I := ProductHalfSpace.model K) x).mfderiv_bijective
      (A.mem_chart_source x)
  rw [heq.mfderiv_eq, mfderiv_comp x (hn.mdifferentiableAt (by simp)) hi] at hc
  constructor
  · intro v w hvw
    exact hc.1 (congrArg (mfderiv I 𝓘(ℝ, ℝ × K) (A.normalForm x) x.val) hvw)
  · intro v
    obtain ⟨w, hw⟩ := hc.2 (mfderiv I 𝓘(ℝ, ℝ × K) (A.normalForm x) x.val v)
    exact ⟨w, hninj hw⟩

end NoExoticSixSphere.SuperlevelAtlas
