import Wikipedia.SmoothSixDPoincare.ManifoldLocalFlow
import Mathlib.Geometry.Manifold.IntegralCurve.UniformTime

/-!
# Completeness of compactly supported native vector fields

The ambient time-times-quotient manifold is not compact. Compact support
is enough: finitely many local flow neighborhoods give a common positive
existence time on the support, and every point outside it has a constant
integral curve. The native uniform-time extension theorem then constructs
global trajectories without changing the manifold or its atlas.
-/

noncomputable section

open Set Metric Manifold Filter Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.OrbitPair.SupportedFlow

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) 1 M]
  {v : (x : M) → TangentSpace 𝓘(ℝ, E) x}

theorem exists_uniformIntegralCurves {K : Set M} (hK : IsCompact K)
    (hv : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1
      (fun x => (⟨x, v x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hzero : ∀ x ∉ K, v x = 0) :
    ∃ ε > (0 : ℝ), ∀ x : M, ∃ γ : ℝ → M,
      γ 0 = x ∧ IsMIntegralCurveOn γ v (Ioo (-ε) ε) := by
  classical
  choose U hU hp ε hε F hFc hF using fun p : M =>
    Wikipedia.SmoothSixDPoincare.FlowConstruction.exists_manifoldLocalFlow p (hv p)
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover U hU
    (fun x _ => mem_iUnion.mpr ⟨x, hp x⟩)
  have hN : (⋂ p ∈ s, Ioo (-(ε p)) (ε p)) ∈ 𝓝 (0 : ℝ) :=
    (biInter_finset_mem s).mpr fun p _ => Ioo_mem_nhds (neg_lt_zero.mpr (hε p)) (hε p)
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp hN
  refine ⟨δ, hδ, ?_⟩
  intro x
  by_cases hx : x ∈ K
  · obtain ⟨p, hps, hxp⟩ := mem_iUnion₂.mp (hs hx)
    refine ⟨fun t => F p (x, t), (hF p x hxp).1, (hF p x hxp).2.mono ?_⟩
    intro t ht
    apply mem_iInter₂.mp (hδsub ?_) p hps
    simpa only [mem_ball, dist_zero_right, Real.norm_eq_abs] using abs_lt.mpr ht
  · exact ⟨fun _ => x, rfl,
      (isMIntegralCurve_const (hzero x hx)).isMIntegralCurveOn _⟩

theorem exists_globalIntegralCurve [T2Space M] {K : Set M} (hK : IsCompact K)
    (hv : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1
      (fun x => (⟨x, v x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hzero : ∀ x ∉ K, v x = 0) (x : M) :
    ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurve γ v := by
  obtain ⟨ε, hε, h⟩ := exists_uniformIntegralCurves hK hv hzero
  exact exists_isMIntegralCurve_of_isMIntegralCurveOn hv hε h x

end Wikipedia.HopfProblem.OrbitPair.SupportedFlow
