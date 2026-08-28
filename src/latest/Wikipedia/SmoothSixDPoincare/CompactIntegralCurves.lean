import Wikipedia.SmoothSixDPoincare.ManifoldLocalFlow
import Mathlib.Geometry.Manifold.IntegralCurve.UniformTime

/-!
# Completeness of vector fields on compact boundaryless manifolds

The local flows provide a common existence time on a neighborhood of each
point. A finite subcover gives a uniform positive time on the whole compact
manifold. The proved uniform-time extension theorem then gives global curves.
-/

noncomputable section

open Set Metric Manifold Filter Topology
open scoped ContDiff

namespace Wikipedia.SmoothSixDPoincare.FlowConstruction

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) 1 M]
  [T2Space M] [CompactSpace M]

omit [T2Space M] in
/-- Compactness makes the local existence time uniform over the original manifold. -/
theorem exists_uniformIntegralCurves {v : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hv : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1
      (fun x => (⟨x, v x⟩ : TangentBundle 𝓘(ℝ, E) M))) :
    ∃ ε > (0 : ℝ), ∀ x : M, ∃ γ : ℝ → M,
      γ 0 = x ∧ IsMIntegralCurveOn γ v (Ioo (-ε) ε) := by
  classical
  choose U hU hp ε hε F hFc hF using fun p : M =>
    exists_manifoldLocalFlow p (hv p)
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover U hU
    (fun x _ => mem_iUnion.mpr ⟨x, hp x⟩)
  have hN : (⋂ p ∈ s, Ioo (-(ε p)) (ε p)) ∈ 𝓝 (0 : ℝ) :=
    (biInter_finset_mem s).mpr fun p _ => Ioo_mem_nhds (neg_lt_zero.mpr (hε p)) (hε p)
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp hN
  refine ⟨δ, hδ, ?_⟩
  intro x
  obtain ⟨p, hps, hx⟩ := mem_iUnion₂.mp (hs (mem_univ x))
  refine ⟨fun t => F p (x, t), (hF p x hx).1, (hF p x hx).2.mono ?_⟩
  intro t ht
  apply mem_iInter₂.mp (hδsub ?_) p hps
  simpa only [mem_ball, dist_zero_right, Real.norm_eq_abs] using abs_lt.mpr ht

/-- A continuously differentiable field on a compact boundaryless manifold is complete. -/
theorem exists_globalIntegralCurve {v : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hv : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1
      (fun x => (⟨x, v x⟩ : TangentBundle 𝓘(ℝ, E) M))) (x : M) :
    ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurve γ v := by
  obtain ⟨ε, hε, h⟩ := exists_uniformIntegralCurves hv
  exact exists_isMIntegralCurve_of_isMIntegralCurveOn hv hε h x

end Wikipedia.SmoothSixDPoincare.FlowConstruction
