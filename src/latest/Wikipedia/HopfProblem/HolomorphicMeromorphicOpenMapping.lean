import Wikipedia.HopfProblem.HolomorphicFunctionSheafStalkChartSections
import Mathlib.Analysis.Complex.OpenMapping

/-!
# Open mapping for holomorphic maps to complex curves

The analytic open-mapping theorem is transported through the given
extended charts.  A holomorphic map from a boundaryless complex manifold
to a boundaryless complex curve is locally constant or maps every
neighborhood to a neighborhood.  In particular, a map that is nowhere
locally constant is open in the original manifold topologies.

No nonvanishing-derivative or alternative-atlas assumption is needed.
-/

open Set Filter Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicMeromorphicOpenMapping

variable {E H M : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
  [TopologicalSpace M] [ChartedSpace H M] [I.Boundaryless]

section Curve

variable {K N : Type} [TopologicalSpace K]
  (J : ModelWithCorners ℂ ℂ K)
  [TopologicalSpace N] [ChartedSpace K N] [J.Boundaryless]

/-- The local open-mapping dichotomy for an actual holomorphic map into
a complex curve, expressed using the original neighborhood filters. -/
theorem contMDiffAt_eventually_constant_or_nhds_le_map_nhds
    {f : M → N} {x : M} (hf : ContMDiffAt I J ω f x) :
    (f =ᶠ[𝓝 x] fun _ => f x) ∨ 𝓝 (f x) ≤ Filter.map f (𝓝 x) := by
  let F : E → ℂ := extChartAt J (f x) ∘ f ∘ (extChartAt I x).symm
  have hF : AnalyticAt ℂ F (extChartAt I x x) := by
    have hc := (contMDiffAt_iff.mp hf).2
    rw [ModelWithCorners.Boundaryless.range_eq_univ, contDiffWithinAt_univ] at hc
    exact hc.analyticAt
  have hbase : F (extChartAt I x x) = extChartAt J (f x) (f x) := by
    simp only [F, Function.comp_apply, extChartAt_to_inv]
  rcases hF.eventually_constant_or_nhds_le_map_nhds with hconst | hopen
  · left
    have hconst' : F =ᶠ[𝓝 (extChartAt I x x)] fun _ => F (extChartAt I x x) := hconst
    have hpull := hconst'.comp_tendsto (continuousAt_extChartAt (I := I) x)
    filter_upwards [hpull, extChartAt_source_mem_nhds (I := I) x,
      hf.continuousAt.eventually (extChartAt_source_mem_nhds (I := J) (f x))]
      with y hy hys hyf
    have heq : extChartAt J (f x) (f y) = extChartAt J (f x) (f x) := by
      simpa only [F, Function.comp_apply, (extChartAt I x).left_inv hys,
        extChartAt_to_inv] using hy
    exact (extChartAt J (f x)).injOn hyf (mem_extChartAt_source (f x)) heq
  · right
    have hcomp : ((extChartAt J (f x)).symm ∘ F) =ᶠ[𝓝 (extChartAt I x x)]
        (f ∘ (extChartAt I x).symm) := by
      have ht : Tendsto (f ∘ (extChartAt I x).symm)
          (𝓝 (extChartAt I x x)) (𝓝 (f x)) :=
        hf.continuousAt.tendsto.comp (HolomorphicFunctionSheaf.chartInverse_tendsto I x)
      filter_upwards [ht.eventually (extChartAt_source_mem_nhds (I := J) (f x))]
        with z hz
      exact (extChartAt J (f x)).left_inv hz
    calc
      𝓝 (f x) = Filter.map (extChartAt J (f x)).symm
          (𝓝 (F (extChartAt I x x))) := by
        rw [hbase, HolomorphicFunctionSheaf.chartInverse_map_nhds J (f x)]
      _ ≤ Filter.map (extChartAt J (f x)).symm
          (Filter.map F (𝓝 (extChartAt I x x))) := Filter.map_mono hopen
      _ = Filter.map (f ∘ (extChartAt I x).symm) (𝓝 (extChartAt I x x)) := by
        rw [Filter.map_map]
        exact Filter.map_congr hcomp
      _ = Filter.map f (𝓝 x) := by
        rw [← Filter.map_map, HolomorphicFunctionSheaf.chartInverse_map_nhds I x]

/-- A holomorphic map to a complex curve which is nowhere locally
constant is an open map in the original manifold topologies. -/
theorem isOpenMap_of_contMDiff_of_not_locally_constant {f : M → N}
    (hf : ContMDiff I J ω f) (hne : ∀ x, ¬ f =ᶠ[𝓝 x] fun _ => f x) :
    IsOpenMap f := by
  rw [isOpenMap_iff_nhds_le]
  intro x
  exact (contMDiffAt_eventually_constant_or_nhds_le_map_nhds I J (hf x)).resolve_left
    (hne x)

end Curve

/-- Scalar-valued specialization of the native manifold open-mapping
theorem. -/
theorem isOpenMap_of_contMDiff_scalar_of_not_locally_constant {f : M → ℂ}
    (hf : ContMDiff I 𝓘(ℂ) ω f) (hne : ∀ x, ¬ f =ᶠ[𝓝 x] fun _ => f x) :
    IsOpenMap f :=
  isOpenMap_of_contMDiff_of_not_locally_constant I 𝓘(ℂ) hf hne

end Wikipedia.HopfProblem.HolomorphicMeromorphicOpenMapping
