import Wikipedia.HopfProblem.SpecialPeriodsTriangleCuspAtlasCore
import Wikipedia.HopfProblem.SpecialPeriodsTriangleCuspChart
import Wikipedia.HopfProblem.SpecialPeriodsTriangleCuspImageAnalytic

/-!
# The compact complex curve of the actual triangle quotient

The original complex quotient and the proved exponential cusp chart are
glued on the actual one-point compactification.  Their analytic agreement
is verified on the punctured cusp using the genuine partial
biholomorphism of the quotient.  Thus the added cusp is an actual smooth
complex point.

This constructs a compact connected complex curve and its holomorphic
triangle projection.  It does not assume or assert a biholomorphism with
the projective line; that uniformization remains a separate theorem.
-/

noncomputable section

open Set Topology UpperHalfPlane
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods

attribute [local instance] triangleOrbitChartedSpace

local instance : IsManifold 𝓘(ℂ) ω TriangleOrbitSpace := triangleOrbit_isManifold

namespace Triangle

theorem cuspFullChart_pullback_eqOn (Y : ℝ) (hY : width ≤ Y) :
    EqOn (cuspFullChart Y hY ∘ triangleOpenInclusion) (cuspImagePartialDiffeomorph Y hY)
      (cuspImage Y : Set TriangleOrbitSpace) := by
  intro q hq
  simp only [Function.comp_apply, cuspFullChart_openInclusion Y hY q hq,
    cuspImagePartialDiffeomorph_apply Y hY q hq]

theorem cuspFullChart_pullback_holomorphic (Y : ℝ) (hY : width ≤ Y) :
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (cuspFullChart Y hY ∘ triangleOpenInclusion)
      (triangleOpenInclusion ⁻¹' (cuspFullChart Y hY).source) := by
  rw [cuspFullChart_source, cuspNeighborhood_preimage]
  exact (cuspImagePartialDiffeomorph_holomorphic Y hY).congr
    (cuspFullChart_pullback_eqOn Y hY)

theorem cuspFullChart_pullback_isLocalDiffeomorphAt (Y : ℝ) (hY : width ≤ Y)
    (q : TriangleOrbitSpace) (hq : triangleOpenInclusion q ∈ (cuspFullChart Y hY).source) :
    IsLocalDiffeomorphAt 𝓘(ℂ) 𝓘(ℂ) ω
      (cuspFullChart Y hY ∘ triangleOpenInclusion) q := by
  have hmem : q ∈ cuspImage Y :=
    (openInclusion_mem_cuspNeighborhood Y q).mp hq
  refine ⟨cuspImagePartialDiffeomorph Y hY, ?_, ?_⟩
  · rw [cuspImagePartialDiffeomorph_source]
    exact hmem
  · rw [cuspImagePartialDiffeomorph_source]
    exact cuspFullChart_pullback_eqOn Y hY

end Triangle

open Triangle

/-- The original quotient charts and the actual filled exponential
chart, with all analytic overlap conditions proved. -/
def triangleCompactifiedAtlasData :
    BranchedQuotientAtlas.Data (E := ℂ) triangleOpenInclusion (Option TriangleOrbitSpace) :=
  OnePointAtlas.data (cuspFullChart width le_rfl)
    (cuspPoint_mem_cuspNeighborhood width)
    (cuspFullChart_pullback_holomorphic width le_rfl)
    (cuspFullChart_pullback_isLocalDiffeomorphAt width le_rfl)

/-- The complex atlas on the actual compactified triangle orbit space. -/
@[instance_reducible] def triangleCompactifiedChartedSpace :
    ChartedSpace ℂ TriangleCompactifiedOrbitSpace :=
  triangleCompactifiedAtlasData.chartedSpace

/-- The added cusp point is a smooth complex point of the actual compact
connected quotient curve. -/
theorem triangleCompactified_isManifold :
    letI := triangleCompactifiedChartedSpace
    IsManifold 𝓘(ℂ) ω TriangleCompactifiedOrbitSpace :=
  triangleCompactifiedAtlasData.isManifold

theorem triangleCompactified_cuspChart_mem_atlas :
    letI := triangleCompactifiedChartedSpace
    cuspFullChart width le_rfl ∈ atlas ℂ TriangleCompactifiedOrbitSpace :=
  triangleCompactifiedAtlasData.chart_mem_atlas none

theorem triangleOpenInclusion_holomorphic :
    letI := triangleCompactifiedChartedSpace
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω triangleOpenInclusion :=
  triangleCompactifiedAtlasData.contMDiff_project

/-- The actual original upper-half-plane projection, now with the
compact complex quotient as its target. -/
def triangleCompactifiedProjection : ℍ → TriangleCompactifiedOrbitSpace :=
  triangleOpenInclusion ∘ triangleOrbitProjection

theorem triangleCompactifiedProjection_holomorphic :
    letI := triangleCompactifiedChartedSpace
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω triangleCompactifiedProjection := by
  let := triangleCompactifiedChartedSpace
  exact triangleOpenInclusion_holomorphic.comp triangleOrbitProjection_holomorphic

theorem triangleCompactifiedProjection_ne_cusp (z : ℍ) :
    triangleCompactifiedProjection z ≠ triangleCuspPoint :=
  triangleOpenInclusion_ne_cusp _

theorem triangleCompactifiedProjection_cusp_formula (z : horodisc width) :
    cuspFullChart width le_rfl (triangleCompactifiedProjection (z : ℍ)) =
      Complex.exp (2 * Real.pi * Complex.I * (z : ℍ) / width) :=
  cuspFullChart_mk_exp width le_rfl z

theorem triangleCompactified_cuspChart_holomorphic :
    letI := triangleCompactifiedChartedSpace
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (cuspFullChart width le_rfl)
      (cuspNeighborhood width : Set TriangleCompactifiedOrbitSpace) := by
  let := triangleCompactifiedChartedSpace
  let := triangleCompactified_isManifold
  exact contMDiffOn_of_mem_maximalAtlas
    (IsManifold.subset_maximalAtlas triangleCompactified_cuspChart_mem_atlas)

theorem triangleCompactified_cuspChart_symm_holomorphic :
    letI := triangleCompactifiedChartedSpace
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (cuspFullChart width le_rfl).symm
      (Metric.ball 0 (cuspRadius width)) := by
  let := triangleCompactifiedChartedSpace
  let := triangleCompactified_isManifold
  exact contMDiffOn_symm_of_mem_maximalAtlas
    (IsManifold.subset_maximalAtlas triangleCompactified_cuspChart_mem_atlas)

end Wikipedia.HopfProblem.SpecialPeriods
