import Wikipedia.HopfProblem.CuspCircleNormalTrivializationConifoldMap

/-!
# Native real analyticity of the global small-resolution matrix map

Regularity is checked in the original affine Riemann-sphere charts and
then transported through the already proved diffeomorphism of the actual
toric open neighborhood. No new atlas on the source is introduced.
-/

noncomputable section

open Set Filter Topology
open scoped ContDiff Manifold Matrix.Norms.Elementwise

namespace Wikipedia.HopfProblem.CuspCircleNormalTrivialization.Conifold

open ToricCharts ConifoldStandardBoundary

local instance matrixTopology : TopologicalSpace MatrixSpace :=
  (inferInstance : PseudoMetricSpace MatrixSpace).toUniformSpace.toTopologicalSpace

local instance matrixChartedSpace : ChartedSpace MatrixSpace MatrixSpace :=
  chartedSpaceSelf MatrixSpace

/-- The normed matrix topology used in the model is the original entrywise
product topology; this only makes the standard instance diamond explicit. -/
theorem matrixTopology_eq_pi :
    matrixTopology = inferInstanceAs (TopologicalSpace (Fin 2 → Fin 2 → ℂ)) := rfl

local notation "IP" => 𝓘(ℝ, Model)
local notation "IM" => 𝓘(ℝ, MatrixSpace)
local notation "I₃" => 𝓘(ℝ, CoordinateSpace 3)

/-- The global matrix is real analytic in the unchanged sphere/product atlas. -/
theorem contMDiff_productMap : ContMDiff IP IM ω productMap := by
  intro p
  obtain ⟨b, q, rfl⟩ := baseProductChart_cover p
  let e := baseProductParametrization b
  have hq : q ∈ e.source := by
    rw [baseProductParametrization_source]
    exact mem_univ q
  have ht : baseProductChart b q ∈ e.target := e.map_source hq
  have hi : ContMDiffAt IP IP ω e.invFun (baseProductChart b q) :=
    (e.contMDiffOn_invFun (baseProductChart b q) ht).contMDiffAt
      (e.open_target.mem_nhds ht)
  have hm : ContMDiffAt IP IM ω (normalChartMatrix b ∘ e.invFun)
      (baseProductChart b q) :=
    (contDiff_normalChartMatrix b (n := ω)).contMDiff.contMDiffAt.comp _ hi
  apply hm.congr_of_eventuallyEq
  filter_upwards [e.open_target.mem_nhds ht] with y hy
  change productMap y = normalChartMatrix b (e.invFun y)
  have he : baseProductChart b (e.invFun y) = y := e.right_inv hy
  calc
    productMap y = productMap (baseProductChart b (e.invFun y)) := congrArg productMap he.symm
    _ = normalChartMatrix b (e.invFun y) := productMap_baseProductChart b _

/-- The genuine conifold map is real analytic in the original toric atlas. -/
theorem contMDiff_toricMap : ContMDiff I₃ IM ω toricMap :=
  contMDiff_productMap.comp toricNeighborhoodDiffeomorph.symm.contMDiff

end Wikipedia.HopfProblem.CuspCircleNormalTrivialization.Conifold
