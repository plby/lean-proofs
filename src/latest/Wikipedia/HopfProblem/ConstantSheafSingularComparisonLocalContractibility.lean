import Wikipedia.HopfProblem.ConstantSheafSingularComparisonLocalContractibilityManifold
import Wikipedia.HopfProblem.ToricComponentManifold
import Wikipedia.HopfProblem.RiemannSphere
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldRealManifold

/-!
# Local contractibility of the original normalization, base, and threefold

The existing actual affine atlases supply local contractibility of every
toric ray surface, the Riemann sphere, and the constructed compact complex
threefold. The threefold statement does not assume any identification with
a sphere. The singular central cusp is not included in this manifold
argument.
-/

noncomputable section

namespace Wikipedia.HopfProblem.ConstantSheafSingularComparison.LocalContractibility

/-- Every original toric ray surface has a genuine contractible
neighborhood basis in its original subspace topology. -/
theorem rayDivisor_stronglyLocallyContractibleSpace (v : Fin 2 → ℤ) :
    StronglyLocallyContractibleSpace (ToricSpace.rayDivisor v) :=
  normedChartedSpace_stronglyLocallyContractibleSpace
    (ToricCharts.CoordinateSpace 2) (ToricSpace.rayDivisor v)

theorem rayDivisor_locallyContractibleSpace (v : Fin 2 → ℤ) :
    LocallyContractibleSpace (ToricSpace.rayDivisor v) :=
  normedChartedSpace_locallyContractibleSpace
    (ToricCharts.CoordinateSpace 2) (ToricSpace.rayDivisor v)

/-- The actual normalization component `E₀`, rather than an abstract
replacement surface, is locally contractible. -/
theorem normalization_locallyContractibleSpace :
    LocallyContractibleSpace (ToricSpace.rayDivisor 0) :=
  rayDivisor_locallyContractibleSpace 0

/-- The original two complex affine charts give the Riemann sphere a
genuine contractible neighborhood basis. -/
theorem sphere_stronglyLocallyContractibleSpace : StronglyLocallyContractibleSpace RiemannSphere :=
  normedChartedSpace_stronglyLocallyContractibleSpace ℂ RiemannSphere

theorem sphere_locallyContractibleSpace : LocallyContractibleSpace RiemannSphere :=
  normedChartedSpace_locallyContractibleSpace ℂ RiemannSphere

/-- The original glued threefold atlas, with no sphere assumption,
provides its genuine contractible neighborhood basis. -/
theorem threefold_stronglyLocallyContractibleSpace :
    StronglyLocallyContractibleSpace SpecialPeriods.Threefold.Space := by
  let : ChartedSpace (ℂ × ComplexPlane₂) SpecialPeriods.Threefold.Space :=
    SpecialPeriods.Threefold.chartedSpace
  exact normedChartedSpace_stronglyLocallyContractibleSpace
    (ℂ × ComplexPlane₂) SpecialPeriods.Threefold.Space

theorem threefold_locallyContractibleSpace :
    LocallyContractibleSpace SpecialPeriods.Threefold.Space := by
  let : StronglyLocallyContractibleSpace SpecialPeriods.Threefold.Space :=
    threefold_stronglyLocallyContractibleSpace
  exact StronglyLocallyContractibleSpace.locallyContractible

end Wikipedia.HopfProblem.ConstantSheafSingularComparison.LocalContractibility
