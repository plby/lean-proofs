import Wikipedia.HopfProblem.ThreefoldHomologyFinitenessCuspHeight
import Wikipedia.HopfProblem.CuspTopology
import Wikipedia.HopfProblem.ComplexRealManifold

/-!
# Topological and real-smooth properties of the original full cusp

The native cusp quotient is Hausdorff, second countable, and sigma compact.
Its original complex quotient atlas is also real smooth by restriction of
scalars.  The atlas is used only locally in these proofs; no global charted
space instance or replacement topology is introduced.
-/

noncomputable section

open scoped ContDiff

namespace Wikipedia.HopfProblem.CuspCoinvariantExtension.Phase

open ThreefoldHomologyFinitenessCusp

variable (D : SpecialPeriods.CuspFamily.Data)

/-- The original cusp quotient has its native Hausdorff topology. -/
theorem native_t2Space : T2Space (FullSpace D) :=
  CuspQuotient.quotient_t2Space D.correction D.radius D.radius_pos D.radius_lt_one
    D.holomorphic D.smallDrift

/-- Second countability follows from the actual open covering projection. -/
theorem native_secondCountable : SecondCountableTopology (FullSpace D) :=
  CuspQuotient.quotient_secondCountable D.correction D.radius D.radius_pos D.radius_lt_one
    D.holomorphic D.smallDrift

/-- The actual local charts and second countability give sigma compactness. -/
theorem native_sigmaCompactSpace : SigmaCompactSpace (FullSpace D) := by
  let := CuspQuotient.chartedSpace D.correction D.radius D.radius_pos D.radius_lt_one
    D.holomorphic D.smallDrift
  let : LocallyCompactSpace (FullSpace D) :=
    ChartedSpace.locallyCompactSpace (ToricCharts.CoordinateSpace 3) (FullSpace D)
  let := native_secondCountable D
  infer_instance

/-- Restriction of scalars makes the unchanged original cusp atlas real smooth. -/
theorem native_isManifold_real :
    letI := CuspQuotient.chartedSpace D.correction D.radius D.radius_pos D.radius_lt_one
      D.holomorphic D.smallDrift
    IsManifold (modelWithCornersSelf ℝ (ToricCharts.CoordinateSpace 3)) ∞ (FullSpace D) := by
  let := CuspQuotient.chartedSpace D.correction D.radius D.radius_pos D.radius_lt_one
    D.holomorphic D.smallDrift
  let := CuspQuotient.isManifold D.correction D.radius D.radius_pos D.radius_lt_one
    D.holomorphic D.smallDrift
  exact complexManifold_isRealManifold (FullSpace D) ∞

end Wikipedia.HopfProblem.CuspCoinvariantExtension.Phase
