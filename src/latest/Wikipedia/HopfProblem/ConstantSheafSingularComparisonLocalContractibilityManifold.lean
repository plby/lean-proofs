import Wikipedia.HopfProblem.ConstantSheafSingularComparisonLocalContractibilityCharts
import Wikipedia.HopfProblem.ConstantSheafSingularComparisonLocalContractibilityNormed

/-!
# Local contractibility of native normed-space atlases

The model's genuine contractible metric-ball basis transfers through the
original charts. Neither finite dimensionality nor completeness nor an
additional differentiability hypothesis is needed for this topological
consequence of a charted-space structure.
-/

noncomputable section

namespace Wikipedia.HopfProblem.ConstantSheafSingularComparison.LocalContractibility

/-- Every native atlas modeled on a real seminormed vector space gives
a genuine basis of contractible neighborhoods. -/
theorem normedChartedSpace_stronglyLocallyContractibleSpace (E M : Type*)
    [SeminormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] : StronglyLocallyContractibleSpace M := by
  let : StronglyLocallyContractibleSpace E := normedSpace_stronglyLocallyContractibleSpace E
  exact chartedSpace_stronglyLocallyContractibleSpace E M

/-- Classical local contractibility follows in the original topology. -/
theorem normedChartedSpace_locallyContractibleSpace (E M : Type*)
    [SeminormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] : LocallyContractibleSpace M := by
  let : StronglyLocallyContractibleSpace M :=
    normedChartedSpace_stronglyLocallyContractibleSpace E M
  exact StronglyLocallyContractibleSpace.locallyContractible

end Wikipedia.HopfProblem.ConstantSheafSingularComparison.LocalContractibility
