import ErdosProblems.Erdos1197.TorusAverageIntegrable

namespace Erdos1197

open MeasureTheory
open UnitAddTorus
open MeasureTheory.Measure

variable {d : Type*} [Fintype d]

/-- The normalized Haar measure on a closed subgroup has total mass one. -/
lemma subgroup_univ_measure
    (H : ClosedAddSubgroup (UnitAddTorus d)) :
    (addHaarMeasure (subgroupUnivPositiveCompact (α := H))) Set.univ = 1 := by
  simpa [subgroupUnivPositiveCompact] using
    (addHaarMeasure_self (G := H) (K₀ := subgroupUnivPositiveCompact (α := H)))

end Erdos1197
