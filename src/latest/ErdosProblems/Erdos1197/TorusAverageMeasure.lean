import ErdosProblems.Erdos1197.TorusAverageIntegrable

namespace Erdos1197

open MeasureTheory
open UnitAddTorus
open MeasureTheory.Measure

variable {d : Type*} [Fintype d]

/-- The normalized Haar measure on a closed subgroup has total mass one. -/
lemma subgroup_univ_measure
    {d : Type*} [Finite d]
    (H : ClosedAddSubgroup (UnitAddTorus d)) :
    letI : Fintype d := Fintype.ofFinite d
    (addHaarMeasure (subgroupUnivPositiveCompact (α := H))) Set.univ = 1 := by
  let _ : Fintype d := Fintype.ofFinite d
  simpa [subgroupUnivPositiveCompact] using
    (addHaarMeasure_self (G := H) (K₀ := subgroupUnivPositiveCompact (α := H)))

end Erdos1197
