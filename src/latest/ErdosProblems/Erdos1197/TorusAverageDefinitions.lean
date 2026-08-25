import ErdosProblems.Erdos1197.TorusAveragePointwise

namespace Erdos1197

open MeasureTheory
open UnitAddTorus

variable {d : Type*} [Fintype d]

lemma avgOverSubgroup_norm_le (H : ClosedAddSubgroup (UnitAddTorus d))
    (f : C(UnitAddTorus d, ℂ)) :
    ‖avgOverSubgroup (d := d) H f‖ ≤ ‖f‖ := by
  refine (ContinuousMap.norm_le (f := avgOverSubgroup (d := d) H f) (norm_nonneg _)).2 ?_
  intro y
  exact avgOverSubgroup_norm_apply_le H f y

end Erdos1197
