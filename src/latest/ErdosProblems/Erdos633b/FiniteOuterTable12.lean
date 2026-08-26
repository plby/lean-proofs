import ErdosProblems.Erdos633b.FiniteOuterCandidates
import ErdosProblems.Erdos633b.FiniteAngleTable12

/-! Kernel-checked finite outer-angle filters for one complete tile table. -/

namespace Erdos633b

theorem finite_outer_table_12_exhaustive :
    ∀ v ∈ finiteAngleTable12, ∀ (a : Fin v.1) (b : Fin v.1),
      FiniteOuterAdmissible v a.val b.val → (v, a.val, b.val) ∈ finiteOuterCandidates := by
  decide +kernel

end Erdos633b
