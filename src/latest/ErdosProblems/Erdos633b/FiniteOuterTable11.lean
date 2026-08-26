import ErdosProblems.Erdos633b.FiniteOuterCandidates
import ErdosProblems.Erdos633b.FiniteAngleTable11

/-! Kernel-checked finite outer-angle filters for one complete tile table. -/

namespace Erdos633b

theorem finite_outer_table_11_exhaustive :
    ∀ v ∈ finiteAngleTable11, ∀ (a : Fin v.1) (b : Fin v.1),
      FiniteOuterAdmissible v a.val b.val → (v, a.val, b.val) ∈ finiteOuterCandidates := by
  decide +kernel

end Erdos633b
