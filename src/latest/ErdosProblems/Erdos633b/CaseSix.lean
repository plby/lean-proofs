import ErdosProblems.Erdos633b.CaseSixGeometry
import ErdosProblems.Erdos633b.CaseSixArithmetic

/-! Full sufficiency for case (6), with actual geometric coverage and a nonsquare count. -/

namespace Erdos633b

theorem case_six_sufficient (T : Triangle) (hB : T.angle 1 = 2 * T.angle 0)
    (hrat : IsRational (Real.sin (T.angle 0 / 2))) : HasNonsquareTiling T := by
  obtain ⟨a, b, c, ha, _, _, hac, he, ht⟩ := case_six_geometric_counts T hB hrat
  exact ⟨(c + b) * (2 * c + b), case_six_integer_nonsquare a b c ha hac he, ht⟩

theorem case_six_sufficient_reindexed (T : Triangle) (e : Equiv.Perm (Fin 3))
    (hB : T.angle (e 1) = 2 * T.angle (e 0))
    (hrat : IsRational (Real.sin (T.angle (e 0) / 2))) : HasNonsquareTiling T := by
  have ht := case_six_sufficient (T.reindex e.symm)
    (by simpa only [Triangle.angle_reindex, Equiv.symm_symm] using hB)
    (by simpa only [Triangle.angle_reindex, Equiv.symm_symm] using hrat)
  exact hasNonsquareTiling_of_support_eq (T.support_reindex e.symm) ht

end Erdos633b
