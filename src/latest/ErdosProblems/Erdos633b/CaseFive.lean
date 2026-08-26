import ErdosProblems.Erdos633b.CaseFiveGeometry
import ErdosProblems.Erdos633b.CaseEight
import ErdosProblems.Erdos633b.EulerTwisted

/-! Full sufficiency for case (5), with the global nonsquare count proved by descent. -/

namespace Erdos633b

theorem case_five_sufficient (T : Triangle) (hB : T.angle 1 = 2 * T.angle 0)
    (hrat : IsRational (Real.sqrt 3 * Real.tan (T.angle 0 / 2))) : HasNonsquareTiling T := by
  obtain ⟨a, b, c, m, ha, hb, _, hm, he, ht⟩ := case_five_geometric_counts T hB hrat
  refine ⟨3 * m ^ 2 * (a + 2 * b) * (a + b), ?_, ht⟩
  have hn := nat_nonsquare_sq_mul m (3 * (a + 2 * b) * (a + b)) hm
    (case_five_integer_nonsquare a b c ha hb he)
  rw [show 3 * m ^ 2 * (a + 2 * b) * (a + b) =
    m ^ 2 * (3 * (a + 2 * b) * (a + b)) by ring]
  exact hn

theorem case_five_sufficient_reindexed (T : Triangle) (e : Equiv.Perm (Fin 3))
    (hB : T.angle (e 1) = 2 * T.angle (e 0))
    (hrat : IsRational (Real.sqrt 3 * Real.tan (T.angle (e 0) / 2))) : HasNonsquareTiling T := by
  have ht := case_five_sufficient (T.reindex e.symm)
    (by simpa only [Triangle.angle_reindex, Equiv.symm_symm] using hB)
    (by simpa only [Triangle.angle_reindex, Equiv.symm_symm] using hrat)
  exact hasNonsquareTiling_of_support_eq (T.support_reindex e.symm) ht

end Erdos633b
