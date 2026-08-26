import ErdosProblems.Erdos633b.CaseFourGeometry
import ErdosProblems.Erdos633b.CaseEight
import ErdosProblems.Erdos633b.PythagoreanQuartic

/-! Full case-(4) sufficiency, including the global nonsquare exclusion. -/

namespace Erdos633b

theorem case_four_sufficient (T : Triangle) (hC : T.angle 2 = Real.pi / 3)
    (hrat : IsRational (Real.sqrt 3 * Real.tan (T.angle 0 / 2))) : HasNonsquareTiling T := by
  rcases case_four_geometric_counts T hC hrat with ht | ⟨a, b, c, ha, hb, _, he, ht⟩
  · exact ht
  · refine ⟨Sixty.commonScale a b ^ 2 * b * (a + b), ?_, ht⟩
    rw [mul_assoc]
    exact nat_nonsquare_sq_mul _ _ (Sixty.commonScale_pos a b)
      (case_four_integer_nonsquare a b c ha hb he)

theorem case_four_sufficient_reindexed (T : Triangle) (e : Equiv.Perm (Fin 3))
    (hC : T.angle (e 2) = Real.pi / 3)
    (hrat : IsRational (Real.sqrt 3 * Real.tan (T.angle (e 0) / 2))) : HasNonsquareTiling T := by
  have ht := case_four_sufficient (T.reindex e.symm)
    (by simpa only [Triangle.angle_reindex, Equiv.symm_symm] using hC)
    (by simpa only [Triangle.angle_reindex, Equiv.symm_symm] using hrat)
  exact hasNonsquareTiling_of_support_eq (T.support_reindex e.symm) ht

end Erdos633b
