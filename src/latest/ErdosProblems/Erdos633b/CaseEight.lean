import ErdosProblems.Erdos633b.CaseEightGeometry
import ErdosProblems.Erdos633b.EulerRational

/-! Full sufficiency for case (8), combining geometric patches with the integer descent. -/

namespace Erdos633b

theorem nat_nonsquare_sq_mul (m n : ℕ) (hm : 0 < m) (hn : ¬ IsSquare n) :
    ¬ IsSquare (m ^ 2 * n) := by
  intro hs
  apply hn
  apply Rat.isSquare_natCast_iff.mp
  apply (isSquare_sq_mul_iff (m : ℚ) n (by exact_mod_cast ne_of_gt hm)).mp
  have hh := Rat.isSquare_natCast_iff.mpr hs
  simpa only [Nat.cast_mul, Nat.cast_pow] using hh

theorem case_eight_sufficient (T : Triangle)
    (hrel : T.angle 2 = 2 * T.angle 0 + T.angle 1 / 2)
    (hrat : IsRational (Real.sqrt 3 * Real.tan (T.angle 0 / 2))) :
    HasNonsquareTiling T := by
  obtain ⟨a, b, c, ha, hb, _, he, ht⟩ := case_eight_geometric_counts T hrel hrat
  refine ⟨Sixty.commonScale a b ^ 2 * (a + b) * (2 * a + b), ?_, ht⟩
  rw [mul_assoc]
  exact nat_nonsquare_sq_mul _ _ (Sixty.commonScale_pos a b)
    (case_eight_integer_nonsquare a b c ha hb he)

theorem case_eight_sufficient_reindexed (T : Triangle) (e : Fin 3 ≃ Fin 3)
    (hrel : T.angle (e 2) = 2 * T.angle (e 0) + T.angle (e 1) / 2)
    (hrat : IsRational (Real.sqrt 3 * Real.tan (T.angle (e 0) / 2))) :
    HasNonsquareTiling T := by
  have ht := case_eight_sufficient (T.reindex e.symm)
    (by simpa only [Triangle.angle_reindex, Equiv.symm_symm] using hrel)
    (by simpa only [Triangle.angle_reindex, Equiv.symm_symm] using hrat)
  exact hasNonsquareTiling_of_support_eq (T.support_reindex e.symm) ht

end Erdos633b
