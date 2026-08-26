import ErdosProblems.Erdos633b.EulerTwisted

/-! The exact rational-function exclusions D5 and D8, with their geometric domains. -/

namespace Erdos633b

theorem caseFiveFactor_nonsquare (t : ℚ) (ht : 0 < t) (ht3 : t < 1 / 3) :
    ¬ IsSquare (caseFiveFactor t) := by
  intro hs
  let a := 4 * t
  let b := (1 - 3 * t) * (1 + t)
  let c := 1 + 3 * t ^ 2
  have ha : 0 < a := mul_pos (by norm_num) ht
  have hb : 0 < b := mul_pos (by linarith) (by linarith)
  have he : c ^ 2 = a ^ 2 + a * b + b ^ 2 := by dsimp [a, b, c]; ring
  apply case_five_rational_nonsquare a b c ha hb he
  have hid : 3 * (a + 2 * b) * (a + b) =
      (3 * (t - 1) * (3 * t + 1)) ^ 2 * caseFiveFactor t := by
    dsimp [a, b, caseFiveFactor]
    field_simp [show t - 1 ≠ 0 by linarith, show 3 * t + 1 ≠ 0 by linarith]
    ring
  rw [hid]
  exact (IsSquare.sq _).mul hs

theorem caseEightFactor_nonsquare (t : ℚ) (ht : 0 < t) (ht3 : t < 1 / 3) :
    ¬ IsSquare (caseEightFactor t) := by
  intro hs
  let a := 4 * t
  let b := (1 - 3 * t) * (1 + t)
  let c := 1 + 3 * t ^ 2
  have ha : 0 < a := mul_pos (by norm_num) ht
  have hb : 0 < b := mul_pos (by linarith) (by linarith)
  have he : c ^ 2 = a ^ 2 + a * b + b ^ 2 := by dsimp [a, b, c]; ring
  apply case_eight_rational_nonsquare a b c ha hb he
  have hid : (a + b) * (2 * a + b) =
      ((t - 1) * (3 * t + 1)) ^ 2 * caseEightFactor t := by
    dsimp [a, b, caseEightFactor]
    field_simp [show t - 1 ≠ 0 by linarith, show 3 * t + 1 ≠ 0 by linarith]
    ring
  rw [hid]
  exact (IsSquare.sq _).mul hs

end Erdos633b
