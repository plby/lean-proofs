import ErdosProblems.Erdos633b.CaseEightAngles

/-! Every case-(8) input has the geometric construction with the exact square-class count.
Its arithmetic nonsquareness is still a separate unproved obligation. -/

namespace Erdos633b

theorem case_eight_geometric_counts (T : Triangle)
    (hrel : T.angle 2 = 2 * T.angle 0 + T.angle 1 / 2)
    (hrat : IsRational (Real.sqrt 3 * Real.tan (T.angle 0 / 2))) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ c ^ 2 = a ^ 2 + a * b + b ^ 2 ∧
      Nonempty (Tiling T (Sixty.commonScale a b ^ 2 * (a + b) * (2 * a + b))) := by
  have hα : T.angle 0 < Real.pi / 3 := by linarith [T.angle_sum, T.angle_pos 1]
  have hC : T.angle 2 = T.angle 0 + Real.pi / 3 := by linarith [T.angle_sum]
  have hd : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have he : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  obtain ⟨a, b, c, ha, hb, hc, habc, hparam⟩ :=
    Sixty.integral_reference_of_rational_parameter (Real.sqrt 3) hd he
      (T.angle 0) (T.angle_pos 0) hα hrat
  let U := Sixty.caseEightOuter (Real.sqrt 3) hd a b ha hb
  have hangs := Sixty.caseEightOuter_angles (Real.sqrt 3) hd he a b c ha hb hc habc
  dsimp only at hangs
  rw [hparam] at hangs
  have hu0 : U.angle 0 = T.angle 0 := hangs.1
  have hu1 : U.angle 1 = T.angle 2 := hangs.2.trans hC.symm
  have hu2 : U.angle 2 = T.angle 1 := by linarith [U.angle_sum, T.angle_sum]
  let S : Triangle := U.reindex (Equiv.swap 1 2)
  have hs (i : Fin 3) : S.angle i = T.angle i := by
    rw [Triangle.angle_reindex]
    fin_cases i
    · exact hu0
    · exact hu2
    · exact hu1
  have d := (Sixty.case_eight_integer_tiling (Real.sqrt 3) hd he a b c ha hb hc habc).reindexOuter
    (Equiv.swap 1 2)
  exact ⟨a, b, c, ha, hb, hc, habc, ⟨d.transportAngles hs⟩⟩

end Erdos633b
