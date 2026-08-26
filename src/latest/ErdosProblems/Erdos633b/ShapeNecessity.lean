import ErdosProblems.Erdos633b.CaseSevenNecessity
import ErdosProblems.Erdos633b.GroupTwoNecessity
import ErdosProblems.Erdos633b.ReptilingOrdering

/-! Convert each of the six explicit non-reptiling shapes, with commensurable
reference sides, to the exact eight-case conditions. Exhaustiveness of these
shapes and side commensurability are not assumed as global facts. -/

namespace Erdos633b

theorem case_six_of_groupOne_shape (S T : Triangle) (hs : S.RationalSides)
    (h0 : T.angle 0 = S.angle 0) (h1 : T.angle 1 = 2 * S.angle 0)
    (h2 : T.angle 2 = 2 * S.angle 1) : EightCases T := by
  have hrel : 3 * S.angle 0 + 2 * S.angle 1 = Real.pi := by
    have ht := T.angle_sum
    rw [h0, h1, h2] at ht
    linarith
  have hrat : IsRational (Real.sin (S.angle 0 / 2)) := by
    obtain ⟨q, hq⟩ := S.groupOne_parameter_rational hrel hs
    refine ⟨q / 2, ?_⟩
    push_cast
    linarith
  refine ⟨Equiv.refl _, ?_⟩
  right; right; right; right; right; left
  exact ⟨by simp only [Equiv.refl_apply, h0, h1], by simpa only [Equiv.refl_apply, h0] using hrat⟩

theorem case_five_of_groupTwo_shape (S T : Triangle) (hs : S.RationalSides)
    (hg : S.angle 2 = 2 * Real.pi / 3)
    (h0 : T.angle 0 = S.angle 0) (h1 : T.angle 1 = 2 * S.angle 0) : EightCases T := by
  refine ⟨Equiv.refl _, ?_⟩
  right; right; right; right; left
  exact ⟨by simp only [Equiv.refl_apply, h0, h1],
    by simpa only [Equiv.refl_apply, h0] using S.groupTwo_half_parameter_rational hg hs⟩

theorem case_eight_of_groupTwo_shape (S T : Triangle) (hs : S.RationalSides)
    (hg : S.angle 2 = 2 * Real.pi / 3)
    (h0 : T.angle 0 = S.angle 0) (h1 : T.angle 1 = 2 * S.angle 1)
    (h2 : T.angle 2 = 2 * S.angle 0 + S.angle 1) : EightCases T := by
  refine ⟨Equiv.refl _, ?_⟩
  right; right; right; right; right; right; right
  refine ⟨?_, ?_⟩
  · simp only [Equiv.refl_apply, h0, h1, h2]
    ring
  · simpa only [Equiv.refl_apply, h0] using S.groupTwo_half_parameter_rational hg hs

theorem case_four_of_groupTwo_third_shape (S T : Triangle) (hs : S.RationalSides)
    (hg : S.angle 2 = 2 * Real.pi / 3)
    (h0 : T.angle 0 = S.angle 0) (h1 : T.angle 1 = S.angle 0 + S.angle 1) :
    EightCases T := by
  have hsum : S.angle 0 + S.angle 1 = Real.pi / 3 := by linarith [S.angle_sum]
  refine ⟨Equiv.swap 1 2, ?_⟩
  right; right; right; left
  simpa [Equiv.swap_apply_def, h0, h1, hsum] using
    And.intro (h1.trans hsum) (S.groupTwo_half_parameter_rational hg hs)

theorem case_four_of_groupTwo_fourth_shape (S T : Triangle) (hs : S.RationalSides)
    (hg : S.angle 2 = 2 * Real.pi / 3)
    (h0 : T.angle 0 = 2 * S.angle 0) (h2 : T.angle 2 = S.angle 0 + S.angle 1) :
    EightCases T := by
  have hsum : S.angle 0 + S.angle 1 = Real.pi / 3 := by linarith [S.angle_sum]
  refine ⟨Equiv.refl _, ?_⟩
  right; right; right; left
  exact ⟨h2.trans hsum,
    by simpa only [Equiv.refl_apply, h0] using S.groupTwo_double_half_parameter_rational hg hs⟩

end Erdos633b
