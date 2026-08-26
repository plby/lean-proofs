import ErdosProblems.Erdos336.RootSemicircleInterval

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos336

open scoped Real

lemma circle_mem_centeredArc_pi_div_two_iff_re_pos (z : Circle) :
    z ∈ Circle.centeredArc (Real.pi / 2) ↔ 0 < (z : ℂ).re := by
  rw [Circle.mem_centeredArc (by linarith [Real.pi_pos])]
  have hto : ((Complex.arg (z : ℂ) : ℝ) : Real.Angle).toReal =
      Complex.arg (z : ℂ) := by
    rw [Real.Angle.toReal_coe_eq_self_iff]
    exact ⟨Complex.neg_pi_lt_arg _, Complex.arg_le_pi _⟩
  have hz0 : (z : ℂ) ≠ 0 := Circle.coe_ne_zero z
  have hcos : Real.cos (Complex.arg (z : ℂ)) = (z : ℂ).re := by
    rw [Complex.cos_arg hz0]
    simp
  calc
    |Complex.arg (z : ℂ)| < Real.pi / 2 ↔
        |((Complex.arg (z : ℂ) : ℝ) : Real.Angle).toReal| <
          Real.pi / 2 := by rw [hto]
    _ ↔ 0 < ((Complex.arg (z : ℂ) : ℝ) : Real.Angle).cos :=
      Real.Angle.cos_pos_iff_abs_toReal_lt_pi_div_two.symm
    _ ↔ 0 < Real.cos (Complex.arg (z : ℂ)) := by
      rw [Real.Angle.cos_coe]
    _ ↔ 0 < (z : ℂ).re := by rw [hcos]

end Erdos336
