import Wikipedia.NoExoticSixSphere.ReflectionQuotientCoordinate
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# A real-line chart as a positive half-line chart

The exponential and logarithm give a genuine open partial homeomorphism from
the whole real line onto the positive part of the nonnegative half-line.
Thus interior and boundary charts can use one common topological model.
-/

noncomputable section

open Set Topology

namespace NoExoticSixSphere.InvolutionQuotient

def positiveHalfLine : OpenPartialHomeomorph ℝ HalfLine where
  toFun t := ⟨Real.exp t, (Real.exp_pos t).le⟩
  invFun y := Real.log y.val
  source := univ
  target := {y | 0 < y.val}
  map_source' t _ := Real.exp_pos t
  map_target' _ _ := mem_univ _
  left_inv' t _ := Real.log_exp t
  right_inv' _ hy := Subtype.ext (Real.exp_log hy)
  open_source := isOpen_univ
  open_target := isOpen_lt continuous_const continuous_subtype_val
  continuousOn_toFun := (Real.continuous_exp.subtype_mk _).continuousOn
  continuousOn_invFun _ hy :=
    ((Real.continuousAt_log hy.ne').comp continuous_subtype_val.continuousAt).continuousWithinAt

theorem positiveHalfLine_apply (t : ℝ) : (positiveHalfLine t).val = Real.exp t := rfl

theorem positiveHalfLine_source : positiveHalfLine.source = univ := rfl

end NoExoticSixSphere.InvolutionQuotient
