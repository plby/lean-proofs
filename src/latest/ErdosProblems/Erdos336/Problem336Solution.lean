import ErdosProblems.Erdos336.FullyPrimitiveRectifiableTheorem
import ErdosProblems.Erdos336.StableV3ConditionalFinal

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos336

/-- Erdős Problem 336: the maximal exact order of an asymptotic basis of
variable order at most `r` is asymptotic to `r² / 3`. -/
theorem problem336 : HasProblem336Value (1 / 3 : ℝ) := by
  apply problem336_of_stableHighPowerStructureV3
  apply stableHighPowerStructureV3_of_rectifiableThreeMinusThree
  apply rectifiableThreeMinusThree_of_fullyPrimitive
  exact fullyPrimitiveRectifiableThreeMinusThree

end Erdos336
