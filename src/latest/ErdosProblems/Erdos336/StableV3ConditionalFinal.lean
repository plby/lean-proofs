import ErdosProblems.Erdos336.EventualConditionalFinal
import ErdosProblems.Erdos336.WideBlockScaleAsymptotic

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos336

/-- The sole remaining V3 structural statement implies Erdős Problem 336. -/
theorem problem336_of_stableHighPowerStructureV3
    (hstruct : HasStableHighPowerStructureV3) :
    HasProblem336Value (1 / 3 : ℝ) := by
  apply problem336_of_eventual_cyclicRemovalUpperThird
  exact ⟨wideStructuralRemovalCost,
    eventually_cyclicRemovalBound_wideStructuralCost hstruct,
    tendsto_wideStructuralRemovalCost_third⟩

end Erdos336
