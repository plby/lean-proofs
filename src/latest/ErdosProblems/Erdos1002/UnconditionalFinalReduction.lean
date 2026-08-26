import ErdosProblems.Erdos1002.ActualGridFinalReduction
import ErdosProblems.Erdos1002.FixedAwayUnshiftedSubquadratic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Final reduction after unconditional fixed-away deletion

The fixed-away Ramanujan remainder is now discharged without an external
arithmetic hypothesis.  Thus the literal Gauss-prefix marked factorial
limits are the sole remaining input to the Erdős conclusion.
-/

namespace Erdos1002

noncomputable section

/-- Once the literal Gauss-prefix annular factorial limits are known, the
original Erdős 1002 statement follows with no further hypothesis. -/
theorem erdos1002Conclusion_of_gaussPrefix
    (hFac : GaussPrefixAnnularGridFactorialLimits) :
    Erdos1002Conclusion := by
  let ε : ℝ := 1 / 4
  have hε : 0 < ε := by
    dsimp [ε]
    norm_num
  have hεhalf : ε < 1 / 2 := by
    dsimp [ε]
    norm_num
  exact erdos1002Conclusion_of_gaussPrefix_and_fixedAway
    ε hε hεhalf hFac
      (iterated_probabilityDeletion_normalizedFixedAwayMinorRemainder_unconditional
        ε hε hεhalf)

end

end Erdos1002
