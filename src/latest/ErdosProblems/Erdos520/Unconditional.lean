import ErdosProblems.Erdos520.Final
import ErdosProblems.Erdos520.HarperUnconditionalInitialMoment

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Erdos
namespace Problem520

/-!
# Premise-free resolution of Erdős #520

The Harper initial moment, the effective prime estimates, the Caich residual
terms, and the Lau--Tenenbaum--Wu interpolation have all been proved inside
the development.  This file exposes the resulting public zero-premise
endpoints.
-/

/-- The critical `1/4 + η` upper bound with every analytic input discharged. -/
theorem criticalUpperBound_unconditional :
    CriticalUpperBound μ partialSum :=
  criticalUpperBound_of_harper
    harperRademacherInitialMomentStatement_unconditional

/-- Premise-free negative answer to Erdős #520: the proposed LIL
normalization converges almost surely to zero. -/
theorem erdos520Disproof_unconditional : Erdos520Disproof :=
  zeroLIL_of_criticalUpperBound criticalUpperBound_unconditional

/-- In particular, no positive limiting LIL constant exists at Erdős's
normalization. -/
theorem erdos520NoPositiveConstant_unconditional :
    Erdos520NoPositiveConstant :=
  erdos520NoPositiveConstant_of_disproof erdos520Disproof_unconditional

end Problem520
end Erdos

#print axioms Erdos.Problem520.criticalUpperBound_unconditional
#print axioms Erdos.Problem520.erdos520Disproof_unconditional
#print axioms Erdos.Problem520.erdos520NoPositiveConstant_unconditional
