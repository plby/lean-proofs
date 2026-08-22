/-
Copyright (c) 2026 The Erdos Problems Formalization Project.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Erdos Problems Formalization Project
-/
import ErdosProblems.Erdos1165.ProfileWeightUpper
import ErdosProblems.Erdos1165.Proposition13Scales

/-!
# Proposition-scale adapter for the constrained-profile upper bound

This tiny downstream module identifies the locally isolated analytic
exponent `profileUpperDelta` with the Proposition-1.3 choice
`chosenProfileDelta`.  Keeping this adapter downstream avoids a dependency
cycle between the analytic profile proof and the final assembly.
-/

namespace Erdos1165.ProfileWeightUpper

open AppendixFirstMoment Proposition13Scales

noncomputable section

/-- The complete profile upper bound in the notation used by the final
Proposition-1.3 and pair-moment assemblies. -/
theorem constrainedProfileWeight_chosenProfileDelta_le_exp {q : ℕ}
    (hq : profileUpperTailStart ≤ q) :
    constrainedProfileWeight q chosenProfileDelta ≤
      Real.exp (-(2 * (q : ℝ)) +
        profileUpperConstant * (q : ℝ) ^ (3 / 5 : ℝ)) := by
  simpa only [profileUpperDelta, chosenProfileDelta] using
    constrainedProfileWeight_le_exp hq

end

end Erdos1165.ProfileWeightUpper
