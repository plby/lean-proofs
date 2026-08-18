/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.ProjectedProperizationTheorem

/-!
# Unconditional Appendix properization composition

This plugs the proved projected-properization theorem into the complete
Appendix encoding/transport chain.
-/

namespace Erdos186.CFP.HigherDimensionalCorollary

/-- The source-correct integer CFP theorem implies the source-correct
higher-dimensional corollary.  The small-cardinality branch and all scale
rounding are internal to the Appendix composition. -/
theorem nonemptyHigherDimensionalCorollary5_of_nonemptyIntegerTheorem15
    (hInteger : NonemptyIntegerTheorem15) :
    NonemptyHigherDimensionalCorollary5 :=
  nonemptyHigherDimensionalCorollary5_of_nonemptyIntegerTheorem15_of_projectedProperization
    hInteger ProjectedProperization.boxProjectedProperizationStatement

end Erdos186.CFP.HigherDimensionalCorollary

#print axioms
  Erdos186.CFP.HigherDimensionalCorollary.nonemptyHigherDimensionalCorollary5_of_nonemptyIntegerTheorem15
