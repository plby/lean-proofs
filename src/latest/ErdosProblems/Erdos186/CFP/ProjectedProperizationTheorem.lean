/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.ProjectedProperizationAssembly
import ErdosProblems.Erdos186.CFP.HigherDimensionalCorollary

/-!
# The box projected-properization statement

This discharges the final Lemma 2.27 boundary in the Appendix composition.
-/

namespace Erdos186.CFP.ProjectedProperization

noncomputable section

/-- Uniform projected properization for box dehomogenization. -/
theorem boxProjectedProperizationStatement :
    HigherDimensionalCorollary.BoxProjectedProperizationStatement := by
  intro D
  refine ⟨projectionFactor D, projectionFactor_pos D, ?_⟩
  intro d s k loss scaleNum scaleDen B A W hk
  exact exists_data_boxDehomogenize B A W hk

end

end Erdos186.CFP.ProjectedProperization

#print axioms
  Erdos186.CFP.ProjectedProperization.boxProjectedProperizationStatement
