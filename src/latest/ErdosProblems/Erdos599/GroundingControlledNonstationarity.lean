/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingControlledAssembly

/-!
# Nonstationarity of the controlled grounding warp

The controlled transversal has the same terminal set as the raw request
transversal.  Since that set is contained in the popular separator, the
separator's failure of strong popularity makes the source-index set of the
controlled warp nonstationary.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace GroundingControlledAssembly

open DirectedPath Stationary

universe u

variable {V I : Type u} {Gamma : DWeb V}

/-- The controlled request warp uses only a nonstationary set of source
indices.  This is the stationary-ideal input in the last step of Assertion
8.22. -/
theorem selectedWarp_initialIndices_nonstationary
    {L : PopularAuxiliary.Input Gamma I} {kappa : Cardinal.{u}}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S) :
    ¬ IsStationaryBelow kappa
      (Popular.initialIndicesOf U (selectedWarp U S K).paths
        (selectedWarp U S K).starts_in_source) := by
  exact PopularSwitching.initialIndices_nonstationary_of_warp_to_subset
    U (selectedWarp U S K) GroundingSelection.requestCut_subset_cut
      S.not_strongly_popular

end GroundingControlledAssembly
end Erdos599

