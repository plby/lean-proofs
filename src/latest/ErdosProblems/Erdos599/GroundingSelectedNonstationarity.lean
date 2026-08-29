/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingAssembly

/-!
# The final nonstationarity input for Assertion 8.22

The recursively selected Lambda paths form a finite warp whose terminals
belong to the request copy of the popular cut.  Since that request cut is a
subset of the popular cut, strong popularity of the selected warp would
contradict the defining non-strong-popularity conclusion of Theorem 8.4.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace GroundingAssembly

open DirectedPath Stationary

universe u

variable {V I : Type u} {Gamma : DWeb V}

/-- The initial indices used by the recursively selected request warp are
nonstationary.  This is the stationary-ideal input used when the selected
indices are removed at the end of Assertion 8.22. -/
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

end GroundingAssembly
end Erdos599
