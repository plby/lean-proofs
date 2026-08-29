/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.DeferredGroundingCanonicalPopularSeparator
import ErdosProblems.Erdos599.DeferredGroundingControls
import ErdosProblems.Erdos599.DeferredGroundingSwitchOutput

/-!
# The separator-only grounding seam for a canonical deferred ladder

The canonical deferred auxiliary cannot have the target-pure equal-index
arm.  Thus the general `SwitchPruneCompiler` interface is unnecessarily
strong here: the only remaining geometric input is the genuine separator
switch/prune output.  This file records that reduced, honest seam without
asserting that the separator output has already been constructed.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace DWeb
namespace KappaLadder
namespace Deferred

open Ladder Stationary

universe u

variable {V : Type u} {G : DWeb V} {kappa : Cardinal.{u}}

/-- For a canonical deferred ladder, a switch/prune output for every actual
popular separator is the only remaining Section 8 grounding obligation.
The target-pure equal-index alternative was eliminated before this theorem,
by `canonicalDeferredLadder_popularAuxiliary_popularSeparator_nonempty`. -/
theorem canonicalDeferredLadder_exists_hindrance_of_separatorSwitchPruneOutput
    (preferred : Stage kappa → Option V)
    (hkappa : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (hNoEnter : G.NoEdgeEnters G.source)
    (hL : IsKappaHindrance
      (canonicalDeferredLadder G kappa preferred))
    (Hseparator : ∀ S : Popular.PopularSeparator
        (popularAuxiliaryIndexed
          (canonicalDeferredLadder G kappa preferred) hL),
      Nonempty (SeparatorSwitchPruneOutput
        (canonicalDeferredLadder G kappa preferred) hL S
        (selectionControls
          (canonicalDeferredLadder G kappa preferred) hL S))) :
    ∃ W : Set G.DPath, G.IsHindrance W := by
  obtain ⟨S⟩ :=
    canonicalDeferredLadder_popularAuxiliary_popularSeparator_nonempty
      preferred hkappa huncountable hNoEnter hL
  obtain ⟨O⟩ := Hseparator S
  exact exists_hindrance_of_stationarySwitchOutput
    hL.legal.regular hL.legal.uncountable
    (IsKappaHindrance.phiGround_isStationary
      (canonicalDeferredLadder G kappa preferred) hL)
    O.toStationaryOutput

end Deferred
end KappaLadder
end DWeb
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.Deferred.canonicalDeferredLadder_exists_hindrance_of_separatorSwitchPruneOutput
