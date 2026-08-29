/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayCausalMovingGlobalClosure
import ErdosProblems.Erdos599.HalfwayMovingBetaLimit
import ErdosProblems.Erdos599.DeferredLegalLimitHitClosure

/-!
# The completed causal moving-stage closure

The global causal carrier supplies the coherent maximal hammocks, reference
closure, records and markers.  Deferred legality supplies limit-hit closure.
Their composition constructs the literal small closed set and its actual
later limit stage before the interval linkage is chosen, with exact
persistent-frontier capture and absorption of the moving symmetric
difference.  No closure premise remains as an extra input.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599.Blueprint.LinkageBlueprint.CausalSection9Rows

open DirectedPath Alternating Ladder

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}

/-- Finish the actual source-order closure at the supremum of the moving
club stages.  The seed lies in the already constructed global carrier;
the future interval linkage is not an input to this theorem. -/
theorem exists_limitMoving931GlobalClosure
    (hkappa : aleph0 ≤ kappa) (hGamma : Gamma.IsNormalized)
    {seed : Set V} (hseed : #seed ≤ succ kappa)
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (hC : C.ladder = finalLadder Gamma kappa hkappa hGamma seed hseed)
    (X0 : Set V)
    (hX0 : X0 ⊆ globalCarrier Gamma kappa hkappa hGamma seed hseed)
    (hX0card : #X0 ≤ kappa) :
    Nonempty (LimitMoving931GlobalClosure C
      (globalCarrier Gamma kappa hkappa hGamma seed hseed) X0) := by
  obtain ⟨R⟩ := exists_movingBetaOmegaClosure hkappa hGamma hseed
    C hC X0 hX0 hX0card
  exact R.exists_limitClosure C.limitHitClosure

#print axioms exists_limitMoving931GlobalClosure

end Erdos599.Blueprint.LinkageBlueprint.CausalSection9Rows
