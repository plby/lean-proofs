/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.TerminalFailureSplit

/-!
# Deterministic terminal controls imply the KSSS outside packing

This file packages the exact deterministic endpoint of the probabilistic
cover-down.  Once the constrained greedy state is exhausted, uniform strict
bounds on selected vertex stars and rooted active threats rule out every
pair-indexed count failure, provided the fixed loss budget fits in the
ambient vertex set.
-/

namespace Erdos207

open Finset

noncomputable section

/-- An exhausted invariant state satisfying the two terminal cutoffs already
gives the outside packing required by the KSSS deterministic reduction. -/
theorem hasKSSSOutsidePacking_of_exhausted_terminalControls
    {V : Type*} [Fintype V] [DecidableEq V]
    {q d r : ℕ} {H : SimpleGraph V} [DecidableRel H.Adj]
    {X : Finset V} {B : TripleSystemOn V} {S : GreedyStateOn V}
    (hInv : AbsorberGreedyInvariant
      (absorberErdosForbiddenConfigurationsOn q B)
      (outsideAvailableTriangles H B) S)
    (hexhausted : S.available = ∅)
    (hbudget : ∀ u v : V, u ≠ v → ¬H.Adj u v →
      H.degree u + H.degree v + B.card + (4 * d + r * q) ≤
        Fintype.card V - 2)
    (hstar : ∀ v : V, (triplesThrough S.chosen v).card < d)
    (hroot : ∀ e : DistinctPair V,
      (rootedActiveForbiddenConfigurations
        (absorberErdosForbiddenConfigurationsOn q B)
        S.chosen e.1.1 e.1.2).card < r) :
    HasKSSSOutsidePacking q H X B S.chosen := by
  apply hasKSSSOutsidePacking_of_countGoodState hInv
  apply countGoodState_of_exhausted_of_avoids_failures hexhausted
  intro e hfail
  have hbad := terminalStarRootBadAt_of_countFailure
    hInv.1.1 hbudget hfail
  rcases hbad with hu | hv | hr
  · exact (not_le_of_gt (hstar e.1.1)) hu
  · exact (not_le_of_gt (hstar e.1.2)) hv
  · exact (not_le_of_gt (hroot e)) hr

end

end Erdos207
