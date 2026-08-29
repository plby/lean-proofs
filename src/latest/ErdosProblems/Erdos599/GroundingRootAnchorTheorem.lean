/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingNormalizedTheorem
import ErdosProblems.Erdos599.GroundingPreStoppedRootAnchorReduction

/-!
# Final grounding interface after root-anchor reduction

Once every auxiliary control exit and every blockable fragment-parent
initial is rooted, the pre-stopped root classifier has only three genuine
outcomes.  This file exposes that reduced separator interface directly at
the final grounding theorem: the normalized finite backward switch and the
two selected-edge collisions on a blocking prefix.
-/

noncomputable section

open Set

namespace Erdos599
namespace DWeb.KappaLadder

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

/-- The separator-side construction after control exits and limiting-ladder
parent initials have been rooted.  Its remaining root repair sees only the
three constructors of `AnchorReducedRootFailureOutcome`. -/
structure RootAnchorPreStoppedRepairs
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance) where
  controlRooted : ∀
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    (R : L.UnusedGroundedRecord hL S)
    (c : GroundingErasedDecode.ControlRequest
      (L.popularAuxiliaryInput hL.legal) S.cut),
    ∃ a ∈ Gamma.source \ {R.record.initial},
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈
          L.assertion822ReservedPreStoppedEdges hL S R) a c.1
  parentRooted : ∀
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    (R : L.UnusedGroundedRecord hL S)
    (P : (L.popularAuxiliaryInput hL.legal).Fragment),
    P ∈ GroundingCut.blockableG0
        (L.popularAuxiliaryInput hL.legal) S.cut →
      ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈
            L.assertion822ReservedPreStoppedEdges hL S R)
          a P.parent.initial
  root : ∀
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    (R : L.UnusedGroundedRecord hL S)
    (O : L.Assertion822PreStoppedRootObstruction hL S R),
    O.AnchorReducedRootFailureOutcome →
      ∃ W : Set Gamma.DPath, Gamma.IsHindrance W
  boundary : ∀
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    (R : L.UnusedGroundedRecord hL S)
    (O : L.Assertion822PreStoppedBoundaryObstruction hL S R),
    O.BackwardNormalizedTerminalFailureOutcome →
      ∃ W : Set Gamma.DPath, Gamma.IsHindrance W

/-- Combine the stationary equal handler with the root-anchor-reduced
separator compiler. -/
theorem exists_hindrance_of_targetPureEqualGrounding_and_rootAnchorRepairs
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (equalGrounding : ∀
      (P : Popular.XSWarp
        (L.popularAuxiliaryInput hL.legal).lambda
        (L.popularAuxiliaryInput hL.legal).lambda.target),
      (∀ p (hp : p ∈ P.paths),
        (L.popularAuxiliaryInput hL.legal).IsTargetPure p) →
      Stationary.IsStationaryBelow kappa
        (Popular.initialIndicesOf (L.popularAuxiliaryIndexed hL)
          ((L.popularAuxiliaryIndexed hL).equalSubwarp P).paths
          ((L.popularAuxiliaryIndexed hL).equalSubwarp P).starts_in_source) →
      ∃ W : Set Gamma.DPath, Gamma.IsHindrance W)
    (repairs : RootAnchorPreStoppedRepairs L hL) :
    ∃ W : Set Gamma.DPath, Gamma.IsHindrance W := by
  apply
    L.exists_hindrance_of_targetPureEqualGrounding_and_assertion822_or_hindrance
      hL equalGrounding
  intro S
  exact L.assertion822Output_or_hindrance_of_preStoppedRootAnchorRepairs
    hL S (repairs.controlRooted S) (repairs.parentRooted S)
      (repairs.root S) (repairs.boundary S)

end DWeb.KappaLadder
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.exists_hindrance_of_targetPureEqualGrounding_and_rootAnchorRepairs
