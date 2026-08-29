/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeEndpointBlueprint
import ErdosProblems.Erdos599.ColouredSafeHammockInsideClosure
import ErdosProblems.Erdos599.ColouredSafeWeakBlueprintTransaction

/-!
# The closed carrier needed by native endpoint replacements

The carrier has whole limiting reference closure and successor-cap endpoint
hammock closure. It need not be small, and arbitrary eligible routes need
not lie in it. Successor-cap closure instead supplies contained large
witnesses with their original filters intact.
-/

noncomputable section

namespace Erdos599.Blueprint.ColouredSafeEndpointBlueprint

open Set Cardinal Order DirectedPath Ladder LinkageBlueprint
open ColouredSafeAmbientOccurrence ColouredSafeReverseReachability
open ColouredSafeHammock ColouredSafeEndpointReference

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath} {kappa : Cardinal.{u}}
variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)} {Z : Set V}

structure ClosedCarrier (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (Z : Set V) : Prop where
  reference_closed : ClosedUnderPaths Gamma C.ladder.limitWarp Z
  endpoint_closed : ColouredSafeEndpointHammock.Closed C.ladder.limitWarp
    (ColouredSafeEndpointHammock.CapturedByStageRoof C.ladder) (succ kappa) Z

namespace ClosedCarrier

theorem pruned_reference_closed (hZ : ClosedCarrier C Z) (s : V) (e : Option V) :
    ClosedUnderPaths Gamma (reference C.ladder.limitWarp s e) Z :=
  fun p hp hmeet ↦ hZ.reference_closed p hp.1 hmeet

theorem referenceClosure_subset (hZ : ClosedCarrier C Z) {s : V} {e : Option V}
    (A : Occurrence (reference C.ladder.limitWarp s e) s) (hA : A.vertexSet ⊆ Z) :
    A.referenceClosure ⊆ Z :=
  A.referenceClosure_subset_of_closedUnderPaths (hZ.pruned_reference_closed s e) hA

theorem ordinary_hasCard_within (hZ : ClosedCarrier C Z) {s : V} {e : Option V}
    (hends : endpoints s e ⊆ Z)
    (h : HasCard (reference C.ladder.limitWarp s e) s e
      (ColouredSafeEndpointHammock.CapturedByStageRoof C.ladder s e) (succ kappa)) :
    HasCard (reference C.ladder.limitWarp s e) s e
      (fun A ↦ ColouredSafeEndpointHammock.CapturedByStageRoof C.ladder s e A ∧
        A.vertexSet ⊆ Z) (succ kappa) :=
  (hZ.endpoint_closed s e hends).1.hasCard_within C.capacity_infinite h

theorem nondegenerate_hasCard_within (hZ : ClosedCarrier C Z) {s t : V}
    (hends : endpoints s (some t) ⊆ Z)
    (h : HasCard (reference C.ladder.limitWarp s (some t)) s (some t)
      (fun A ↦ ColouredSafeEndpointHammock.CapturedByStageRoof C.ladder s (some t) A ∧
        ¬A.HasFiniteSwitchedPathTo t) (succ kappa)) :
    HasCard (reference C.ladder.limitWarp s (some t)) s (some t)
      (fun A ↦ (ColouredSafeEndpointHammock.CapturedByStageRoof C.ladder s (some t) A ∧
        ¬A.HasFiniteSwitchedPathTo t) ∧ A.vertexSet ⊆ Z) (succ kappa) :=
  ((hZ.endpoint_closed s (some t) hends).2 t rfl).hasCard_within C.capacity_infinite h

#print axioms referenceClosure_subset
#print axioms ordinary_hasCard_within
#print axioms nondegenerate_hasCard_within

end ClosedCarrier
end Erdos599.Blueprint.ColouredSafeEndpointBlueprint
