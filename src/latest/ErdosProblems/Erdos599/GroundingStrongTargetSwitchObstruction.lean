/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingStrongTargetSwitch
import ErdosProblems.Erdos599.SafeSwitching

/-!
# A seed collision obstructs the current strong-target closure

`StrongTargetSwitch.routes` is combined by set union.  Consequently adding
more routes cannot cancel a collision between two seed edges which are not
edges of the reference ladder: both edges survive the symmetric difference.
This file isolates the resulting necessary condition on any constructor.

In particular a sound equal-stage construction must first thin or replace
the seed family.  Merely closing a route set while retaining every canonical
seed route cannot repair a route--route degree collision.
-/

noncomputable section

open Set

namespace Erdos599
namespace DWeb

open _root_.Erdos599.DirectedPath

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace KappaLadder.StrongTargetSwitch

variable {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
  {P : Popular.XSWarp
    (L.popularAuxiliaryInput hL.legal).lambda
    (L.popularAuxiliaryInput hL.legal).lambda.target}

/-- Two distinct non-ladder seed predecessors of one vertex make the
current all-seeds `StrongTargetSwitch` structure uninhabitable.  Extra
closure routes cannot remove either edge from a set union. -/
theorem not_nonempty_of_seed_incoming_collision
    {x y z : V} (hxy : x ≠ y)
    (hxSeed : (x, z) ∈ routeEdges L hL P)
    (hySeed : (y, z) ∈ routeEdges L hL P)
    (hxBase : (x, z) ∉ Alternating.familyEdges
      (L.popularAuxiliaryInput hL.legal).ladder.paths)
    (hyBase : (y, z) ∉ Alternating.familyEdges
      (L.popularAuxiliaryInput hL.legal).ladder.paths) :
    ¬ Nonempty (L.StrongTargetSwitch hL P) := by
  rintro ⟨S⟩
  have hxClosed : (x, z) ∈ closedRouteEdges S.routes :=
    routeEdges_subset_closedRouteEdges S hxSeed
  have hyClosed : (y, z) ∈ closedRouteEdges S.routes :=
    routeEdges_subset_closedRouteEdges S hySeed
  have hxSwitched : (x, z) ∈ closedSwitchedEdges L hL S.routes :=
    Or.inr ⟨hxClosed, hxBase⟩
  have hySwitched : (y, z) ∈ closedSwitchedEdges L hL S.routes :=
    Or.inr ⟨hyClosed, hyBase⟩
  have hxFamily : (x, z) ∈ Alternating.familyEdges S.family := by
    rw [S.realized.2.1]
    exact hxSwitched
  have hyFamily : (y, z) ∈ Alternating.familyEdges S.family := by
    rw [S.realized.2.1]
    exact hySwitched
  exact hxy
    (Alternating.IsWarp.familyEdges_biUnique S.realized.1 |>.1
      hxFamily hyFamily)

/-- The outgoing analogue: two distinct non-ladder seed successors of one
vertex also obstruct every all-seeds closure. -/
theorem not_nonempty_of_seed_outgoing_collision
    {x y z : V} (hyz : y ≠ z)
    (hySeed : (x, y) ∈ routeEdges L hL P)
    (hzSeed : (x, z) ∈ routeEdges L hL P)
    (hyBase : (x, y) ∉ Alternating.familyEdges
      (L.popularAuxiliaryInput hL.legal).ladder.paths)
    (hzBase : (x, z) ∉ Alternating.familyEdges
      (L.popularAuxiliaryInput hL.legal).ladder.paths) :
    ¬ Nonempty (L.StrongTargetSwitch hL P) := by
  rintro ⟨S⟩
  have hyClosed : (x, y) ∈ closedRouteEdges S.routes :=
    routeEdges_subset_closedRouteEdges S hySeed
  have hzClosed : (x, z) ∈ closedRouteEdges S.routes :=
    routeEdges_subset_closedRouteEdges S hzSeed
  have hySwitched : (x, y) ∈ closedSwitchedEdges L hL S.routes :=
    Or.inr ⟨hyClosed, hyBase⟩
  have hzSwitched : (x, z) ∈ closedSwitchedEdges L hL S.routes :=
    Or.inr ⟨hzClosed, hzBase⟩
  have hyFamily : (x, y) ∈ Alternating.familyEdges S.family := by
    rw [S.realized.2.1]
    exact hySwitched
  have hzFamily : (x, z) ∈ Alternating.familyEdges S.family := by
    rw [S.realized.2.1]
    exact hzSwitched
  exact hyz
    (Alternating.IsWarp.familyEdges_biUnique S.realized.1 |>.2
      hyFamily hzFamily)

#print axioms not_nonempty_of_seed_incoming_collision
#print axioms not_nonempty_of_seed_outgoing_collision

end KappaLadder.StrongTargetSwitch
end DWeb
end Erdos599
