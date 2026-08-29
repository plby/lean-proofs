/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingEqualMaximalOrderedActiveClosure
import ErdosProblems.Erdos599.GroundingEqualMaximalCollisionForest

/-!
# Root-prefix isolation in the maximal ordered active closure

The asymmetric collision-carrier condition is strong in both directions
around one active route.  A later route avoids the route's exposed grounded
parent directly.  If an earlier route met that parent, it would expose the
parent and force the current later route to avoid its own canonical initial.
Consequently the current route is the unique active route whose actual
decoded carrier meets its grounded source parent.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599

open DirectedPath Alternating

universe u

variable {V : Type u} {Gamma : DWeb V}

namespace DWeb.KappaLadder

open GroundingEqualActiveSelection
open GroundingEqualMaximalCollisionForest
open GroundingEqualOrderedActiveSelection

variable {kappa : Cardinal.{u}}

private abbrev MaximalWarp
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {q : FinitePath (EqualInput L hL).lambda.graph}
    (M : Popular.MaximalDecodedTargetPureAvoidingRestrictedXSWarp
      (EqualInput L hL)
      ((EqualInput L hL).lambda.source \ {q.start})
      (collisionCarrier (EqualInput L hL) q)) :=
  ReservedMaximalDecodedActiveSupply.toXSWarp M

private abbrev ActiveWarp
    {L : Gamma.KappaLadder kappa} (hL : L.IsKappaHindrance)
    {q : FinitePath (EqualInput L hL).lambda.graph}
    (M : Popular.MaximalDecodedTargetPureAvoidingRestrictedXSWarp
      (EqualInput L hL)
      ((EqualInput L hL).lambda.source \ {q.start})
      (collisionCarrier (EqualInput L hL) q)) :=
  maximalOrderedActiveSubwarp hL M

private def activeAsMaximal
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {q : FinitePath (EqualInput L hL).lambda.graph}
    {M : Popular.MaximalDecodedTargetPureAvoidingRestrictedXSWarp
      (EqualInput L hL)
      ((EqualInput L hL).lambda.source \ {q.start})
      (collisionCarrier (EqualInput L hL) q)}
    (p : WarpPath (ActiveWarp hL M)) : WarpPath (MaximalWarp M) :=
  ⟨p.1, p.2.1⟩

private theorem activeAsMaximal_index_eq
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {q : FinitePath (EqualInput L hL).lambda.graph}
    {M : Popular.MaximalDecodedTargetPureAvoidingRestrictedXSWarp
      (EqualInput L hL)
      ((EqualInput L hL).lambda.source \ {q.start})
      (collisionCarrier (EqualInput L hL) q)}
    (p : WarpPath (ActiveWarp hL M)) :
    warpPathIndex (L.popularAuxiliaryIndexed hL) (MaximalWarp M)
        (activeAsMaximal p) =
      warpPathIndex (L.popularAuxiliaryIndexed hL) (ActiveWarp hL M) p := by
  rfl

/-- A later active maximal route has decoded carrier disjoint from every
limiting-ladder parent exposed by an earlier active route. -/
theorem maximalActive_later_decodedCarrier_disjoint_earlier_exposedParent
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {reserved : FinitePath (EqualInput L hL).lambda.graph}
    {M : Popular.MaximalDecodedTargetPureAvoidingRestrictedXSWarp
      (EqualInput L hL)
      ((EqualInput L hL).lambda.source \ {reserved.start})
      (collisionCarrier (EqualInput L hL) reserved)}
    (p r : WarpPath (ActiveWarp hL M))
    (hrp : warpPathIndex (L.popularAuxiliaryIndexed hL) (ActiveWarp hL M) r <
      warpPathIndex (L.popularAuxiliaryIndexed hL) (ActiveWarp hL M) p)
    {Y : Gamma.DPath}
    (hY : Y ∈ GroundingSimultaneousDecode.exposedLadderPaths
      (EqualInput L hL) r.1) :
    Disjoint ((EqualInput L hL).decodedVertexCarrier p.1) Y.support := by
  apply decodedVertexCarrier_disjoint_exposedLadderPath_of_support_disjoint
    (EqualInput L hL) (L.popularAuxiliary_proxyPathsFaithful hL)
    p.1 r.1 ((ActiveWarp hL M).starts_in_source p.2) hY
  apply maximalOrderedActiveSubwarp_orderedAvoidance M p.2 r.2
  change warpPathIndex (L.popularAuxiliaryIndexed hL) (MaximalWarp M)
      (activeAsMaximal r) <
    warpPathIndex (L.popularAuxiliaryIndexed hL) (MaximalWarp M)
      (activeAsMaximal p)
  rw [activeAsMaximal_index_eq, activeAsMaximal_index_eq]
  exact hrp

/-- An active route earlier than `p` cannot meet the grounded parent of
`p`'s canonical source prefix. -/
theorem maximalActive_earlierRoute_decodedCarrier_disjoint_rootParent
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {reserved : FinitePath (EqualInput L hL).lambda.graph}
    {M : Popular.MaximalDecodedTargetPureAvoidingRestrictedXSWarp
      (EqualInput L hL)
      ((EqualInput L hL).lambda.source \ {reserved.start})
      (collisionCarrier (EqualInput L hL) reserved)}
    (r p : WarpPath (ActiveWarp hL M))
    (hrp : warpPathIndex (L.popularAuxiliaryIndexed hL) (ActiveWarp hL M) r <
      warpPathIndex (L.popularAuxiliaryIndexed hL) (ActiveWarp hL M) p)
    (R : L.CanonicalErasedRouteRootPrefix hL (ActiveWarp hL M) p) :
    Disjoint ((EqualInput L hL).decodedVertexCarrier r.1)
      R.parent.support := by
  rw [Set.disjoint_left]
  intro x hxr hxparent
  have hparentExposed : R.parent ∈
      GroundingSimultaneousDecode.exposedLadderPaths
        (EqualInput L hL) r.1 := by
    apply (EqualInput L hL).mem_exposedLadderPaths_of_mem_decodedVertexCarrier_of_mem_support
      (L.popularAuxiliary_proxyPathsFaithful hL) r.1
      ((ActiveWarp hL M).starts_in_source r.2)
      R.parent_inessential.1 hxr hxparent
  have havoid :=
    maximalActive_later_decodedCarrier_disjoint_earlier_exposedParent
      p r hrp hparentExposed
  let y := (canonicalErasedRoute (EqualInput L hL) (ActiveWarp hL M) p).initial
  have hyp : y ∈ (EqualInput L hL).decodedVertexCarrier p.1 :=
    canonicalErasedRoute_vertexSet_subset_decodedVertexCarrier
      (EqualInput L hL) (ActiveWarp hL M) p
      (canonicalErasedRoute
        (EqualInput L hL) (ActiveWarp hL M) p).initial_mem_vertexSet
  have hyparent : y ∈ R.parent.support := by
    have hfinish : R.path.finish = y := by
      simpa only [y] using R.finish_eq
    rw [← hfinish]
    exact R.support_subset R.path.finish_mem_support
  exact Set.disjoint_left.1 havoid hyp hyparent

/-- Every other active route avoids the canonical grounded source parent of
`p`. -/
theorem maximalActive_otherRoute_decodedCarrier_disjoint_rootParent
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {reserved : FinitePath (EqualInput L hL).lambda.graph}
    {M : Popular.MaximalDecodedTargetPureAvoidingRestrictedXSWarp
      (EqualInput L hL)
      ((EqualInput L hL).lambda.source \ {reserved.start})
      (collisionCarrier (EqualInput L hL) reserved)}
    (r p : WarpPath (ActiveWarp hL M)) (hrp : r ≠ p)
    (R : L.CanonicalErasedRouteRootPrefix hL (ActiveWarp hL M) p) :
    Disjoint ((EqualInput L hL).decodedVertexCarrier r.1)
      R.parent.support := by
  have hne :
      warpPathIndex (L.popularAuxiliaryIndexed hL) (ActiveWarp hL M) r ≠
        warpPathIndex (L.popularAuxiliaryIndexed hL) (ActiveWarp hL M) p := by
    intro heq
    exact hrp (warpPath_eq_of_index_eq
      (L.popularAuxiliaryIndexed hL)
      (L.popularAuxiliaryIndexed_sourceIndexed hL)
      (ActiveWarp hL M) heq)
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact maximalActive_earlierRoute_decodedCarrier_disjoint_rootParent
      r p hlt R
  · have hparentExposed : R.parent ∈
        GroundingSimultaneousDecode.exposedLadderPaths
          (EqualInput L hL) p.1 := by
      let y := (canonicalErasedRoute
        (EqualInput L hL) (ActiveWarp hL M) p).initial
      apply (EqualInput L hL).mem_exposedLadderPaths_of_mem_decodedVertexCarrier_of_mem_support
        (L.popularAuxiliary_proxyPathsFaithful hL) p.1
        ((ActiveWarp hL M).starts_in_source p.2) R.parent_inessential.1
      · exact canonicalErasedRoute_vertexSet_subset_decodedVertexCarrier
          (EqualInput L hL) (ActiveWarp hL M) p
          (canonicalErasedRoute
            (EqualInput L hL) (ActiveWarp hL M) p).initial_mem_vertexSet
      · have hfinish : R.path.finish = y := by
          simpa only [y] using R.finish_eq
        change y ∈ R.parent.support
        rw [← hfinish]
        exact R.support_subset R.path.finish_mem_support
    exact maximalActive_later_decodedCarrier_disjoint_earlier_exposedParent
      r p hgt hparentExposed

namespace GroundingEqualMaximalCollisionForest.FirstActualRootParentCollision

/-- For the maximal ordered active subwarp, the first actual collision owner
of a route's grounded source parent is the route itself. -/
theorem owner_eq_route_of_maximalActive
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {reserved : FinitePath (EqualInput L hL).lambda.graph}
    {M : Popular.MaximalDecodedTargetPureAvoidingRestrictedXSWarp
      (EqualInput L hL)
      ((EqualInput L hL).lambda.source \ {reserved.start})
      (collisionCarrier (EqualInput L hL) reserved)}
    {p : WarpPath (ActiveWarp hL M)}
    {R : L.CanonicalErasedRouteRootPrefix hL (ActiveWarp hL M) p}
    (C : FirstActualRootParentCollision p R) :
    C.owner = p := by
  by_contra hne
  have hdisj := maximalActive_otherRoute_decodedCarrier_disjoint_rootParent
    C.owner p hne R
  obtain ⟨x, hxroute, hxparent⟩ := C.owner_contact
  have hxcarrier : x ∈ (EqualInput L hL).decodedVertexCarrier C.owner.1 :=
    canonicalErasedRoute_vertexSet_subset_decodedVertexCarrier
      (EqualInput L hL) (ActiveWarp hL M) C.owner hxroute
  exact Set.disjoint_left.1 hdisj hxcarrier hxparent

end GroundingEqualMaximalCollisionForest.FirstActualRootParentCollision

/-- Immediately before an active route is switched, its canonical initial
is source-rooted and its first collision owner is itself. -/
theorem maximalActive_route_initial_sourceRooted_before_self
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {reserved : FinitePath (EqualInput L hL).lambda.graph}
    {M : Popular.MaximalDecodedTargetPureAvoidingRestrictedXSWarp
      (EqualInput L hL)
      ((EqualInput L hL).lambda.source \ {reserved.start})
      (collisionCarrier (EqualInput L hL) reserved)}
    (p : WarpPath (ActiveWarp hL M))
    (R : L.CanonicalErasedRouteRootPrefix hL (ActiveWarp hL M) p) :
    ∃ a ∈ Gamma.source,
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ canonicalErasedRepairedEdges
          (EqualInput L hL)
          (routesBeforeIndex L hL (ActiveWarp hL M)
            (warpPathIndex (L.popularAuxiliaryIndexed hL)
              (ActiveWarp hL M) p))) a
        (canonicalErasedRoute (EqualInput L hL) (ActiveWarp hL M) p).initial := by
  obtain ⟨C⟩ := exists_firstActualRootParentCollision p R
  exact C.route_initial_sourceRooted_before_self
    C.owner_eq_route_of_maximalActive

end DWeb.KappaLadder
end Erdos599

#print axioms Erdos599.DWeb.KappaLadder.maximalActive_later_decodedCarrier_disjoint_earlier_exposedParent
#print axioms Erdos599.DWeb.KappaLadder.maximalActive_otherRoute_decodedCarrier_disjoint_rootParent
#print axioms Erdos599.DWeb.KappaLadder.GroundingEqualMaximalCollisionForest.FirstActualRootParentCollision.owner_eq_route_of_maximalActive
#print axioms Erdos599.DWeb.KappaLadder.maximalActive_route_initial_sourceRooted_before_self
