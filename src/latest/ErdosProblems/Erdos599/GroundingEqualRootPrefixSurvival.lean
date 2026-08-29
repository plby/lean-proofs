/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingEqualOrderedActiveSelection

/-!
# Ordered survival of equal-stage source prefixes

The ordered equal-stage selection is asymmetric: a later selected route avoids
every limiting-ladder component exposed by an earlier selected route.  This is
nevertheless enough to show that no route *earlier* than `q` can meet the
grounded parent of `q`'s canonical source prefix.  Indeed, such a meeting would
expose that parent to the earlier route; the avoidance invariant would then
force `q`'s decoded carrier to avoid the parent, contrary to the common
canonical initial vertex.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599

open DirectedPath Alternating

universe u

variable {V : Type u} {Gamma : DWeb V}

namespace DWeb.KappaLadder

open GroundingEqualActiveSelection

variable {kappa : Cardinal.{u}}
variable {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
variable {P : Popular.XSWarp
  (L.popularAuxiliaryInput hL.legal).lambda
  (L.popularAuxiliaryInput hL.legal).lambda.target}

namespace OrderedReservedStationaryDiagonalEqualSelection

/-- A route earlier than `q` cannot meet the grounded parent of `q`'s
canonical source prefix. -/
theorem earlierRoute_decodedCarrier_disjoint_rootPrefix_parent
    (S : L.OrderedReservedStationaryDiagonalEqualSelection hL P)
    (r q : WarpPath S.routes)
    (hrq : warpPathIndex (L.popularAuxiliaryIndexed hL) S.routes r <
      warpPathIndex (L.popularAuxiliaryIndexed hL) S.routes q)
    (R : L.CanonicalErasedRouteRootPrefix hL
      ((L.popularAuxiliaryIndexed hL).equalSubwarp S.base)
      ⟨q.1, S.routes_subset_equalBase q.2⟩) :
    Disjoint
      ((L.popularAuxiliaryInput hL.legal).decodedVertexCarrier r.1)
      R.parent.support := by
  let J := L.popularAuxiliaryInput hL.legal
  let U := L.popularAuxiliaryIndexed hL
  let Q := U.equalSubwarp S.base
  let qQ : WarpPath Q := ⟨q.1, S.routes_subset_equalBase q.2⟩
  rw [Set.disjoint_left]
  intro x hxr hxparent
  have hparentExposed : R.parent ∈
      GroundingSimultaneousDecode.exposedLadderPaths J r.1 := by
    apply J.mem_exposedLadderPaths_of_mem_decodedVertexCarrier_of_mem_support
      (L.popularAuxiliary_proxyPathsFaithful hL) r.1
      (S.routes.starts_in_source r.2) R.parent_inessential.1 hxr hxparent
  have havoid := S.routes_later_decodedCarrier_disjoint_earlier_exposedParent
    q.2 r.2 hrq hparentExposed
  let y := (canonicalErasedRoute J Q qQ).initial
  have hyq : y ∈ J.decodedVertexCarrier q.1 := by
    exact canonicalErasedRoute_vertexSet_subset_decodedVertexCarrier J Q qQ
      (canonicalErasedRoute J Q qQ).initial_mem_vertexSet
  have hyparent : y ∈ R.parent.support := by
    have hfinish : R.path.finish = y := by
      simpa only [y, J, Q, qQ] using R.finish_eq
    rw [← hfinish]
    exact R.support_subset R.path.finish_mem_support
  exact Set.disjoint_left.1 havoid hyq hyparent

/-- Every selected route other than `q` avoids the grounded parent of `q`'s
canonical source prefix. -/
theorem otherRoute_decodedCarrier_disjoint_rootPrefix_parent
    (S : L.OrderedReservedStationaryDiagonalEqualSelection hL P)
    (r q : WarpPath S.routes) (hrq : r ≠ q)
    (R : L.CanonicalErasedRouteRootPrefix hL
      ((L.popularAuxiliaryIndexed hL).equalSubwarp S.base)
      ⟨q.1, S.routes_subset_equalBase q.2⟩) :
    Disjoint
      ((L.popularAuxiliaryInput hL.legal).decodedVertexCarrier r.1)
      R.parent.support := by
  have hne : warpPathIndex (L.popularAuxiliaryIndexed hL) S.routes r ≠
      warpPathIndex (L.popularAuxiliaryIndexed hL) S.routes q := by
    intro heq
    exact hrq (warpPath_eq_of_index_eq
      (L.popularAuxiliaryIndexed hL)
      (L.popularAuxiliaryIndexed_sourceIndexed hL) S.routes heq)
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact S.earlierRoute_decodedCarrier_disjoint_rootPrefix_parent
      r q hlt R
  · exact S.laterRoute_decodedCarrier_disjoint_rootPrefix_parent
      r q hgt R

/-- The first route whose decoded carrier meets `q`'s grounded root parent is
`q` itself. -/
theorem FirstRootParentCollision.owner_eq_route
    {S : L.OrderedReservedStationaryDiagonalEqualSelection hL P}
    {q : WarpPath S.routes}
    {R : L.CanonicalErasedRouteRootPrefix hL
      ((L.popularAuxiliaryIndexed hL).equalSubwarp S.base)
      ⟨q.1, S.routes_subset_equalBase q.2⟩}
    (C : FirstRootParentCollision S q R) : C.owner = q := by
  by_contra hne
  have hdisj := S.otherRoute_decodedCarrier_disjoint_rootPrefix_parent
    C.owner q hne R
  obtain ⟨x, hxowner, hxparent⟩ := C.owner_contact
  exact Set.disjoint_left.1 hdisj hxowner hxparent

end OrderedReservedStationaryDiagonalEqualSelection
end DWeb.KappaLadder
end Erdos599

#print axioms Erdos599.DWeb.KappaLadder.OrderedReservedStationaryDiagonalEqualSelection.earlierRoute_decodedCarrier_disjoint_rootPrefix_parent
#print axioms Erdos599.DWeb.KappaLadder.OrderedReservedStationaryDiagonalEqualSelection.otherRoute_decodedCarrier_disjoint_rootPrefix_parent
#print axioms Erdos599.DWeb.KappaLadder.OrderedReservedStationaryDiagonalEqualSelection.FirstRootParentCollision.owner_eq_route
