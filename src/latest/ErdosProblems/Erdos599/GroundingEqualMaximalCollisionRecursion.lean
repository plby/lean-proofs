/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingEqualMaximalCollisionForest

/-!
# Deterministic well-founded collision nodes for the equal active closure

The maximal decoded family supplies a canonical well-founded absorption
forest after making harmless classical choices.  A node stores a grounded
source parent, its least actual route owner, and a literal point of the
corrected `BB` which lies on that parent and is source-rooted before the
owner is processed.

The owner is either the node route itself or has strictly smaller source
index.  The final theorem in this file is the induction principle used by
the pre-stopped compiler: self transactions and absorption by a completed
earlier owner suffice for every route.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599

open DirectedPath Alternating

universe u

variable {V : Type u} {Gamma : DWeb V}

namespace DWeb.KappaLadder
namespace GroundingEqualMaximalCollisionRecursion

open GroundingEqualActiveSelection
open GroundingEqualMaximalCollisionForest

variable {kappa : Cardinal.{u}}
variable {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
variable {W : Popular.XSWarp
  (L.popularAuxiliaryInput hL.legal).lambda
  (L.popularAuxiliaryInput hL.legal).lambda.target}

/-- All data at one selected route needed by the ordered absorption
recursion.  In particular `stop` is the literal corrected-boundary witness,
not an abstract representative of its component. -/
structure ActiveCollisionNode
    (hL : L.IsKappaHindrance)
    (W : Popular.XSWarp
      (L.popularAuxiliaryInput hL.legal).lambda
      (L.popularAuxiliaryInput hL.legal).lambda.target)
    (q : WarpPath W) where
  rootPrefix : L.CanonicalErasedRouteRootPrefix hL W q
  firstCollision :
    FirstActualRootParentCollision q rootPrefix
  stop : V
  stop_mem_boundary : stop ∈
    GroundingCut.BB (L.popularAuxiliaryInput hL.legal)
      (reservedMaximalTargetCollisionCut
        (L.popularAuxiliaryInput hL.legal) W.paths)
  stop_mem_parent : stop ∈ rootPrefix.parent.support
  stop_mem_owner_route : stop ∈
    (canonicalErasedRoute
      (L.popularAuxiliaryInput hL.legal) W firstCollision.owner).vertexSet
  stop_ordered :
    stop = (canonicalErasedRoute
      (L.popularAuxiliaryInput hL.legal) W firstCollision.owner).initial ∨
    stop ∈ (canonicalErasedRoute
      (L.popularAuxiliaryInput hL.legal) W firstCollision.owner
        ).directionVertices .forward ∨
    ∃ l : Link Gamma.graph,
      l ∈ (canonicalErasedRoute
        (L.popularAuxiliaryInput hL.legal) W firstCollision.owner).links ∧
      l.direction = .backward ∧ l.path.IsSubpathOf rootPrefix.parent ∧
      stop = l.entry
  sourceRoot : V
  sourceRoot_mem : sourceRoot ∈ Gamma.source
  sourceRoot_eq_parent_initial :
    sourceRoot = rootPrefix.parent.initial
  sourceRoot_reaches_stop :
    Relation.ReflTransGen
      (fun u v ↦ (u, v) ∈ canonicalErasedRepairedEdges
        (L.popularAuxiliaryInput hL.legal)
        (routesBeforeIndex L hL W
          (warpPathIndex (L.popularAuxiliaryIndexed hL) W
            firstCollision.owner))) sourceRoot stop

/-- Every route admits an active collision node. -/
theorem exists_activeCollisionNode (q : WarpPath W) :
    Nonempty (ActiveCollisionNode hL W q) := by
  obtain ⟨R⟩ := L.exists_canonicalErasedRouteRootPrefix hL W q
  obtain ⟨C⟩ := exists_firstActualRootParentCollision q R
  obtain ⟨x, hxOwner, hxParent, hxBB, hxOrdered⟩ :=
    C.exists_orderedOwnerContact_mem_parent_mem_targetCollisionCut_BB
  obtain ⟨s, hsStart, hsFinish, _hsSupport, hsEdges⟩ :=
    GroundingPathPrefix.exists_initialFinitePrefix R.parent hxParent
  have hreach :=
    GroundingRootedReachabilityWarp.finitePath_start_reaches_of_mem_support
      s (hsEdges.trans C.rootParent_edgeSet_subset_repaired_beforeOwner)
        s.finish_mem_support
  exact ⟨{
    rootPrefix := R
    firstCollision := C
    stop := x
    stop_mem_boundary := hxBB
    stop_mem_parent := hxParent
    stop_mem_owner_route := hxOwner
    stop_ordered := hxOrdered
    sourceRoot := R.parent.initial
    sourceRoot_mem := R.parent_initial_mem_source
    sourceRoot_eq_parent_initial := rfl
    sourceRoot_reaches_stop := by
      simpa only [hsStart, hsFinish] using hreach }⟩

/-- A fixed node for each selected route.  All later definitions are
projections of this single choice, so their dependent witnesses agree
definitionally. -/
def activeCollisionNode (hL : L.IsKappaHindrance)
    (W : Popular.XSWarp
      (L.popularAuxiliaryInput hL.legal).lambda
      (L.popularAuxiliaryInput hL.legal).lambda.target)
    (q : WarpPath W) : ActiveCollisionNode hL W q :=
  Classical.choice (exists_activeCollisionNode q)

/-- The least selected route whose actual canonical erased route meets the
grounded parent at `q`. -/
def collisionOwner (hL : L.IsKappaHindrance)
    (W : Popular.XSWarp
      (L.popularAuxiliaryInput hL.legal).lambda
      (L.popularAuxiliaryInput hL.legal).lambda.target)
    (q : WarpPath W) : WarpPath W :=
  (activeCollisionNode hL W q).firstCollision.owner

/-- The literal corrected-boundary stopping point attached to `q`. -/
def collisionStop (hL : L.IsKappaHindrance)
    (W : Popular.XSWarp
      (L.popularAuxiliaryInput hL.legal).lambda
      (L.popularAuxiliaryInput hL.legal).lambda.target)
    (q : WarpPath W) : V :=
  (activeCollisionNode hL W q).stop

/-- The original source which roots the stopping point before its owner. -/
def collisionRoot (hL : L.IsKappaHindrance)
    (W : Popular.XSWarp
      (L.popularAuxiliaryInput hL.legal).lambda
      (L.popularAuxiliaryInput hL.legal).lambda.target)
    (q : WarpPath W) : V :=
  (activeCollisionNode hL W q).sourceRoot

theorem collisionStop_mem_boundary (q : WarpPath W) :
    collisionStop hL W q ∈
      GroundingCut.BB (L.popularAuxiliaryInput hL.legal)
        (reservedMaximalTargetCollisionCut
          (L.popularAuxiliaryInput hL.legal) W.paths) :=
  (activeCollisionNode hL W q).stop_mem_boundary

theorem collisionStop_mem_parent (q : WarpPath W) :
    collisionStop hL W q ∈
      (activeCollisionNode hL W q).rootPrefix.parent.support :=
  (activeCollisionNode hL W q).stop_mem_parent

/-- The collision stop is an actual vertex of the owner route, not merely a
point in the owner's broad decoded carrier. -/
theorem collisionStop_mem_owner_route (q : WarpPath W) :
    collisionStop hL W q ∈
      (canonicalErasedRoute
        (L.popularAuxiliaryInput hL.legal) W
        (collisionOwner hL W q)).vertexSet :=
  (activeCollisionNode hL W q).stop_mem_owner_route

/-- The chosen owner-route stop is an initial vertex, a retained forward
vertex, or the ordered entry of a backward link on the protected parent. -/
theorem collisionStop_ordered (q : WarpPath W) :
    collisionStop hL W q =
        (canonicalErasedRoute
          (L.popularAuxiliaryInput hL.legal) W
          (collisionOwner hL W q)).initial ∨
      collisionStop hL W q ∈
        (canonicalErasedRoute
          (L.popularAuxiliaryInput hL.legal) W
          (collisionOwner hL W q)).directionVertices .forward ∨
      ∃ l : Link Gamma.graph,
        l ∈ (canonicalErasedRoute
          (L.popularAuxiliaryInput hL.legal) W
          (collisionOwner hL W q)).links ∧
        l.direction = .backward ∧
        l.path.IsSubpathOf
          (activeCollisionNode hL W q).rootPrefix.parent ∧
        collisionStop hL W q = l.entry :=
  (activeCollisionNode hL W q).stop_ordered

theorem collisionRoot_mem_source (q : WarpPath W) :
    collisionRoot hL W q ∈ Gamma.source :=
  (activeCollisionNode hL W q).sourceRoot_mem

theorem collisionRoot_eq_parent_initial (q : WarpPath W) :
    collisionRoot hL W q =
      (activeCollisionNode hL W q).rootPrefix.parent.initial :=
  (activeCollisionNode hL W q).sourceRoot_eq_parent_initial

theorem collisionRoot_reaches_stop_before_owner (q : WarpPath W) :
    Relation.ReflTransGen
      (fun u v ↦ (u, v) ∈ canonicalErasedRepairedEdges
        (L.popularAuxiliaryInput hL.legal)
        (routesBeforeIndex L hL W
          (warpPathIndex (L.popularAuxiliaryIndexed hL) W
            (collisionOwner hL W q))))
      (collisionRoot hL W q) (collisionStop hL W q) :=
  (activeCollisionNode hL W q).sourceRoot_reaches_stop

/-- The owner alternative at every node: self, or strictly earlier in the
source-index well order. -/
theorem collisionOwner_eq_self_or_index_lt (q : WarpPath W) :
    collisionOwner hL W q = q ∨
      warpPathIndex (L.popularAuxiliaryIndexed hL) W
          (collisionOwner hL W q) <
        warpPathIndex (L.popularAuxiliaryIndexed hL) W q :=
  (activeCollisionNode hL W q).firstCollision.owner_eq_route_or_index_lt

/-- The proper absorption relation obtained by discarding self-owners. -/
def Absorbs (hL : L.IsKappaHindrance)
    (W : Popular.XSWarp
      (L.popularAuxiliaryInput hL.legal).lambda
      (L.popularAuxiliaryInput hL.legal).lambda.target)
    (r q : WarpPath W) : Prop :=
  collisionOwner hL W q = r ∧ r ≠ q

theorem absorbs_index_lt {r q : WarpPath W} (hrq : Absorbs hL W r q) :
    warpPathIndex (L.popularAuxiliaryIndexed hL) W r <
      warpPathIndex (L.popularAuxiliaryIndexed hL) W q := by
  rcases collisionOwner_eq_self_or_index_lt (hL := hL) q with hself | hlt
  · exact False.elim (hrq.2 (hrq.1 ▸ hself))
  · simpa only [hrq.1] using hlt

/-- Proper owner absorption is well founded because it strictly decreases
the auxiliary source index. -/
theorem absorbs_wellFounded :
    WellFounded (Absorbs hL W) := by
  apply WellFounded.mono
    (InvImage.wf
      (warpPathIndex (L.popularAuxiliaryIndexed hL) W) wellFounded_lt)
  intro r q hrq
  exact absorbs_index_lt hrq

/-- Collision-forest induction.  The self-owner case performs the local
one-route transaction.  In the proper-owner case the already completed
earlier owner absorbs the node. -/
theorem all_of_self_or_absorb
    (Closed : WarpPath W → Prop)
    (self : ∀ q, collisionOwner hL W q = q → Closed q)
    (absorb : ∀ q, collisionOwner hL W q ≠ q →
      Closed (collisionOwner hL W q) → Closed q) :
    ∀ q, Closed q := by
  intro q
  apply absorbs_wellFounded.induction q
  intro q ih
  by_cases hself : collisionOwner hL W q = q
  · exact self q hself
  · exact absorb q hself
      (ih (collisionOwner hL W q) ⟨rfl, hself⟩)

end GroundingEqualMaximalCollisionRecursion
end DWeb.KappaLadder
end Erdos599

#print axioms Erdos599.DWeb.KappaLadder.GroundingEqualMaximalCollisionRecursion.exists_activeCollisionNode
#print axioms Erdos599.DWeb.KappaLadder.GroundingEqualMaximalCollisionRecursion.collisionRoot_reaches_stop_before_owner
#print axioms Erdos599.DWeb.KappaLadder.GroundingEqualMaximalCollisionRecursion.collisionStop_mem_owner_route
#print axioms Erdos599.DWeb.KappaLadder.GroundingEqualMaximalCollisionRecursion.collisionStop_ordered
#print axioms Erdos599.DWeb.KappaLadder.GroundingEqualMaximalCollisionRecursion.absorbs_wellFounded
#print axioms Erdos599.DWeb.KappaLadder.GroundingEqualMaximalCollisionRecursion.all_of_self_or_absorb
