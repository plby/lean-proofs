/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingEqualActiveIsolation

/-!
# Concrete one-route transaction for the split equal branch

Pruning a grounded parent prefix against the full ordered active relation
either roots the route initial, reaches a vertex of that route at the first
self-deletion, or reaches a point of its grounded parent immediately before
a head conflict.  No abstract transaction provider is used.
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

private abbrev SplitTransactionInput
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance) :=
  L.splitPopularAuxiliaryInput hL.legal

/-- A finite reachability chain in the union either survives after deleting
blocked base edges, or exposes a first blocked base edge whose tail is still
reachable. -/
theorem split_reflTransGen_union_prune_or_exists_conflict
    {base inserted blocked : Set (V × V)} {a b : V}
    (hab : Relation.ReflTransGen
      (fun x y ↦ (x, y) ∈ base ∪ inserted) a b) :
    Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ (base \ blocked) ∪ inserted) a b ∨
      ∃ u v,
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ (base \ blocked) ∪ inserted) a u ∧
        (u, v) ∈ base ∧ (u, v) ∈ blocked ∧
        (u, v) ∉ inserted := by
  induction hab using Relation.ReflTransGen.trans_induction_on with
  | refl => exact Or.inl .refl
  | single hab =>
      rename_i x y
      rcases hab with hbase | hinserted
      · by_cases hblocked : (x, y) ∈ blocked
        · by_cases hinserted : (x, y) ∈ inserted
          · exact Or.inl (.single (Or.inr hinserted))
          · exact Or.inr ⟨x, y, .refl, hbase, hblocked, hinserted⟩
        · exact Or.inl (.single (Or.inl ⟨hbase, hblocked⟩))
      · exact Or.inl (.single (Or.inr hinserted))
  | trans hab hbc ihab ihbc =>
      rcases ihab with hab' |
          ⟨u, v, hau, huvBase, huvBlocked, huvNotInserted⟩
      · rcases ihbc with hbc' |
          ⟨u, v, hbu, huvBase, huvBlocked, huvNotInserted⟩
        · exact Or.inl (hab'.trans hbc')
        · exact Or.inr
            ⟨u, v, hab'.trans hbu, huvBase, huvBlocked, huvNotInserted⟩
      · exact Or.inr
          ⟨u, v, hau, huvBase, huvBlocked, huvNotInserted⟩

/-- Every ordered active route produces a concrete source-rooted absorption
seed: either an actual vertex of the route or a point of its grounded
parent. -/
theorem splitMaximalActive_exists_sourceRooted_routeVertex_or_parentPoint
    {L : Gamma.KappaLadder kappa} {hL : L.IsSplitKappaHindrance}
    {reserved : FinitePath (SplitTransactionInput L hL).lambda.graph}
    {M : Popular.MaximalDecodedTargetPureAvoidingRestrictedXSWarp
      (SplitTransactionInput L hL)
      (L.splitGroundedAuxiliarySources hL \ {reserved.start})
      (collisionCarrier (SplitTransactionInput L hL) reserved)}
    (p : WarpPath (splitMaximalOrderedActiveSubwarp hL M))
    (R : L.SplitCanonicalErasedRouteRootPrefix hL
      (splitMaximalOrderedActiveSubwarp hL M) p) :
    (∃ x ∈ (canonicalErasedRoute
        (SplitTransactionInput L hL)
        (splitMaximalOrderedActiveSubwarp hL M) p).vertexSet,
      ∃ a ∈ Gamma.source,
        Relation.ReflTransGen
          (fun s t ↦ (s, t) ∈ canonicalErasedRepairedEdges
            (SplitTransactionInput L hL)
            (splitMaximalOrderedActiveSubwarp hL M)) a x) ∨
    (∃ x ∈ R.parentData.parent.support,
      ∃ a ∈ Gamma.source,
        Relation.ReflTransGen
          (fun s t ↦ (s, t) ∈ canonicalErasedRepairedEdges
            (SplitTransactionInput L hL)
            (splitMaximalOrderedActiveSubwarp hL M)) a x) := by
  let I := SplitTransactionInput L hL
  let W := splitMaximalOrderedActiveSubwarp hL M
  let E := canonicalErasedRepairedEdges I W
  let inserted :=
    (canonicalErasedRoute I W p).directionEdges .forward
  let blocked : Set (V × V) := R.path.edgeSet \ E
  have hpathReach : Relation.ReflTransGen
      (fun x y ↦ (x, y) ∈ R.path.edgeSet)
      R.path.start R.path.finish :=
    GroundingRootedReachabilityWarp.finitePath_start_reaches_of_mem_support
      R.path (fun _ h ↦ h) R.path.finish_mem_support
  have hrootUnion : Relation.ReflTransGen
      (fun x y ↦ (x, y) ∈ R.path.edgeSet ∪ inserted)
      R.path.start R.path.finish :=
    Relation.ReflTransGen.mono (fun _ _ hxy ↦ Or.inl hxy)
      _ _ hpathReach
  rcases split_reflTransGen_union_prune_or_exists_conflict hrootUnion with
      hsurvives | ⟨u, v, hau, huvPath, huvBlocked, _huvNotInserted⟩
  · left
    refine ⟨(canonicalErasedRoute I W p).initial,
      (canonicalErasedRoute I W p).initial_mem_vertexSet,
      R.path.start, R.start_mem_source, ?_⟩
    have hmono : (R.path.edgeSet \ blocked) ∪ inserted ⊆ E := by
      rintro e (he | he)
      · by_contra heNotE
        exact he.2 ⟨he.1, heNotE⟩
      · exact Or.inr (Set.mem_iUnion.2 ⟨p, he⟩)
    have hreach := Relation.ReflTransGen.mono
      (fun _ _ hxy ↦ hmono hxy) _ _ hsurvives
    simpa only [E, R.finish_eq] using hreach
  · have huvNotE : (u, v) ∉ E := huvBlocked.2
    have huvParent : (u, v) ∈ R.parentData.parent.edgeSet :=
      R.edgeSet_subset huvPath
    have hkind :=
      splitMaximalActive_rootParentEdge_currentDeletion_of_not_mem
        p R huvParent huvNotE
    have hmono : (R.path.edgeSet \ blocked) ∪ inserted ⊆ E := by
      rintro e (he | he)
      · by_contra heNotE
        exact he.2 ⟨he.1, heNotE⟩
      · exact Or.inr (Set.mem_iUnion.2 ⟨p, he⟩)
    have hauE := Relation.ReflTransGen.mono
      (fun _ _ hxy ↦ hmono hxy) _ _ hau
    rcases hkind with hbackward | ⟨f, hf, htail | hhead⟩
    · left
      have hends := AltPath.directionEdge_endpoints_mem_vertexSet
        (canonicalErasedRoute I W p) hbackward
      exact ⟨u, hends.1, R.path.start, R.start_mem_source, hauE⟩
    · left
      have hends := AltPath.directionEdge_endpoints_mem_vertexSet
        (canonicalErasedRoute I W p) hf
      change u = f.1 at htail
      exact ⟨u, htail.symm ▸ hends.1,
        R.path.start, R.start_mem_source, hauE⟩
    · right
      have huParent :
          u ∈ R.parentData.parent.support :=
        (R.parentData.parent.edgeSet_subset_support_prod huvParent).1
      exact ⟨u, huParent, R.path.start, R.start_mem_source, hauE⟩

end DWeb.KappaLadder
end Erdos599
