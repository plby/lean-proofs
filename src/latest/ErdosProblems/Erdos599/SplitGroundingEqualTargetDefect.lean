/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingEqualActiveTransaction
import ErdosProblems.Erdos599.SplitGroundingEqualReservedParent
import ErdosProblems.Erdos599.GroundingFiniteSourceRoot

/-!
# Ambient target defects for the split maximal ordered equal relation

A point of the source-reachable essential terminal cut carries a concrete
ambient path from an original source.  If it is not rooted in the repaired
relation of the grounded split maximal ordered active family, that path has
a last deleted head.  The incoming edge at that head is either outside the
limiting-ladder family, selected backwards by an actual route, or deleted
by a tail/head conflict with an actual selected forward edge.

This is a classification theorem only.  It deliberately exposes the four
route-level outcomes and does not assume or package a repair provider.
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

private abbrev SplitDefectInput
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance) :=
  L.splitPopularAuxiliaryInput hL.legal

private abbrev SplitActiveWarp
    {L : Gamma.KappaLadder kappa} (hL : L.IsSplitKappaHindrance)
    {reserved : FinitePath (SplitDefectInput L hL).lambda.graph}
    (M : Popular.MaximalDecodedTargetPureAvoidingRestrictedXSWarp
      (SplitDefectInput L hL)
      (L.splitGroundedAuxiliarySources hL \ {reserved.start})
      (collisionCarrier (SplitDefectInput L hL) reserved)) :=
  splitMaximalOrderedActiveSubwarp hL M

/-- If a source-root reaches the start of a finite ambient path but not its
end, the path has a last deleted head which is itself unrooted. -/
private theorem split_exists_unrootedLastDeletedHead
    {E : Set (V × V)} {A : Set V}
    (p : FinitePath Gamma.graph)
    (hstart : ∃ a ∈ A,
      Relation.ReflTransGen (fun x y ↦ (x, y) ∈ E) a p.start)
    (hfinish : ¬ ∃ a ∈ A,
      Relation.ReflTransGen (fun x y ↦ (x, y) ∈ E) a p.finish) :
    ∃ D : LastDeletedHead p E,
      ¬ ∃ a ∈ A,
        Relation.ReflTransGen (fun x y ↦ (x, y) ∈ E) a D.head := by
  have hdeleted : ∃ e ∈ p.edgeSet, e ∉ E := by
    by_contra hnone
    apply hfinish
    obtain ⟨a, ha, hastart⟩ := hstart
    refine ⟨a, ha, hastart.trans ?_⟩
    apply Relation.ReflTransGen.mono
      (r := fun x y ↦ (x, y) ∈ p.edgeSet)
      (p := fun x y ↦ (x, y) ∈ E)
    · intro x y hxy
      by_contra hxyE
      exact hnone ⟨(x, y), hxy, hxyE⟩
    · exact Alternating.Walk.reflTransGen_edgeSet p.walk
  let D := (exists_lastDeletedHead p hdeleted).some
  refine ⟨D, ?_⟩
  rintro ⟨a, ha, haD⟩
  apply hfinish
  refine ⟨a, ha, haD.trans ?_⟩
  have hsuffix : Relation.ReflTransGen
      (fun x y ↦ (x, y) ∈ E) D.suffix.start D.suffix.finish := by
    apply Relation.ReflTransGen.mono
      (r := fun x y ↦ (x, y) ∈ D.suffix.edgeSet)
      (p := fun x y ↦ (x, y) ∈ E)
    · intro x y hxy
      exact D.suffix_edgeSet_subset hxy
    · exact Alternating.Walk.reflTransGen_edgeSet D.suffix.walk
  exact D.suffix_finish ▸ (D.suffix_start ▸ hsuffix)

/-- The last missing edge on an ambient source path to a point of the
source-reachable split terminal cut. -/
structure SplitMaximalActiveTargetAmbientDefect
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
    {reserved : FinitePath (SplitDefectInput L hL).lambda.graph}
    (M : Popular.MaximalDecodedTargetPureAvoidingRestrictedXSWarp
      (SplitDefectInput L hL)
      (L.splitGroundedAuxiliarySources hL \ {reserved.start})
      (collisionCarrier (SplitDefectInput L hL) reserved))
    (b : V) where
  boundary_mem : b ∈ splitReachableTerminalCut L hL
  path : FinitePath Gamma.graph
  path_start_source : path.start ∈ Gamma.source
  path_finish : path.finish = b
  deleted : LastDeletedHead path
    (canonicalErasedRepairedEdges
      (SplitDefectInput L hL) (SplitActiveWarp hL M))
  deleted_head_not_rooted :
    ¬ ∃ a ∈ Gamma.source,
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ canonicalErasedRepairedEdges
          (SplitDefectInput L hL) (SplitActiveWarp hL M)) a deleted.head
  tail : V
  incoming_mem : (tail, deleted.head) ∈ path.edgeSet
  incoming_not_relation :
    (tail, deleted.head) ∉ canonicalErasedRepairedEdges
      (SplitDefectInput L hL) (SplitActiveWarp hL M)
  incoming_class :
    (tail, deleted.head) ∉ (SplitDefectInput L hL).familyEdges ∨
      (tail, deleted.head) ∈ canonicalErasedBackwardEdges
        (SplitDefectInput L hL) (SplitActiveWarp hL M) ∨
      (tail, deleted.head) ∈ canonicalErasedForwardConflictEdges
        (SplitDefectInput L hL) (SplitActiveWarp hL M)

namespace SplitMaximalActiveTargetAmbientDefect

variable {L : Gamma.KappaLadder kappa} {hL : L.IsSplitKappaHindrance}
  {reserved : FinitePath (SplitDefectInput L hL).lambda.graph}
  {M : Popular.MaximalDecodedTargetPureAvoidingRestrictedXSWarp
    (SplitDefectInput L hL)
    (L.splitGroundedAuxiliarySources hL \ {reserved.start})
    (collisionCarrier (SplitDefectInput L hL) reserved)}
  {b : V}

/-- The four actual route-level causes of the last missing ambient edge. -/
inductive IncomingOutcome
    (D : L.SplitMaximalActiveTargetAmbientDefect hL M b) : Prop
  | outsideFamily
      (h : (D.tail, D.deleted.head) ∉
        (SplitDefectInput L hL).familyEdges)
  | backward (r : WarpPath (SplitActiveWarp hL M))
      (h : (D.tail, D.deleted.head) ∈
        (canonicalErasedRoute
          (SplitDefectInput L hL) (SplitActiveWarp hL M) r).directionEdges
            .backward)
  | forwardTail (r : WarpPath (SplitActiveWarp hL M)) (f : V × V)
      (hf : f ∈ (canonicalErasedRoute
        (SplitDefectInput L hL) (SplitActiveWarp hL M) r).directionEdges
          .forward)
      (htail : D.tail = f.1)
  | forwardHead (r : WarpPath (SplitActiveWarp hL M)) (f : V × V)
      (hf : f ∈ (canonicalErasedRoute
        (SplitDefectInput L hL) (SplitActiveWarp hL M) r).directionEdges
          .forward)
      (hhead : D.deleted.head = f.2)

/-- Unpack the set-valued deletion class to one of the four concrete route
outcomes. -/
theorem incomingOutcome
    (D : L.SplitMaximalActiveTargetAmbientDefect hL M b) :
    D.IncomingOutcome := by
  rcases D.incoming_class with hout | hbackward | hconflict
  · exact .outsideFamily hout
  · simp only [canonicalErasedBackwardEdges, Set.mem_iUnion] at hbackward
    obtain ⟨r, hr⟩ := hbackward
    exact .backward r hr
  · change ∃ f ∈ canonicalErasedForwardEdges
        (SplitDefectInput L hL) (SplitActiveWarp hL M),
        (D.tail, D.deleted.head).1 = f.1 ∨
          (D.tail, D.deleted.head).2 = f.2 at hconflict
    obtain ⟨f, hf, htail | hhead⟩ := hconflict
    · simp only [canonicalErasedForwardEdges, Set.mem_iUnion] at hf
      obtain ⟨r, hfr⟩ := hf
      exact .forwardTail r f hfr htail
    · simp only [canonicalErasedForwardEdges, Set.mem_iUnion] at hf
      obtain ⟨r, hfr⟩ := hf
      exact .forwardHead r f hfr hhead

/-- Rooting the displayed deleted head roots the boundary point along the
surviving final suffix of its ambient path. -/
theorem target_rooted
    (D : L.SplitMaximalActiveTargetAmbientDefect hL M b)
    (hhead : ∃ a ∈ Gamma.source,
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ canonicalErasedRepairedEdges
          (SplitDefectInput L hL) (SplitActiveWarp hL M)) a D.deleted.head) :
    ∃ a ∈ Gamma.source,
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ canonicalErasedRepairedEdges
          (SplitDefectInput L hL) (SplitActiveWarp hL M)) a b := by
  obtain ⟨a, ha, haHead⟩ := hhead
  refine ⟨a, ha, haHead.trans ?_⟩
  have hsuffix : Relation.ReflTransGen
      (fun x y ↦ (x, y) ∈ canonicalErasedRepairedEdges
        (SplitDefectInput L hL) (SplitActiveWarp hL M))
      D.deleted.suffix.start D.deleted.suffix.finish := by
    apply Relation.ReflTransGen.mono
      (r := fun x y ↦ (x, y) ∈ D.deleted.suffix.edgeSet)
      (p := fun x y ↦ (x, y) ∈ canonicalErasedRepairedEdges
        (SplitDefectInput L hL) (SplitActiveWarp hL M))
    · intro x y hxy
      exact D.deleted.suffix_edgeSet_subset hxy
    · exact Alternating.Walk.reflTransGen_edgeSet D.deleted.suffix.walk
  rw [D.deleted.suffix_start] at hsuffix
  rw [D.deleted.suffix_finish, D.path_finish] at hsuffix
  exact hsuffix

end SplitMaximalActiveTargetAmbientDefect

/-- Every point of the source-reachable terminal boundary is rooted in the
concrete split maximal active relation, or exposes its literal last ambient
deletion. -/
theorem splitMaximalActive_target_rooted_or_ambientDefect
    {L : Gamma.KappaLadder kappa} {hL : L.IsSplitKappaHindrance}
    {reserved : FinitePath (SplitDefectInput L hL).lambda.graph}
    (M : Popular.MaximalDecodedTargetPureAvoidingRestrictedXSWarp
      (SplitDefectInput L hL)
      (L.splitGroundedAuxiliarySources hL \ {reserved.start})
      (collisionCarrier (SplitDefectInput L hL) reserved))
    (b : V) (hb : b ∈ splitReachableTerminalCut L hL) :
    (∃ a ∈ Gamma.source,
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ canonicalErasedRepairedEdges
          (SplitDefectInput L hL) (SplitActiveWarp hL M)) a b) ∨
      Nonempty (L.SplitMaximalActiveTargetAmbientDefect hL M b) := by
  let E := canonicalErasedRepairedEdges
    (SplitDefectInput L hL) (SplitActiveWarp hL M)
  by_cases hroot : ∃ a ∈ Gamma.source,
      Relation.ReflTransGen (fun x y ↦ (x, y) ∈ E) a b
  · exact Or.inl hroot
  right
  obtain ⟨p, hpStart, hpFinish⟩ := hb.2
  have hstart : ∃ a ∈ Gamma.source,
      Relation.ReflTransGen (fun x y ↦ (x, y) ∈ E) a p.start :=
    ⟨p.start, hpStart, .refl⟩
  have hfinish : ¬ ∃ a ∈ Gamma.source,
      Relation.ReflTransGen (fun x y ↦ (x, y) ∈ E) a p.finish := by
    simpa only [hpFinish] using hroot
  obtain ⟨D, hDnot⟩ :=
    split_exists_unrootedLastDeletedHead p hstart hfinish
  obtain ⟨tail, htailPath, htailNot⟩ := D.deleted_incoming
  have hclass :
      (tail, D.head) ∉ (SplitDefectInput L hL).familyEdges ∨
        (tail, D.head) ∈ canonicalErasedBackwardEdges
          (SplitDefectInput L hL) (SplitActiveWarp hL M) ∨
        (tail, D.head) ∈ canonicalErasedForwardConflictEdges
          (SplitDefectInput L hL) (SplitActiveWarp hL M) := by
    by_cases hfamily :
        (tail, D.head) ∈ (SplitDefectInput L hL).familyEdges
    · by_cases hbackward :
          (tail, D.head) ∈ canonicalErasedBackwardEdges
            (SplitDefectInput L hL) (SplitActiveWarp hL M)
      · exact Or.inr (Or.inl hbackward)
      · by_cases hconflict :
            (tail, D.head) ∈ canonicalErasedForwardConflictEdges
              (SplitDefectInput L hL) (SplitActiveWarp hL M)
        · exact Or.inr (Or.inr hconflict)
        · exact False.elim <| htailNot <| Or.inl
            ⟨⟨hfamily, hbackward⟩, hconflict⟩
    · exact Or.inl hfamily
  exact ⟨{
    boundary_mem := hb
    path := p
    path_start_source := hpStart
    path_finish := hpFinish
    deleted := D
    deleted_head_not_rooted := hDnot
    tail := tail
    incoming_mem := htailPath
    incoming_not_relation := htailNot
    incoming_class := hclass }⟩

/-- Direct rooted-or-four-outcome form of the split target defect
classifier. -/
theorem splitMaximalActive_target_rooted_or_incomingOutcome
    {L : Gamma.KappaLadder kappa} {hL : L.IsSplitKappaHindrance}
    {reserved : FinitePath (SplitDefectInput L hL).lambda.graph}
    (M : Popular.MaximalDecodedTargetPureAvoidingRestrictedXSWarp
      (SplitDefectInput L hL)
      (L.splitGroundedAuxiliarySources hL \ {reserved.start})
      (collisionCarrier (SplitDefectInput L hL) reserved))
    (b : V) (hb : b ∈ splitReachableTerminalCut L hL) :
    (∃ a ∈ Gamma.source,
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ canonicalErasedRepairedEdges
          (SplitDefectInput L hL) (SplitActiveWarp hL M)) a b) ∨
      ∃ D : L.SplitMaximalActiveTargetAmbientDefect hL M b,
        D.IncomingOutcome := by
  rcases splitMaximalActive_target_rooted_or_ambientDefect M b hb with
      hroot | hdefect
  · exact Or.inl hroot
  · let D := hdefect.some
    exact Or.inr ⟨D, D.incomingOutcome⟩

end DWeb.KappaLadder
end Erdos599

#print axioms Erdos599.DWeb.KappaLadder.SplitMaximalActiveTargetAmbientDefect.target_rooted
#print axioms Erdos599.DWeb.KappaLadder.splitMaximalActive_target_rooted_or_ambientDefect
#print axioms Erdos599.DWeb.KappaLadder.splitMaximalActive_target_rooted_or_incomingOutcome
