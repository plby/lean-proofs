/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingEqualMaximalOrderedTransaction
import ErdosProblems.Erdos599.GroundingStoppedRootReduction

/-!
# Exact ambient defects at the equal-stage target boundary

The selected minimal target boundary consists of ambient-source-reachable
vertices.  If one of them is not rooted in the concrete maximal ordered
relation, its ambient source prefix therefore has a last deleted head.  For
the canonical equal-stage relation the incoming edge of that head has only
three possible classifications: it is outside the limiting-ladder family,
it is a selected backward edge, or it is removed by a selected forward-edge
incidence conflict.

This replaces the opaque target-rooting premise by the literal final missing
edge and its surviving suffix.  A construction-specific repair only has to
root that one head; the suffix then roots the selected target automatically.
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

private abbrev ActiveWarp
    {L : Gamma.KappaLadder kappa} (hL : L.IsKappaHindrance)
    {q : FinitePath (EqualInput L hL).lambda.graph}
    (M : Popular.MaximalDecodedTargetPureAvoidingRestrictedXSWarp
      (EqualInput L hL)
      ((EqualInput L hL).lambda.source \ {q.start})
      (collisionCarrier (EqualInput L hL) q)) :=
  maximalOrderedActiveSubwarp hL M

/-- The last missing edge on an ambient source prefix to one selected target
of the concrete maximal ordered equal relation. -/
structure MaximalActiveTargetAmbientDefect
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    {q : FinitePath (EqualInput L hL).lambda.graph}
    (M : Popular.MaximalDecodedTargetPureAvoidingRestrictedXSWarp
      (EqualInput L hL)
      ((EqualInput L hL).lambda.source \ {q.start})
      (collisionCarrier (EqualInput L hL) q))
    (T : L.MinimalReachableTargetBoundary hL) (b : V) where
  boundary_mem : b ∈ T.vertices
  path : FinitePath Gamma.graph
  path_start_source : path.start ∈ Gamma.source
  path_finish : path.finish = b
  deleted : LastDeletedHead path
    (canonicalErasedRepairedEdges (EqualInput L hL) (ActiveWarp hL M))
  deleted_head_not_rooted :
    ¬ ∃ a ∈ Gamma.source,
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ canonicalErasedRepairedEdges
          (EqualInput L hL) (ActiveWarp hL M)) a deleted.head
  tail : V
  incoming_mem : (tail, deleted.head) ∈ path.edgeSet
  incoming_not_relation :
    (tail, deleted.head) ∉
      canonicalErasedRepairedEdges (EqualInput L hL) (ActiveWarp hL M)
  incoming_class :
    (tail, deleted.head) ∉ (EqualInput L hL).familyEdges ∨
      (tail, deleted.head) ∈
        canonicalErasedBackwardEdges (EqualInput L hL) (ActiveWarp hL M) ∨
      (tail, deleted.head) ∈
        canonicalErasedForwardConflictEdges
          (EqualInput L hL) (ActiveWarp hL M)

namespace MaximalActiveTargetAmbientDefect

variable {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
  {q : FinitePath (EqualInput L hL).lambda.graph}
  {M : Popular.MaximalDecodedTargetPureAvoidingRestrictedXSWarp
    (EqualInput L hL)
    ((EqualInput L hL).lambda.source \ {q.start})
    (collisionCarrier (EqualInput L hL) q)}
  {T : L.MinimalReachableTargetBoundary hL} {b : V}

/-- The route-level form of the final missing ambient edge.  The incidence
conflict is split by orientation because a same-head conflict immediately
feeds the missing head, whereas a same-tail conflict diverts the old suffix.
-/
inductive IncomingOutcome
    (D : L.MaximalActiveTargetAmbientDefect hL M T b) : Prop
  | outsideFamily
      (h : (D.tail, D.deleted.head) ∉ (EqualInput L hL).familyEdges)
  | backward (r : WarpPath (ActiveWarp hL M))
      (h : (D.tail, D.deleted.head) ∈
        (canonicalErasedRoute
          (EqualInput L hL) (ActiveWarp hL M) r).directionEdges .backward)
  | forwardTail (r : WarpPath (ActiveWarp hL M)) (f : V × V)
      (hf : f ∈ (canonicalErasedRoute
        (EqualInput L hL) (ActiveWarp hL M) r).directionEdges .forward)
      (htail : D.tail = f.1)
  | forwardHead (r : WarpPath (ActiveWarp hL M)) (f : V × V)
      (hf : f ∈ (canonicalErasedRoute
        (EqualInput L hL) (ActiveWarp hL M) r).directionEdges .forward)
      (hhead : D.deleted.head = f.2)

/-- Unpack the set-valued deletion classification to an actual selected
route and an actual forward or backward edge. -/
theorem incomingOutcome
    (D : L.MaximalActiveTargetAmbientDefect hL M T b) :
    D.IncomingOutcome := by
  rcases D.incoming_class with hout | hbackward | hconflict
  · exact .outsideFamily hout
  · simp only [canonicalErasedBackwardEdges, Set.mem_iUnion] at hbackward
    obtain ⟨r, hr⟩ := hbackward
    exact .backward r hr
  · change ∃ f ∈ canonicalErasedForwardEdges
        (EqualInput L hL) (ActiveWarp hL M),
        (D.tail, D.deleted.head).1 = f.1 ∨
          (D.tail, D.deleted.head).2 = f.2 at hconflict
    obtain ⟨f, hf, htail | hhead⟩ := hconflict
    · simp only [canonicalErasedForwardEdges, Set.mem_iUnion] at hf
      obtain ⟨r, hfr⟩ := hf
      exact .forwardTail r f hfr htail
    · simp only [canonicalErasedForwardEdges, Set.mem_iUnion] at hf
      obtain ⟨r, hfr⟩ := hf
      exact .forwardHead r f hfr hhead

/-- Rooting the one displayed deleted head roots the selected target along
the surviving last suffix. -/
theorem target_rooted
    (D : L.MaximalActiveTargetAmbientDefect hL M T b)
    (hhead : ∃ a ∈ Gamma.source,
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ canonicalErasedRepairedEdges
          (EqualInput L hL) (ActiveWarp hL M)) a D.deleted.head) :
    ∃ a ∈ Gamma.source,
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ canonicalErasedRepairedEdges
          (EqualInput L hL) (ActiveWarp hL M)) a b := by
  obtain ⟨a, ha, haHead⟩ := hhead
  refine ⟨a, ha, haHead.trans ?_⟩
  have hsuffix : Relation.ReflTransGen
      (fun x y ↦ (x, y) ∈ canonicalErasedRepairedEdges
        (EqualInput L hL) (ActiveWarp hL M))
      D.deleted.suffix.start D.deleted.suffix.finish := by
    apply Relation.ReflTransGen.mono
      (r := fun x y ↦ (x, y) ∈ D.deleted.suffix.edgeSet)
      (p := fun x y ↦ (x, y) ∈ canonicalErasedRepairedEdges
        (EqualInput L hL) (ActiveWarp hL M))
    · intro x y hxy
      exact D.deleted.suffix_edgeSet_subset hxy
    · exact Alternating.Walk.reflTransGen_edgeSet D.deleted.suffix.walk
  rw [D.deleted.suffix_start] at hsuffix
  rw [D.deleted.suffix_finish, D.path_finish] at hsuffix
  exact hsuffix

end MaximalActiveTargetAmbientDefect

/-- Every selected minimal target is rooted in the concrete maximal active
relation, or exposes its literal last ambient deletion with the exact three
equal-relation deletion classes. -/
theorem maximalActive_target_rooted_or_ambientDefect
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {q : FinitePath (EqualInput L hL).lambda.graph}
    (M : Popular.MaximalDecodedTargetPureAvoidingRestrictedXSWarp
      (EqualInput L hL)
      ((EqualInput L hL).lambda.source \ {q.start})
      (collisionCarrier (EqualInput L hL) q))
    (T : L.MinimalReachableTargetBoundary hL) (b : V)
    (hb : b ∈ T.vertices) :
    (∃ a ∈ Gamma.source,
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ canonicalErasedRepairedEdges
          (EqualInput L hL) (ActiveWarp hL M)) a b) ∨
      Nonempty (L.MaximalActiveTargetAmbientDefect hL M T b) := by
  let E := canonicalErasedRepairedEdges
    (EqualInput L hL) (ActiveWarp hL M)
  by_cases hroot : ∃ a ∈ Gamma.source,
      Relation.ReflTransGen (fun x y ↦ (x, y) ∈ E) a b
  · exact Or.inl hroot
  right
  obtain ⟨p, hpStart, hpFinish⟩ :=
    T.subset_reachableTerminalCut hb |>.2
  have hstart : ∃ a ∈ Gamma.source,
      Relation.ReflTransGen (fun x y ↦ (x, y) ∈ E) a p.start :=
    ⟨p.start, hpStart, .refl⟩
  have hfinish : ¬ ∃ a ∈ Gamma.source,
      Relation.ReflTransGen (fun x y ↦ (x, y) ∈ E) a p.finish := by
    simpa only [hpFinish] using hroot
  obtain ⟨D, hDnot⟩ :=
    exists_unrootedLastDeletedHead p hstart hfinish
  obtain ⟨u, huPath, huNot⟩ := D.deleted_incoming
  have hclass :
      (u, D.head) ∉ (EqualInput L hL).familyEdges ∨
        (u, D.head) ∈ canonicalErasedBackwardEdges
          (EqualInput L hL) (ActiveWarp hL M) ∨
        (u, D.head) ∈ canonicalErasedForwardConflictEdges
          (EqualInput L hL) (ActiveWarp hL M) := by
    by_cases huFamily : (u, D.head) ∈ (EqualInput L hL).familyEdges
    · by_cases huBackward : (u, D.head) ∈ canonicalErasedBackwardEdges
          (EqualInput L hL) (ActiveWarp hL M)
      · exact Or.inr (Or.inl huBackward)
      · by_cases huConflict : (u, D.head) ∈
            canonicalErasedForwardConflictEdges
              (EqualInput L hL) (ActiveWarp hL M)
        · exact Or.inr (Or.inr huConflict)
        · exact False.elim <| huNot <| Or.inl
            ⟨⟨huFamily, huBackward⟩, huConflict⟩
    · exact Or.inl huFamily
  exact ⟨{
    boundary_mem := hb
    path := p
    path_start_source := hpStart
    path_finish := hpFinish
    deleted := D
    deleted_head_not_rooted := hDnot
    tail := u
    incoming_mem := huPath
    incoming_not_relation := huNot
    incoming_class := hclass }⟩

/-- Strongest concrete target-only compiler for the maximal ordered equal
switch.  All global geometry is internal.  The sole repair callback receives
the literal last missing ambient edge and its deletion classification. -/
theorem ReservedGroundedParent.exists_hindrance_of_maximalActive_targetDefectRepairs
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {q : FinitePath (EqualInput L hL).lambda.graph}
    {hqsource : q.start ∈ (EqualInput L hL).lambda.source}
    (R : L.ReservedGroundedParent hL q hqsource)
    (M : Popular.MaximalDecodedTargetPureAvoidingRestrictedXSWarp
      (EqualInput L hL)
      ((EqualInput L hL).lambda.source \ {q.start})
      (collisionCarrier (EqualInput L hL) q))
    (T : L.MinimalReachableTargetBoundary hL)
    (repair : ∀ (b : V)
      (D : L.MaximalActiveTargetAmbientDefect hL M T b),
      ∃ a ∈ Gamma.source,
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ canonicalErasedRepairedEdges
            (EqualInput L hL) (ActiveWarp hL M)) a D.deleted.head) :
    ∃ H : Set Gamma.DPath, Gamma.IsHindrance H := by
  apply R.exists_hindrance_of_maximalOrderedActive_targetRooted M T
  intro b hb
  rcases maximalActive_target_rooted_or_ambientDefect M T b hb with
      hroot | hdefect
  · exact hroot
  · obtain ⟨D⟩ := hdefect
    exact D.target_rooted (repair b D)

/-- Four-case version of the preceding compiler.  It is the direct equal
analogue of the reachable Assertion 8.22 ambient-defect interface and leaves
no set-valued collision membership for a downstream repair to unpack. -/
theorem ReservedGroundedParent.exists_hindrance_of_maximalActive_targetOutcomeRepairs
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {q : FinitePath (EqualInput L hL).lambda.graph}
    {hqsource : q.start ∈ (EqualInput L hL).lambda.source}
    (R : L.ReservedGroundedParent hL q hqsource)
    (M : Popular.MaximalDecodedTargetPureAvoidingRestrictedXSWarp
      (EqualInput L hL)
      ((EqualInput L hL).lambda.source \ {q.start})
      (collisionCarrier (EqualInput L hL) q))
    (T : L.MinimalReachableTargetBoundary hL)
    (repairOutside : ∀ (b : V)
      (D : L.MaximalActiveTargetAmbientDefect hL M T b),
      (D.tail, D.deleted.head) ∉ (EqualInput L hL).familyEdges →
      ∃ a ∈ Gamma.source,
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ canonicalErasedRepairedEdges
            (EqualInput L hL) (ActiveWarp hL M)) a D.deleted.head)
    (repairBackward : ∀ (b : V)
      (D : L.MaximalActiveTargetAmbientDefect hL M T b)
      (r : WarpPath (ActiveWarp hL M)),
      (D.tail, D.deleted.head) ∈
        (canonicalErasedRoute
          (EqualInput L hL) (ActiveWarp hL M) r).directionEdges .backward →
      ∃ a ∈ Gamma.source,
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ canonicalErasedRepairedEdges
            (EqualInput L hL) (ActiveWarp hL M)) a D.deleted.head)
    (repairForwardTail : ∀ (b : V)
      (D : L.MaximalActiveTargetAmbientDefect hL M T b)
      (r : WarpPath (ActiveWarp hL M)) (f : V × V),
      f ∈ (canonicalErasedRoute
        (EqualInput L hL) (ActiveWarp hL M) r).directionEdges .forward →
      D.tail = f.1 →
      ∃ a ∈ Gamma.source,
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ canonicalErasedRepairedEdges
            (EqualInput L hL) (ActiveWarp hL M)) a D.deleted.head)
    (repairForwardHead : ∀ (b : V)
      (D : L.MaximalActiveTargetAmbientDefect hL M T b)
      (r : WarpPath (ActiveWarp hL M)) (f : V × V),
      f ∈ (canonicalErasedRoute
        (EqualInput L hL) (ActiveWarp hL M) r).directionEdges .forward →
      D.deleted.head = f.2 →
      ∃ a ∈ Gamma.source,
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ canonicalErasedRepairedEdges
            (EqualInput L hL) (ActiveWarp hL M)) a D.deleted.head) :
    ∃ H : Set Gamma.DPath, Gamma.IsHindrance H := by
  apply R.exists_hindrance_of_maximalActive_targetDefectRepairs M T
  intro b D
  rcases D.incomingOutcome with hout | ⟨r, hr⟩ |
      ⟨r, f, hf, htail⟩ | ⟨r, f, hf, hhead⟩
  · exact repairOutside b D hout
  · exact repairBackward b D r hr
  · exact repairForwardTail b D r f hf htail
  · exact repairForwardHead b D r f hf hhead

/-- The four local target-defect repairs bundled after all stationary and
maximal-family choices have been made. -/
structure EqualMaximalActiveTargetOutcomeRepairs
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (q : FinitePath (EqualInput L hL).lambda.graph)
    (hqsource : q.start ∈ (EqualInput L hL).lambda.source)
    (R : L.ReservedGroundedParent hL q hqsource)
    (M : Popular.MaximalDecodedTargetPureAvoidingRestrictedXSWarp
      (EqualInput L hL)
      ((EqualInput L hL).lambda.source \ {q.start})
      (collisionCarrier (EqualInput L hL) q))
    (T : L.MinimalReachableTargetBoundary hL) where
  outside : ∀ (b : V)
    (D : L.MaximalActiveTargetAmbientDefect hL M T b),
    (D.tail, D.deleted.head) ∉ (EqualInput L hL).familyEdges →
    ∃ a ∈ Gamma.source,
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ canonicalErasedRepairedEdges
          (EqualInput L hL) (ActiveWarp hL M)) a D.deleted.head
  backward : ∀ (b : V)
    (D : L.MaximalActiveTargetAmbientDefect hL M T b)
    (r : WarpPath (ActiveWarp hL M)),
    (D.tail, D.deleted.head) ∈
      (canonicalErasedRoute
        (EqualInput L hL) (ActiveWarp hL M) r).directionEdges .backward →
    ∃ a ∈ Gamma.source,
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ canonicalErasedRepairedEdges
          (EqualInput L hL) (ActiveWarp hL M)) a D.deleted.head
  forwardTail : ∀ (b : V)
    (D : L.MaximalActiveTargetAmbientDefect hL M T b)
    (r : WarpPath (ActiveWarp hL M)) (f : V × V),
    f ∈ (canonicalErasedRoute
      (EqualInput L hL) (ActiveWarp hL M) r).directionEdges .forward →
    D.tail = f.1 →
    ∃ a ∈ Gamma.source,
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ canonicalErasedRepairedEdges
          (EqualInput L hL) (ActiveWarp hL M)) a D.deleted.head
  forwardHead : ∀ (b : V)
    (D : L.MaximalActiveTargetAmbientDefect hL M T b)
    (r : WarpPath (ActiveWarp hL M)) (f : V × V),
    f ∈ (canonicalErasedRoute
      (EqualInput L hL) (ActiveWarp hL M) r).directionEdges .forward →
    D.deleted.head = f.2 →
    ∃ a ∈ Gamma.source,
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ canonicalErasedRepairedEdges
          (EqualInput L hL) (ActiveWarp hL M)) a D.deleted.head

namespace EqualMaximalActiveTargetOutcomeRepairs

variable {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
  {q : FinitePath (EqualInput L hL).lambda.graph}
  {hqsource : q.start ∈ (EqualInput L hL).lambda.source}
  {R : L.ReservedGroundedParent hL q hqsource}
  {M : Popular.MaximalDecodedTargetPureAvoidingRestrictedXSWarp
    (EqualInput L hL)
    ((EqualInput L hL).lambda.source \ {q.start})
    (collisionCarrier (EqualInput L hL) q)}
  {T : L.MinimalReachableTargetBoundary hL}

theorem exists_hindrance
    (C : L.EqualMaximalActiveTargetOutcomeRepairs hL q hqsource R M T) :
    ∃ H : Set Gamma.DPath, Gamma.IsHindrance H :=
  R.exists_hindrance_of_maximalActive_targetOutcomeRepairs M T
    C.outside C.backward C.forwardTail C.forwardHead

end EqualMaximalActiveTargetOutcomeRepairs

/-- End-to-end lift of the concrete four-way target repair interface through
the stationary thinning, reserved parent, maximal decoded extension, and
minimal reachable target choices. -/
theorem exists_hindrance_of_targetPure_stationary_equalSubwarp_of_maximalActive_targetOutcomeRepairs
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (P : Popular.XSWarp
      (EqualInput L hL).lambda (EqualInput L hL).lambda.target)
    (hpure : ∀ p ∈ P.paths, (EqualInput L hL).IsTargetPure p)
    (hstat : Stationary.IsStationaryBelow kappa
      (Popular.initialIndicesOf (L.popularAuxiliaryIndexed hL)
        ((L.popularAuxiliaryIndexed hL).equalSubwarp P).paths
        ((L.popularAuxiliaryIndexed hL).equalSubwarp P).starts_in_source))
    (build : ∀
      (q : FinitePath (EqualInput L hL).lambda.graph)
      (hq : q ∈ ((L.popularAuxiliaryIndexed hL).equalSubwarp P).paths)
      (Q : Popular.XSWarp
        (EqualInput L hL).lambda (EqualInput L hL).lambda.target),
      Q.paths ⊆ ((L.popularAuxiliaryIndexed hL).equalSubwarp P).paths →
      (∀ p ∈ Q.paths, (EqualInput L hL).IsTargetPure p) →
      Stationary.IsStationaryBelow kappa
        (Popular.initialIndicesOf (L.popularAuxiliaryIndexed hL)
          ((L.popularAuxiliaryIndexed hL).equalSubwarp Q).paths
          ((L.popularAuxiliaryIndexed hL).equalSubwarp Q).starts_in_source) →
      Q.paths.PairwiseDisjoint (EqualInput L hL).decodedVertexCarrier →
      (∀ p ∈ Q.paths,
        Disjoint p.support (collisionCarrier (EqualInput L hL) q)) →
      ∀ R : L.ReservedGroundedParent hL q
          (((L.popularAuxiliaryIndexed hL).equalSubwarp P).starts_in_source hq),
      ∀ M : Popular.MaximalDecodedTargetPureAvoidingRestrictedXSWarp
          (EqualInput L hL)
          ((EqualInput L hL).lambda.source \ {q.start})
          (collisionCarrier (EqualInput L hL) q),
      Q.paths ⊆ M.paths →
      ∀ T : L.MinimalReachableTargetBoundary hL,
        Nonempty (L.EqualMaximalActiveTargetOutcomeRepairs hL q
          (((L.popularAuxiliaryIndexed hL).equalSubwarp P).starts_in_source hq)
          R M T)) :
    ∃ H : Set Gamma.DPath, Gamma.IsHindrance H := by
  obtain ⟨q, hq, Q, hQP, hQpure, hQstat, hQdisjoint, hQavoid⟩ :=
    L.exists_reserved_targetPure_stationary_equalSubwarp hL P hpure hstat
  obtain ⟨R⟩ := L.reservedGroundedParent_nonempty hL q
    (((L.popularAuxiliaryIndexed hL).equalSubwarp P).starts_in_source hq)
  obtain ⟨M, hQM⟩ :=
    L.exists_reservedMaximalDecodedTargetPureAvoidingSupply hL q Q
      hQdisjoint hQpure hQavoid
  obtain ⟨T⟩ := L.exists_minimalReachableTargetBoundary hL
  exact (build q hq Q hQP hQpure hQstat hQdisjoint hQavoid R M hQM T).some
    |>.exists_hindrance

end DWeb.KappaLadder
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.MaximalActiveTargetAmbientDefect.target_rooted
#print axioms
  Erdos599.DWeb.KappaLadder.maximalActive_target_rooted_or_ambientDefect
#print axioms
  Erdos599.DWeb.KappaLadder.ReservedGroundedParent.exists_hindrance_of_maximalActive_targetDefectRepairs
#print axioms
  Erdos599.DWeb.KappaLadder.MaximalActiveTargetAmbientDefect.incomingOutcome
#print axioms
  Erdos599.DWeb.KappaLadder.ReservedGroundedParent.exists_hindrance_of_maximalActive_targetOutcomeRepairs
#print axioms
  Erdos599.DWeb.KappaLadder.EqualMaximalActiveTargetOutcomeRepairs.exists_hindrance
#print axioms
  Erdos599.DWeb.KappaLadder.exists_hindrance_of_targetPure_stationary_equalSubwarp_of_maximalActive_targetOutcomeRepairs
