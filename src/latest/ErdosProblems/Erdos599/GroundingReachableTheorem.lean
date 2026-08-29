/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingEqualMaximalTargetDefect
import ErdosProblems.Erdos599.GroundingPreStoppedBackwardSelfNormalizedOutcome
import ErdosProblems.Erdos599.GroundingPreStoppedAmbientPrefixExchange
import ErdosProblems.Erdos599.GroundingPreStoppedReachableBoundaryReduction
import ErdosProblems.Erdos599.GroundingPreStoppedReachableEssentialDeletedHead
import ErdosProblems.Erdos599.GroundingPreStoppedReachableWholeSourceDeletedHead
import ErdosProblems.Erdos599.GroundingTheorem

/-!
# Final grounding interface at the reachable target boundary

This module combines the sound minimal target-only equal-stage compiler with the
failure-oriented separator compiler.  In particular, it does not assume
that every control exit or every limiting-ladder parent initial is already
rooted.  Active failures retain their exact selected initial/backward-owner
anchor and can therefore be handled by the construction-specific descending
repair.

The collision hull is used only as routing metadata by
`EqualMinimalTargetPreStoppedCompiler`; the separating boundary is a selected
minimal subset of the source-reachable essential terminal cut.
-/

noncomputable section

open Set

namespace Erdos599
namespace DWeb.KappaLadder

open GroundingEqualActiveSelection

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

/-- Exact builder for the minimal source-reachable target-only equal-stage
compiler.
The selected stationary family, reserved grounded parent, and maximal
collision-avoiding supply are chosen by the existing reduction; a producer
only supplies the final active relation and its local absorption facts. -/
structure ReachableTargetEqualCompilerSupply
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance) where
  build : ∀
    (P : Popular.XSWarp
      (EqualInput L hL).lambda (EqualInput L hL).lambda.target)
    (_hpure : ∀ p ∈ P.paths, (EqualInput L hL).IsTargetPure p)
    (_hstat : Stationary.IsStationaryBelow kappa
      (Popular.initialIndicesOf (L.popularAuxiliaryIndexed hL)
        ((L.popularAuxiliaryIndexed hL).equalSubwarp P).paths
        ((L.popularAuxiliaryIndexed hL).equalSubwarp P).starts_in_source))
    (q : DirectedPath.FinitePath (EqualInput L hL).lambda.graph)
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
      Nonempty (L.EqualMinimalTargetPreStoppedCompiler hL q
        (((L.popularAuxiliaryIndexed hL).equalSubwarp P).starts_in_source hq)
        R M T)

/-- All standard choices made by the equal-stage reduction, retained as one
dependent record so that the four literal deleted-edge repairs can share the
same selected stationary family, reserved parent, maximal extension, and
minimal reachable target boundary. -/
structure ReachableTargetEqualDefectContext
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance) where
  P : Popular.XSWarp
    (EqualInput L hL).lambda (EqualInput L hL).lambda.target
  hpure : ∀ p ∈ P.paths, (EqualInput L hL).IsTargetPure p
  hstat : Stationary.IsStationaryBelow kappa
    (Popular.initialIndicesOf (L.popularAuxiliaryIndexed hL)
      ((L.popularAuxiliaryIndexed hL).equalSubwarp P).paths
      ((L.popularAuxiliaryIndexed hL).equalSubwarp P).starts_in_source)
  q : DirectedPath.FinitePath (EqualInput L hL).lambda.graph
  hq : q ∈ ((L.popularAuxiliaryIndexed hL).equalSubwarp P).paths
  Q : Popular.XSWarp
    (EqualInput L hL).lambda (EqualInput L hL).lambda.target
  Q_sub : Q.paths ⊆
    ((L.popularAuxiliaryIndexed hL).equalSubwarp P).paths
  Q_targetPure : ∀ p ∈ Q.paths, (EqualInput L hL).IsTargetPure p
  Q_stationary : Stationary.IsStationaryBelow kappa
    (Popular.initialIndicesOf (L.popularAuxiliaryIndexed hL)
      ((L.popularAuxiliaryIndexed hL).equalSubwarp Q).paths
      ((L.popularAuxiliaryIndexed hL).equalSubwarp Q).starts_in_source)
  Q_disjoint :
    Q.paths.PairwiseDisjoint (EqualInput L hL).decodedVertexCarrier
  Q_avoids : ∀ p ∈ Q.paths,
    Disjoint p.support (collisionCarrier (EqualInput L hL) q)
  R : L.ReservedGroundedParent hL q
    (((L.popularAuxiliaryIndexed hL).equalSubwarp P).starts_in_source hq)
  M : Popular.MaximalDecodedTargetPureAvoidingRestrictedXSWarp
    (EqualInput L hL)
    ((EqualInput L hL).lambda.source \ {q.start})
    (collisionCarrier (EqualInput L hL) q)
  Q_sub_M : Q.paths ⊆ M.paths
  T : L.MinimalReachableTargetBoundary hL

/-- The four concrete repairs left by the exact target-defect classification.
Unlike `ReachableTargetEqualCompilerSupply`, this interface does not hide the
equal branch behind a restated compiler: every field receives the literal
last deleted ambient edge and one of its four possible route classifications. -/
structure ReachableTargetEqualDefectRepairs
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance) where
  outside : ∀ (C : ReachableTargetEqualDefectContext L hL) (b : V)
    (D : L.MaximalActiveTargetAmbientDefect hL C.M C.T b),
    (D.tail, D.deleted.head) ∉ (EqualInput L hL).familyEdges →
    ∃ a ∈ Gamma.source,
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ canonicalErasedRepairedEdges
          (EqualInput L hL) (maximalOrderedActiveSubwarp hL C.M))
        a D.deleted.head
  backward : ∀ (C : ReachableTargetEqualDefectContext L hL) (b : V)
    (D : L.MaximalActiveTargetAmbientDefect hL C.M C.T b)
    (r : WarpPath (maximalOrderedActiveSubwarp hL C.M)),
    (D.tail, D.deleted.head) ∈
      (canonicalErasedRoute (EqualInput L hL)
        (maximalOrderedActiveSubwarp hL C.M) r).directionEdges .backward →
    ∃ a ∈ Gamma.source,
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ canonicalErasedRepairedEdges
          (EqualInput L hL) (maximalOrderedActiveSubwarp hL C.M))
        a D.deleted.head
  forwardTail : ∀ (C : ReachableTargetEqualDefectContext L hL) (b : V)
    (D : L.MaximalActiveTargetAmbientDefect hL C.M C.T b)
    (r : WarpPath (maximalOrderedActiveSubwarp hL C.M)) (f : V × V),
    f ∈ (canonicalErasedRoute (EqualInput L hL)
      (maximalOrderedActiveSubwarp hL C.M) r).directionEdges .forward →
    D.tail = f.1 →
    ∃ a ∈ Gamma.source,
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ canonicalErasedRepairedEdges
          (EqualInput L hL) (maximalOrderedActiveSubwarp hL C.M))
        a D.deleted.head
  forwardHead : ∀ (C : ReachableTargetEqualDefectContext L hL) (b : V)
    (D : L.MaximalActiveTargetAmbientDefect hL C.M C.T b)
    (r : WarpPath (maximalOrderedActiveSubwarp hL C.M)) (f : V × V),
    f ∈ (canonicalErasedRoute (EqualInput L hL)
      (maximalOrderedActiveSubwarp hL C.M) r).directionEdges .forward →
    D.deleted.head = f.2 →
    ∃ a ∈ Gamma.source,
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ canonicalErasedRepairedEdges
          (EqualInput L hL) (maximalOrderedActiveSubwarp hL C.M))
        a D.deleted.head

namespace ReachableTargetEqualDefectRepairs

/-- Bundle the four explicit reachable-stage callbacks at one fixed choice
context into the local target-defect repair record. -/
def build
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    (repairs : ReachableTargetEqualDefectRepairs L hL)
    (C : ReachableTargetEqualDefectContext L hL) :
    L.EqualMaximalActiveTargetOutcomeRepairs hL C.q
      (((L.popularAuxiliaryIndexed hL).equalSubwarp C.P).starts_in_source C.hq)
      C.R C.M C.T where
  outside := repairs.outside C
  backward := repairs.backward C
  forwardTail := repairs.forwardTail C
  forwardHead := repairs.forwardHead C

end ReachableTargetEqualDefectRepairs

/-- Lift the four literal deleted-edge repairs through the standard
stationary thinning, reserved-parent, maximal-extension, and minimal-boundary
choices. -/
theorem exists_hindrance_of_targetPure_stationary_equalSubwarp_of_reachableTargetEqualDefectRepairs
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (repairs : ReachableTargetEqualDefectRepairs L hL)
    (P : Popular.XSWarp
      (EqualInput L hL).lambda (EqualInput L hL).lambda.target)
    (hpure : ∀ p ∈ P.paths, (EqualInput L hL).IsTargetPure p)
    (hstat : Stationary.IsStationaryBelow kappa
      (Popular.initialIndicesOf (L.popularAuxiliaryIndexed hL)
        ((L.popularAuxiliaryIndexed hL).equalSubwarp P).paths
        ((L.popularAuxiliaryIndexed hL).equalSubwarp P).starts_in_source)) :
    ∃ H : Set Gamma.DPath, Gamma.IsHindrance H := by
  apply
    L.exists_hindrance_of_targetPure_stationary_equalSubwarp_of_maximalActive_targetOutcomeRepairs
      hL P hpure hstat
  intro q hq Q hQP hQpure hQstat hQdisjoint hQavoid R M hQM T
  let C : ReachableTargetEqualDefectContext L hL := {
    P := P
    hpure := hpure
    hstat := hstat
    q := q
    hq := hq
    Q := Q
    Q_sub := hQP
    Q_targetPure := hQpure
    Q_stationary := hQstat
    Q_disjoint := hQdisjoint
    Q_avoids := hQavoid
    R := R
    M := M
    Q_sub_M := hQM
    T := T }
  exact ⟨repairs.build C⟩

/-- Remaining construction data after all generic reductions.

The equal branch sees only the target-only active-relation compiler.  The
separator branch first restricts the literal boundary to points admitting an
ambient finite path from the original source, then applies the source-faithful
nonessential-boundary compiler.  Its reserved-root callback therefore sees
only an essential, ambient-source-reachable boundary point.  A genuinely
stronger failure -- no root from any original source in the repaired relation
despite such an ambient prefix -- is kept as a separate exact callback.  The
impossible finite-source first endpoint has already been eliminated from the
ordered boundary collision outcome.  Both root callbacks retain the
escape/terminal-split first-fragment parent-initial failure after the
initial-prefix measure has eliminated every repeated self-owned backward
anchor.
Cut-preceded parent leaves have already been returned to control recursion.
Represented-cut and
same-head failures have already
been fed back through every active and inactive control branch, including the
ones reached through a blocking prefix. Every remaining selected-edge
deletion is represented by the same exposed-component owner recursion, and
hanging equality remains explicit. A limiting-ladder parent initial that is
not already rooted is exposed as either the reserved record itself or a
genuinely hanging component. It contains no global `controlRooted` or
`parentRooted` premise. -/
structure ReachableTargetPreStoppedRepairs
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance) where
  equal : ReachableTargetEqualDefectRepairs L hL
  essential : ∀
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    (R : L.UnusedGroundedRecord hL S)
    (O : L.Assertion822ReachableEssentialReservedRootObstruction hL S R),
    O.AmbientDefectOutcome →
    O.obstruction.BackwardSelfNormalizedFirstFragmentRootFailureOutcome →
      ∃ W : Set Gamma.DPath, Gamma.IsHindrance W
  wholeSource : ∀
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    (R : L.UnusedGroundedRecord hL S)
    (O : L.Assertion822ReachableWholeSourceRootObstruction hL S R),
    ∀ data : O.AmbientLastDeletedHeadData,
    O.AmbientDeletedHeadExchangeOutcome data →
    O.obstruction.BackwardSelfNormalizedFirstFragmentRootFailureOutcome →
      ∃ W : Set Gamma.DPath, Gamma.IsHindrance W
  boundary : ∀
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    (R : L.UnusedGroundedRecord hL S)
    (O : L.Assertion822ReachableBoundaryObstruction hL S R),
    O.obstruction.FiniteSinkReducedTerminalFailureOutcome →
      ∃ W : Set Gamma.DPath, Gamma.IsHindrance W

/-- Assemble the source-reachable target-only equal compiler and the
failure-oriented separator compiler into an ordinary hindrance. -/
theorem exists_hindrance_of_reachableTargetPreStoppedRepairs
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (repairs : ReachableTargetPreStoppedRepairs L hL) :
    ∃ W : Set Gamma.DPath, Gamma.IsHindrance W := by
  apply
    L.exists_hindrance_of_targetPureEqualGrounding_and_assertion822_or_hindrance
      hL
  · intro P hPpure hPstat
    exact
      L.exists_hindrance_of_targetPure_stationary_equalSubwarp_of_reachableTargetEqualDefectRepairs
        hL repairs.equal P hPpure hPstat
  · intro S
    exact L.assertion822Output_or_hindrance_of_preStoppedReachableRepairs
      hL S (fun R O outcome ↦ repairs.essential S R O
        O.ambientDefectOutcome outcome)
        (fun R O outcome ↦
          let data := O.exists_ambientLastDeletedHeadData.some
          repairs.wholeSource S R O data
            (O.ambientDeletedHeadExchangeOutcome data) outcome)
        (repairs.boundary S)

end DWeb.KappaLadder
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.exists_hindrance_of_targetPure_stationary_equalSubwarp_of_reachableTargetEqualDefectRepairs
#print axioms
  Erdos599.DWeb.KappaLadder.exists_hindrance_of_reachableTargetPreStoppedRepairs
