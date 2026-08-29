/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingPreStoppedRealization
import ErdosProblems.Erdos599.GroundingFiniteSourceDuplicateExchange

/-!
# Concrete cases of an ordered pre-stopped boundary collision

An `Assertion822PreStoppedBoundaryObstruction` remembers two distinct points
of `BB` and a directed reachability witness from the first to the second.
This file expands both boundary memberships into the three source-level
classes used by the grounding decoder: a cut finite source, an old-request
control, or the blocking point of a blockable retained fragment.  The
classification retains all endpoint equalities as well as the original
ordered reachability proof.

The blocking--finite mixed case has a direct exchange interpretation when
the later finite source is the terminal of the displayed earlier fragment.
Distinctness then forces that fragment to meet the escape region, and the
finite-source duplicate compiler supplies a cut-private auxiliary
source--target path (and its loop-erased alternating decode).  Ordered
reachability alone does not identify the later point with that fragment's
terminal, so the exact terminal-incidence hypothesis remains explicit.
-/

noncomputable section

open Set

namespace Erdos599
namespace DWeb.KappaLadder

open Alternating GroundingErasedDecode GroundingFiniteSourceDuplicateExchange
  PopularGroundingBridge

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace Assertion822PreStoppedBoundaryObstruction

/-- The finite-source alternative for one endpoint of a pre-stopped
boundary collision.  The old-gadget cut membership is retained. -/
def FiniteCase
    {L : Gamma.KappaLadder kappa} (hL : L.IsKappaHindrance)
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    (x : V) : Prop :=
  x ∈ (L.popularAuxiliaryInput hL.legal).finiteSource ∧
    (PopularAuxiliary.Input.LambdaVertex.old x :
      (L.popularAuxiliaryInput hL.legal).LV) ∈ S.cut

/-- The actual old-request alternative for one endpoint.  The equality
identifies the untagged control vertex with the displayed endpoint. -/
def ControlCase
    {L : Gamma.KappaLadder kappa} (hL : L.IsKappaHindrance)
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    (x : V) : Prop :=
  ∃ c : ControlRequest (L.popularAuxiliaryInput hL.legal) S.cut,
    c.1 = x

/-- The blocking-point alternative for one endpoint.  This retains the
fragment, `G0` membership, blockability, the endpoint equality, and support
membership, so later geometry need not reopen the image definition of
`BL`. -/
def BlockingCase
    {L : Gamma.KappaLadder kappa} (hL : L.IsKappaHindrance)
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    (x : V) : Prop :=
  ∃ P : (L.popularAuxiliaryInput hL.legal).Fragment,
    P ∈ GroundingCut.G0 (L.popularAuxiliaryInput hL.legal) S.cut ∧
    GroundingCut.IsBlockable
      (L.popularAuxiliaryInput hL.legal) S.cut P ∧
    GroundingCut.blockingPoint
      (L.popularAuxiliaryInput hL.legal) S.cut P = x ∧
    x ∈ P.path.support

/-- The lossless three-way classification of one point of `BB`. -/
def BoundaryCase
    {L : Gamma.KappaLadder kappa} (hL : L.IsKappaHindrance)
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    (x : V) : Prop :=
  FiniteCase hL S x ∨ ControlCase hL S x ∨ BlockingCase hL S x

/-- Expand a literal `BB` membership into the finite/control/blocking
classification used below. -/
theorem boundaryCase_of_mem_BB
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {x : V}
    (hx : x ∈ GroundingCut.BB
      (L.popularAuxiliaryInput hL.legal) S.cut) :
    BoundaryCase hL S x := by
  change FiniteCase hL S x ∨ ControlCase hL S x ∨ BlockingCase hL S x
  rcases
      GroundingBBGeometry.mem_BB_finiteSourceWithCut_or_oldRequestExit_or_blockingPoint
        hx with hfinite | hold | hblocking
  · exact Or.inl ⟨hfinite.1, hfinite.2⟩
  · right
    left
    obtain ⟨r, haux, hexit⟩ := hold
    cases r with
    | inl r =>
        refine ⟨oldRequestControl r, ?_⟩
        simpa only [oldRequestControl_val, requestExit] using hexit
    | inr r => cases haux
  · right
    right
    obtain ⟨P, hPG0, hPblockable, hPx, hxSupport⟩ := hblocking
    exact ⟨P, hPG0, hPblockable, hPx, hxSupport⟩

/-- Both classified endpoints together with the exact inequality and
ordered reachability carried by the original obstruction. -/
structure OrderedCases
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    (o : L.Assertion822PreStoppedBoundaryObstruction hL S R) : Prop where
  earlier_case : BoundaryCase hL S o.earlier
  later_case : BoundaryCase hL S o.later
  distinct : o.earlier ≠ o.later
  reaches : Relation.ReflTransGen
    (fun x y ↦
      (x, y) ∈ L.assertion822ReservedPreStoppedEdges hL S R)
    o.earlier o.later

/-- Lossless classification of an ordered boundary obstruction.  Pattern
matching the two `BoundaryCase` fields gives the nine concrete mixed cases
without losing either endpoint equality or the reachability witness. -/
theorem orderedCases
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    (o : L.Assertion822PreStoppedBoundaryObstruction hL S R) :
    OrderedCases o where
  earlier_case := boundaryCase_of_mem_BB o.earlier_mem
  later_case := boundaryCase_of_mem_BB o.later_mem
  distinct := o.distinct
  reaches := o.reaches

/-- Exact refinement of the blocking--finite mixed branch for which the
finite-source duplicate compiler applies: the later endpoint is the terminal
of the fragment whose blocking point is the earlier endpoint. -/
def BlockingFiniteTerminalCase
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    (o : L.Assertion822PreStoppedBoundaryObstruction hL S R) : Prop :=
  ∃ P : (L.popularAuxiliaryInput hL.legal).Fragment,
    P ∈ GroundingCut.G0 (L.popularAuxiliaryInput hL.legal) S.cut ∧
    GroundingCut.IsBlockable
      (L.popularAuxiliaryInput hL.legal) S.cut P ∧
    GroundingCut.blockingPoint
      (L.popularAuxiliaryInput hL.legal) S.cut P = o.earlier ∧
    P.path.terminal? = some o.later ∧
    FiniteCase hL S o.later

/-- In the blocking--finite mixed case, if the later endpoint is the
terminal of the displayed earlier fragment, distinctness forces the
fragment to meet the escape region. -/
theorem meetsEscape_of_blocking_finite_terminal
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    (o : L.Assertion822PreStoppedBoundaryObstruction hL S R)
    {P : (L.popularAuxiliaryInput hL.legal).Fragment}
    (hblockingPoint : GroundingCut.blockingPoint
      (L.popularAuxiliaryInput hL.legal) S.cut P = o.earlier)
    (hterminal : P.path.terminal? = some o.later) :
    PopularAuxiliary.Input.Fragment.MeetsEscape
      (L.popularAuxiliaryInput hL.legal) S.cut P := by
  by_contra hnoEscape
  apply o.distinct
  exact hblockingPoint.symm.trans
    (GroundingCut.blockingPoint_eq_terminal_of_not_meetsEscape
      (L.popularAuxiliaryInput hL.legal) S.cut P
        hnoEscape hterminal)

/-- The blocking--finite terminal collision yields the private auxiliary
source--target path used by the finite-source duplicate exchange. -/
theorem exists_private_source_target_path_of_blocking_finite_terminal
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    (o : L.Assertion822PreStoppedBoundaryObstruction hL S R)
    (hcase : BlockingFiniteTerminalCase o) :
    ∃ q : _root_.Erdos599.DirectedPath.FinitePath
        (L.popularAuxiliaryInput hL.legal).lambda.graph,
      q.start ∈ (L.popularAuxiliaryInput hL.legal).lambda.source ∧
      q.finish ∈ (L.popularAuxiliaryInput hL.legal).lambda.target ∧
      (L.popularAuxiliaryInput hL.legal).lambda.Avoids q
        (S.cut \ {(.old o.later :
          (L.popularAuxiliaryInput hL.legal).LV)}) ∧
      q.support ∩ S.cut =
        {(.old o.later : (L.popularAuxiliaryInput hL.legal).LV)} := by
  obtain ⟨P, hPG0, hPblockable, hPearly, hterminal, hlater⟩ := hcase
  apply
    exists_private_source_target_path_of_finiteSource_duplicate
      (L.popularAuxiliaryInput hL.legal) S.cut P hPG0.1 hterminal
        (meetsEscape_of_blocking_finite_terminal o hPearly hterminal)
        hlater.1 (GroundingCut.mem_CV.mpr hlater.2)
  intro heq
  exact o.distinct (hPearly.symm.trans heq)

/-- Switch-ready form of the same mixed collision: the private path comes
with its loop-erased alternating decode, target-marker endpoint, and exact
backward-link provenance on the limiting ladder. -/
theorem exists_private_decoded_exchange_of_blocking_finite_terminal
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    (o : L.Assertion822PreStoppedBoundaryObstruction hL S R)
    (hcase : BlockingFiniteTerminalCase o) :
    ∃ (q : _root_.Erdos599.DirectedPath.FinitePath
          (L.popularAuxiliaryInput hL.legal).lambda.graph)
        (A : Alternating.AltPath Gamma.graph) (y : V),
      q.start = .old o.later ∧
      q.finish ∈ (L.popularAuxiliaryInput hL.legal).lambda.target ∧
      (L.popularAuxiliaryInput hL.legal).lambda.Avoids q
        (S.cut \ {(.old o.later :
          (L.popularAuxiliaryInput hL.legal).LV)}) ∧
      q.support ∩ S.cut =
        {(.old o.later : (L.popularAuxiliaryInput hL.legal).LV)} ∧
      A.initial = o.later ∧ A.terminal? = some y ∧
      y ∈ (L.popularAuxiliaryInput hL.legal).targetMarkers ∧
      Alternating.BackwardLinksOn
        (L.popularAuxiliaryInput hL.legal).ladder.paths A := by
  obtain ⟨P, hPG0, hPblockable, hPearly, hterminal, hlater⟩ := hcase
  obtain ⟨q, A, y, hstart, hfinish, havoid, hcut, _hpure, hinitial,
      hterminalA, hmarker, _hstop, hback⟩ :=
    exists_private_decoded_exchange_of_finiteSource_duplicate
      (L.popularAuxiliaryInput hL.legal) S.cut P hPG0.1 hterminal
        (meetsEscape_of_blocking_finite_terminal o hPearly hterminal)
        hlater.1 (GroundingCut.mem_CV.mpr hlater.2) (by
          intro heq
          exact o.distinct (hPearly.symm.trans heq))
  exact ⟨q, A, y, hstart, hfinish, havoid, hcut, hinitial,
    hterminalA, hmarker, hback⟩

#print axioms orderedCases
#print axioms exists_private_decoded_exchange_of_blocking_finite_terminal

end Assertion822PreStoppedBoundaryObstruction
end DWeb.KappaLadder
end Erdos599
