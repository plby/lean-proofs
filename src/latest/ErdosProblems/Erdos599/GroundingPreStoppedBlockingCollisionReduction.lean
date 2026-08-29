/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingPreStoppedFirstCollisionOrder
import ErdosProblems.Erdos599.GroundingPreStoppedFiniteExchange

/-!
# Normal form for pre-stopped collisions leaving a blocking point

After replacing an ordered boundary collision by its first distinct boundary
hit, a collision from a blocking point to a finite cut source has only two
forms.  A residual-only collision gives the private finite-source exchange,
while a nonresidual collision has a named active selected route whose first
forward edge leaves exactly at the blocking point.
-/

noncomputable section

open Set

namespace Erdos599
namespace DWeb.KappaLadder
namespace Assertion822PreStoppedBoundaryObstruction

open Alternating GroundingErasedDecode

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

/-- The switch-ready private exchange produced by a finite-source duplicate. -/
def PrivateDecodedFiniteExchange
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    (o : L.Assertion822PreStoppedBoundaryObstruction hL S R) : Prop :=
  ∃ (q : _root_.Erdos599.DirectedPath.FinitePath
        (L.popularAuxiliaryInput hL.legal).lambda.graph)
      (A : AltPath Gamma.graph) (y : V),
    q.start = .old o.later ∧
    q.finish ∈ (L.popularAuxiliaryInput hL.legal).lambda.target ∧
    (L.popularAuxiliaryInput hL.legal).lambda.Avoids q
      (S.cut \ {(.old o.later :
        (L.popularAuxiliaryInput hL.legal).LV)}) ∧
    q.support ∩ S.cut =
      {(.old o.later : (L.popularAuxiliaryInput hL.legal).LV)} ∧
    A.initial = o.later ∧ A.terminal? = some y ∧
    y ∈ (L.popularAuxiliaryInput hL.legal).targetMarkers ∧
    BackwardLinksOn (L.popularAuxiliaryInput hL.legal).ladder.paths A

/-- The strengthened finite exchange retains the genuine finite trace, its
fresh terminal marker, and both endpoint incidences with the limiting
ladder. -/
def PrivateFiniteExchange
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    (o : L.Assertion822PreStoppedBoundaryObstruction hL S R) : Prop :=
  ∃ (q : _root_.Erdos599.DirectedPath.FinitePath
        (L.popularAuxiliaryInput hL.legal).lambda.graph)
      (Q : FiniteTrace Gamma.graph) (y : V),
    q.start = .old o.later ∧
    q.finish ∈ (L.popularAuxiliaryInput hL.legal).lambda.target ∧
    (L.popularAuxiliaryInput hL.legal).lambda.Avoids q
      (S.cut \ {(.old o.later :
        (L.popularAuxiliaryInput hL.legal).LV)}) ∧
    q.support ∩ S.cut =
      {(.old o.later : (L.popularAuxiliaryInput hL.legal).LV)} ∧
    (L.popularAuxiliaryInput hL.legal).IsTargetPure q ∧
    (AltPath.finite Q).initial = o.later ∧
    (AltPath.finite Q).terminal? = some y ∧
    y ∈ (L.popularAuxiliaryInput hL.legal).targetMarkers ∧
    o.later ∈ Gamma.terminalFrontier
      (L.popularAuxiliaryInput hL.legal).ladder.paths ∧
    y ∈ Gamma.initialSet
      (L.popularAuxiliaryInput hL.legal).ladder.paths ∧
    (∀ z, (y, z) ∉ (AltPath.finite Q).directionEdges .forward) ∧
    (∃ P : (L.popularAuxiliaryInput hL.legal).Fragment,
      P ∈ GroundingCut.G0
        (L.popularAuxiliaryInput hL.legal) S.cut ∧
      GroundingCut.blockingPoint
        (L.popularAuxiliaryInput hL.legal) S.cut P = o.earlier ∧
      P.path.terminal? = some o.later ∧
      y ∉ P.parent.support) ∧
    BackwardLinksOn
      (L.popularAuxiliaryInput hL.legal).ladder.paths (.finite Q)

/-- The first nonresidual departure of a normalized collision is a selected
forward edge leaving its earlier boundary point. -/
def FirstSelectedDeparture
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    {o : L.Assertion822PreStoppedBoundaryObstruction hL S R}
    (D : FirstBoundaryReduction o) : Prop :=
  ∃ (c : ActiveControlRequestAt
        (L.popularAuxiliaryIndexed hL) S
        (L.reservedGroundedControls hL S R) (∅ : Set V))
      (v : V),
    (D.reduced.earlier, v) ∈
      (selectedErasedCompression
        (L.popularAuxiliaryIndexed hL) S
        (L.reservedGroundedControls hL S R)
        (chosenRequest c.1)).path.directionEdges .forward ∧
    (D.reduced.earlier, v) ∈ D.path.edgeSet ∧
    Relation.ReflTransGen
      (fun x y ↦ (x, y) ∈
        L.assertion822ReservedPreStoppedEdges hL S R)
      v D.reduced.later

/-- The finite later-boundary case is completely reduced to a private
decoded exchange or a selected route departing at the blocker. -/
theorem FirstBoundaryReduction.privateExchange_or_selectedDeparture
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    {o : L.Assertion822PreStoppedBoundaryObstruction hL S R}
    (D : FirstBoundaryReduction o)
    (hearlier : BlockingCase hL S D.reduced.earlier)
    (hlater : FiniteCase hL S D.reduced.later) :
    PrivateDecodedFiniteExchange D.reduced ∨ FirstSelectedDeparture D := by
  obtain ⟨P, hPG0, hblockable, hpoint, _hmem⟩ := hearlier
  rcases D.residual_or_selectedForward_from_blocker
      P hPG0 hblockable hpoint with hresidual | hselected
  · left
    exact exists_private_decoded_exchange_of_residual_blocking_finite
      D.reduced P hPG0 hblockable hpoint hlater hresidual
  · exact Or.inr hselected

/-- Strengthened form retaining the complete finite-trace exchange payload. -/
theorem FirstBoundaryReduction.privateFiniteExchange_or_selectedDeparture
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    {o : L.Assertion822PreStoppedBoundaryObstruction hL S R}
    (D : FirstBoundaryReduction o)
    (hearlier : BlockingCase hL S D.reduced.earlier)
    (hlater : FiniteCase hL S D.reduced.later) :
    (BlockingFiniteTerminalCase D.reduced ∧
      PrivateFiniteExchange D.reduced) ∨ FirstSelectedDeparture D := by
  obtain ⟨P, hPG0, hblockable, hpoint, _hmem⟩ := hearlier
  rcases D.residual_or_selectedForward_from_blocker
      P hPG0 hblockable hpoint with hresidual | hselected
  · left
    let hcase := blockingFiniteTerminalCase_of_residual_reach
      D.reduced P hPG0 hblockable hpoint hlater hresidual
    exact ⟨hcase,
      exists_private_finite_exchange_of_blocking_finite_terminal
        D.reduced hcase⟩
  · exact Or.inr hselected

/-- A normalized collision leaving a blocker is either already a private
finite exchange, has an exact selected departure, or ends in one of the two
remaining non-finite boundary classes. -/
def BlockingFirstBoundaryOutcome
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    {o : L.Assertion822PreStoppedBoundaryObstruction hL S R}
    (D : FirstBoundaryReduction o) : Prop :=
  PrivateFiniteExchange D.reduced ∨
    FirstSelectedDeparture D ∨
    ControlCase hL S D.reduced.later ∨
    BlockingCase hL S D.reduced.later

/-- Lossless first-hit classification of a collision whose earlier endpoint
is a blocking point. -/
theorem FirstBoundaryReduction.blockingOutcome
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    {o : L.Assertion822PreStoppedBoundaryObstruction hL S R}
    (D : FirstBoundaryReduction o)
    (hearlier : BlockingCase hL S D.reduced.earlier) :
    BlockingFirstBoundaryOutcome D := by
  have hlater := boundaryCase_of_mem_BB D.reduced.later_mem
  change FiniteCase hL S D.reduced.later ∨
      ControlCase hL S D.reduced.later ∨
      BlockingCase hL S D.reduced.later at hlater
  rcases hlater with hfinite | hcontrol | hblocking
  · rcases D.privateFiniteExchange_or_selectedDeparture
      hearlier hfinite with ⟨_hcase, hexchange⟩ | hselected
    · exact Or.inl hexchange
    · exact Or.inr (Or.inl hselected)
  · exact Or.inr (Or.inr (Or.inl hcontrol))
  · exact Or.inr (Or.inr (Or.inr hblocking))

/-- Every collision starting at a blocker admits the normalized outcome
above. -/
theorem exists_firstBlockingBoundaryOutcome
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    (o : L.Assertion822PreStoppedBoundaryObstruction hL S R)
    (hearlier : BlockingCase hL S o.earlier) :
    ∃ D : FirstBoundaryReduction o, BlockingFirstBoundaryOutcome D := by
  obtain ⟨D⟩ := exists_firstBoundaryReduction o
  have hearlier' : BlockingCase hL S D.reduced.earlier := by
    simpa only [D.earlier_eq] using hearlier
  exact ⟨D, D.blockingOutcome hearlier'⟩

/-- Total first-hit normal form for an arbitrary ordered boundary
obstruction.  The only unresolved coarse starts are a finite source or an
old control.  A blocking start is refined all the way to the exchange,
selected-departure, control, or blocking alternatives above. -/
inductive FirstBoundaryFailureOutcome
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    (o : L.Assertion822PreStoppedBoundaryObstruction hL S R) : Prop
  | earlierFinite
      (D : FirstBoundaryReduction o)
      (earlier : FiniteCase hL S D.reduced.earlier)
  | earlierControl
      (D : FirstBoundaryReduction o)
      (earlier : ControlCase hL S D.reduced.earlier)
  | privateFinite
      (D : FirstBoundaryReduction o)
      (collision : BlockingFiniteTerminalCase D.reduced)
      (exchange : PrivateFiniteExchange D.reduced)
  | selectedDeparture
      (D : FirstBoundaryReduction o)
      (departure : FirstSelectedDeparture D)
  | blockingToControl
      (D : FirstBoundaryReduction o)
      (earlier : BlockingCase hL S D.reduced.earlier)
      (later : ControlCase hL S D.reduced.later)
  | blockingToBlocking
      (D : FirstBoundaryReduction o)
      (earlier : BlockingCase hL S D.reduced.earlier)
      (later : BlockingCase hL S D.reduced.later)

/-- Every ordered boundary obstruction admits the total first-hit normal
form. -/
theorem firstBoundaryFailureOutcome
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    (o : L.Assertion822PreStoppedBoundaryObstruction hL S R) :
    FirstBoundaryFailureOutcome o := by
  obtain ⟨D⟩ := exists_firstBoundaryReduction o
  have hearlier := boundaryCase_of_mem_BB D.reduced.earlier_mem
  change FiniteCase hL S D.reduced.earlier ∨
      ControlCase hL S D.reduced.earlier ∨
      BlockingCase hL S D.reduced.earlier at hearlier
  rcases hearlier with hfinite | hcontrol | hblocking
  · exact .earlierFinite D hfinite
  · exact .earlierControl D hcontrol
  · have hlater := boundaryCase_of_mem_BB D.reduced.later_mem
    change FiniteCase hL S D.reduced.later ∨
        ControlCase hL S D.reduced.later ∨
        BlockingCase hL S D.reduced.later at hlater
    rcases hlater with hlaterFinite | hlaterControl | hlaterBlocking
    · rcases D.privateFiniteExchange_or_selectedDeparture
        hblocking hlaterFinite with ⟨hcase, hexchange⟩ | hdeparture
      · exact .privateFinite D hcase hexchange
      · exact .selectedDeparture D hdeparture
    · exact .blockingToControl D hblocking hlaterControl
    · exact .blockingToBlocking D hblocking hlaterBlocking

end Assertion822PreStoppedBoundaryObstruction
end DWeb.KappaLadder
end Erdos599

#print axioms Erdos599.DWeb.KappaLadder.Assertion822PreStoppedBoundaryObstruction.FirstBoundaryReduction.privateExchange_or_selectedDeparture
#print axioms Erdos599.DWeb.KappaLadder.Assertion822PreStoppedBoundaryObstruction.FirstBoundaryReduction.privateFiniteExchange_or_selectedDeparture
#print axioms Erdos599.DWeb.KappaLadder.Assertion822PreStoppedBoundaryObstruction.exists_firstBlockingBoundaryOutcome
#print axioms Erdos599.DWeb.KappaLadder.Assertion822PreStoppedBoundaryObstruction.firstBoundaryFailureOutcome
