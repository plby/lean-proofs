/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingEqualReachableTargetBoundary
import ErdosProblems.Erdos599.GroundingPreStoppedInessentialBoundaryReduction
import ErdosProblems.Erdos599.GroundingPreStoppedBackwardSelfNormalizedOutcome

/-!
# Restricting the pre-stopped boundary to ambient-source-reachable points

The literal bookkeeping boundary `BB` may contain a point on a hanging
component which no original source can reach.  Such a point is irrelevant to
every source--target path, and asking the switched relation to root it is both
unnecessary and in general false.

This file performs the same source-faithful restriction already used by the
equal target-only branch: retain only points of `BB` admitting a finite ambient
path from the original source.  The restricted boundary is still separating,
because any source--target path supplies its own finite prefix to any `BB`
contact.  Consequently every remaining whole-source root obstruction carries
the concrete ambient prefix needed by the hanging-component exchange.
-/

noncomputable section

open Set

namespace Erdos599
namespace DWeb.KappaLadder

open GroundingRootedReachabilityWarp

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

/-- The part of the literal grounding boundary which is relevant to an
ambient source--target path. -/
def reachableBB
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)) : Set V :=
  GroundingCut.BB (L.popularAuxiliaryInput hL.legal) S.cut ∩
    ambientSourceReachable Gamma

/-- Every source--target path meets a literal boundary point which its own
initial segment witnesses to be ambient-source-reachable. -/
theorem reachableBB_isSeparator
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)) :
    Popular.IsSeparator Gamma (L.reachableBB hL S) := by
  intro p hpSource hpTarget
  obtain ⟨x, hxp, hxBB⟩ :=
    GroundingAssertion818Decoder.assertion8_18
      L hL.legal S.cut S.separates p hpSource hpTarget
  obtain ⟨r, hrStart, hrFinish, _hrSupport, _hrEdges⟩ :=
    GroundingPathPrefix.exists_initialFinitePrefix
      (Sum.inl p : Gamma.DPath) (by
        change x ∈ p.support
        exact hxp)
  refine ⟨x, hxp, hxBB, r, ?_, hrFinish⟩
  simpa only [hrStart, DirectedPath.Path.initial] using hpSource

theorem reachableBB_subset_BB
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)) :
    L.reachableBB hL S ⊆
      GroundingCut.BB (L.popularAuxiliaryInput hL.legal) S.cut :=
  Set.inter_subset_left

/-- A reserved-source root failure at the reachable boundary, after the
generic nonessential-point compiler has run. -/
structure Assertion822ReachableEssentialReservedRootObstruction
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    (R : L.UnusedGroundedRecord hL S) where
  obstruction : L.Assertion822PreStoppedRootObstruction hL S R
  boundary_reachable : obstruction.boundary ∈ ambientSourceReachable Gamma
  boundary_essential : obstruction.boundary ∈
    Gamma.essential (L.reachableBB hL S)

namespace Assertion822ReachableEssentialReservedRootObstruction

/-- Unpack the source-reachability retained by the essential reserved-root
obstruction. -/
theorem exists_ambientPath_to_boundary
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    (O : L.Assertion822ReachableEssentialReservedRootObstruction hL S R) :
    ∃ p : DirectedPath.FinitePath Gamma.graph,
      p.start ∈ Gamma.source ∧ p.finish = O.obstruction.boundary :=
  O.boundary_reachable

/-- A source-reachable reserved-root failure has an exact pathwise cause.
Either its ambient prefix starts at the one deliberately reserved source,
or the prefix starts at an allowed source and therefore has a last deleted
incoming edge whose surviving head is still unrooted. -/
theorem reservedPath_or_exists_unrootedLastDeletedHead
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    (O : L.Assertion822ReachableEssentialReservedRootObstruction hL S R) :
    (∃ p : DirectedPath.FinitePath Gamma.graph,
      p.start = R.record.initial ∧
        p.finish = O.obstruction.boundary) ∨
    ∃ p : DirectedPath.FinitePath Gamma.graph,
      p.start ∈ Gamma.source \ {R.record.initial} ∧
        p.finish = O.obstruction.boundary ∧
      ∃ D : LastDeletedHead p
          (L.assertion822ReservedPreStoppedEdges hL S R),
        ¬ ∃ a ∈ Gamma.source \ {R.record.initial},
          Relation.ReflTransGen
            (fun x y ↦
              (x, y) ∈ L.assertion822ReservedPreStoppedEdges hL S R)
            a D.head := by
  obtain ⟨p, hpSource, hpFinish⟩ := O.exists_ambientPath_to_boundary
  by_cases hpReserved : p.start = R.record.initial
  · exact Or.inl ⟨p, hpReserved, hpFinish⟩
  · right
    have hpAllowed : p.start ∈ Gamma.source \ {R.record.initial} := by
      exact ⟨hpSource, by simpa only [Set.mem_singleton_iff] using hpReserved⟩
    have hstart : ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦
            (x, y) ∈ L.assertion822ReservedPreStoppedEdges hL S R)
          a p.start :=
      ⟨p.start, hpAllowed, Relation.ReflTransGen.refl⟩
    have hfinish : ¬ ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦
            (x, y) ∈ L.assertion822ReservedPreStoppedEdges hL S R)
          a p.finish := by
      rintro ⟨a, ha, hareach⟩
      apply O.obstruction.not_rooted
      exact ⟨a, ha, by simpa only [hpFinish] using hareach⟩
    obtain ⟨D, hD⟩ := exists_unrootedLastDeletedHead p hstart hfinish
    exact ⟨p, hpAllowed, hpFinish, D, hD⟩

end Assertion822ReachableEssentialReservedRootObstruction

/-- A failure of repaired-relation reachability from the whole source at a
point which nevertheless has a concrete ambient source prefix. -/
structure Assertion822ReachableWholeSourceRootObstruction
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    (R : L.UnusedGroundedRecord hL S) where
  obstruction : L.Assertion822PreStoppedRootObstruction hL S R
  ambient : obstruction.boundary ∈ ambientSourceReachable Gamma
  not_rooted : ¬ ∃ a ∈ Gamma.source,
    Relation.ReflTransGen
      (fun x y ↦
        (x, y) ∈ L.assertion822ReservedPreStoppedEdges hL S R)
      a obstruction.boundary

namespace Assertion822ReachableWholeSourceRootObstruction

/-- Unpack the source-reachability retained by the obstruction. -/
theorem exists_ambientPath_to_boundary
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    (O : L.Assertion822ReachableWholeSourceRootObstruction hL S R) :
    ∃ p : DirectedPath.FinitePath Gamma.graph,
      p.start ∈ Gamma.source ∧ p.finish = O.obstruction.boundary :=
  O.ambient

/-- In the escape-free finite hanging leaf, the retained ambient path ends
at the displayed fragment terminal.  This is the exact prefix required by
the subsequent hanging-component exchange. -/
theorem exists_ambientPath_to_hangingTerminal
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    (O : L.Assertion822ReachableWholeSourceRootObstruction hL S R)
    {P : (L.popularAuxiliaryInput hL.legal).Fragment}
    (boundary_eq : GroundingCut.blockingPoint
      (L.popularAuxiliaryInput hL.legal) S.cut P = O.obstruction.boundary)
    {terminal : V} (terminal_eq : P.path.terminal? = some terminal)
    (not_meets_escape : ¬ PopularAuxiliary.Input.Fragment.MeetsEscape
      (L.popularAuxiliaryInput hL.legal) S.cut P) :
    ∃ p : DirectedPath.FinitePath Gamma.graph,
      p.start ∈ Gamma.source ∧ p.finish = terminal := by
  obtain ⟨p, hpSource, hpFinish⟩ := O.exists_ambientPath_to_boundary
  refine ⟨p, hpSource, hpFinish.trans ?_⟩
  exact boundary_eq.symm.trans
    (GroundingCut.blockingPoint_eq_terminal_of_not_meetsEscape
      (L.popularAuxiliaryInput hL.legal) S.cut P
      not_meets_escape terminal_eq)

end Assertion822ReachableWholeSourceRootObstruction

/-- An ordered collision in the source-reachable boundary.  The older
collision object retains all construction-specific normalization data; the
two additional fields retain the ambient source prefixes which justified
keeping the endpoints in the boundary. -/
structure Assertion822ReachableBoundaryObstruction
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    (R : L.UnusedGroundedRecord hL S) where
  obstruction : L.Assertion822PreStoppedBoundaryObstruction hL S R
  earlier_reachable : obstruction.earlier ∈ ambientSourceReachable Gamma
  later_reachable : obstruction.later ∈ ambientSourceReachable Gamma
  earlier_rooted : ∃ a ∈ Gamma.source,
    Relation.ReflTransGen
      (fun x y ↦
        (x, y) ∈ L.assertion822ReservedPreStoppedEdges hL S R)
      a obstruction.earlier
  later_rooted : ∃ a ∈ Gamma.source,
    Relation.ReflTransGen
      (fun x y ↦
        (x, y) ∈ L.assertion822ReservedPreStoppedEdges hL S R)
      a obstruction.later

namespace Assertion822ReachableBoundaryObstruction

theorem exists_ambientPath_to_earlier
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    (O : L.Assertion822ReachableBoundaryObstruction hL S R) :
    ∃ p : DirectedPath.FinitePath Gamma.graph,
      p.start ∈ Gamma.source ∧ p.finish = O.obstruction.earlier :=
  O.earlier_reachable

theorem exists_ambientPath_to_later
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    (O : L.Assertion822ReachableBoundaryObstruction hL S R) :
    ∃ p : DirectedPath.FinitePath Gamma.graph,
      p.start ∈ Gamma.source ∧ p.finish = O.obstruction.later :=
  O.later_reachable

end Assertion822ReachableBoundaryObstruction

/-- Exact reduction on the source-reachable literal boundary.  Unreachable
hanging components disappear before any relation-rooting obligation is
formed.  If all remaining points are rooted, a nonessential point already
gives Assertion 8.22; otherwise the residual reserved obstruction is
essential in the restricted boundary. -/
theorem assertion822Output_or_preStoppedReachableObstruction
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    (R : L.UnusedGroundedRecord hL S) :
    Nonempty (GroundingFinalAssembly.Assertion822Output
        (L.popularAuxiliaryInput hL.legal) S.cut) ∨
      Nonempty (L.Assertion822ReachableEssentialReservedRootObstruction
        hL S R) ∨
      Nonempty (L.Assertion822ReachableWholeSourceRootObstruction hL S R) ∨
      Nonempty (L.Assertion822ReachableBoundaryObstruction hL S R) := by
  classical
  let B := L.reachableBB hL S
  let E := L.assertion822ReservedPreStoppedEdges hL S R
  by_cases hroot : ∀ b ∈ B, ∃ a ∈ Gamma.source,
      Relation.ReflTransGen (fun x y ↦ (x, y) ∈ E) a b
  · by_cases hanti : IsReachabilityAntichain E B
    · by_cases hessential : B ⊆ Gamma.essential B
      · by_cases hreserved : ∀ b ∈ B,
          ∃ a ∈ Gamma.source \ {R.record.initial},
            Relation.ReflTransGen (fun x y ↦ (x, y) ∈ E) a b
        · exact Or.inl (by
            apply GroundingAssertion822Output.exists_of_rootedReachability
              (L.popularAuxiliaryInput hL.legal) S.cut E
              (Gamma.source \ {R.record.initial}) B
            · exact L.assertion822ReservedSwitchedEdgesAt_subset_adj
                hL S R ∅
            · exact L.assertion822ReservedSwitchedEdgesAt_biUnique
                hL S R ∅
            · exact Set.sdiff_subset
            · exact L.reachableBB_subset_BB hL S
            · exact L.reachableBB_isSeparator hL S
            · exact hanti
            · exact hreserved
            · exact R.record_initial_mem_source
            · simp)
        · right
          left
          push Not at hreserved
          obtain ⟨b, hb, hbnot⟩ := hreserved
          exact ⟨{
            obstruction := {
              boundary := b
              boundary_mem := (show b ∈ B from hb).1
              not_rooted := by
                rintro ⟨a, ha, hab⟩
                exact hbnot a ha hab }
            boundary_reachable := (show b ∈ B from hb).2
            boundary_essential := hessential hb }⟩
      · obtain ⟨b, hb, hbnot⟩ := Set.not_subset.mp hessential
        exact Or.inl
          (L.assertion822Output_of_preStoppedInessentialFrontierGeometry
            hL S R B (L.reachableBB_subset_BB hL S)
              (L.reachableBB_isSeparator hL S) hanti hroot b hb hbnot)
    · right
      right
      right
      by_contra hnone
      apply hanti
      intro b hb c hc hbc
      by_contra hne
      exact hnone ⟨{
        obstruction := {
          earlier := b
          later := c
          earlier_mem := (show b ∈ B from hb).1
          later_mem := (show c ∈ B from hc).1
          distinct := hne
          reaches := hbc }
        earlier_reachable := (show b ∈ B from hb).2
        later_reachable := (show c ∈ B from hc).2
        earlier_rooted := hroot b hb
        later_rooted := hroot c hc }⟩
  · right
    right
    left
    push Not at hroot
    obtain ⟨b, hb, hbnot⟩ := hroot
    exact ⟨{
      obstruction := {
        boundary := b
        boundary_mem := (show b ∈ B from hb).1
        not_rooted := by
          rintro ⟨a, ha, hab⟩
          exact hbnot a ha.1 hab }
      ambient := (show b ∈ B from hb).2
      not_rooted := by
        rintro ⟨a, ha, hab⟩
        exact hbnot a ha hab }⟩

/-- Public compiler on the source-reachable literal boundary.  Both residual
root failures are classified only after unreachable bookkeeping points have
been removed.  In particular, the whole-source callback retains the ambient
source prefix while receiving the same well-founded self-backward-normalized
outcome as the reserved-source callback. -/
theorem assertion822Output_or_hindrance_of_preStoppedReachableRepairs
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    (repairEssential : ∀ (R : L.UnusedGroundedRecord hL S)
        (O : L.Assertion822ReachableEssentialReservedRootObstruction hL S R),
      O.obstruction.BackwardSelfNormalizedFirstFragmentRootFailureOutcome →
        ∃ W : Set Gamma.DPath, Gamma.IsHindrance W)
    (repairWholeSource : ∀ (R : L.UnusedGroundedRecord hL S)
        (O : L.Assertion822ReachableWholeSourceRootObstruction hL S R),
      O.obstruction.BackwardSelfNormalizedFirstFragmentRootFailureOutcome →
        ∃ W : Set Gamma.DPath, Gamma.IsHindrance W)
    (repairBoundary : ∀ (R : L.UnusedGroundedRecord hL S)
        (O : L.Assertion822ReachableBoundaryObstruction hL S R),
      O.obstruction.FiniteSinkReducedTerminalFailureOutcome →
        ∃ W : Set Gamma.DPath, Gamma.IsHindrance W) :
    Nonempty (GroundingFinalAssembly.Assertion822Output
        (L.popularAuxiliaryInput hL.legal) S.cut) ∨
      ∃ W : Set Gamma.DPath, Gamma.IsHindrance W := by
  let R := (L.exists_unusedGroundedRecord hL S).some
  rcases L.assertion822Output_or_preStoppedReachableObstruction hL S R with
    houtput | hessential | hwhole | hboundary
  · exact Or.inl houtput
  · exact Or.inr (repairEssential R hessential.some
      hessential.some.obstruction.backwardSelfNormalizedFirstFragmentRootFailureOutcome)
  · exact Or.inr (repairWholeSource R hwhole.some
      hwhole.some.obstruction.backwardSelfNormalizedFirstFragmentRootFailureOutcome)
  · exact Or.inr (repairBoundary R hboundary.some
      hboundary.some.obstruction.finiteSinkReducedTerminalFailureOutcome)

end DWeb.KappaLadder
end Erdos599

#print axioms Erdos599.DWeb.KappaLadder.reachableBB_isSeparator
#print axioms
  Erdos599.DWeb.KappaLadder.assertion822Output_or_preStoppedReachableObstruction
#print axioms
  Erdos599.DWeb.KappaLadder.assertion822Output_or_hindrance_of_preStoppedReachableRepairs
