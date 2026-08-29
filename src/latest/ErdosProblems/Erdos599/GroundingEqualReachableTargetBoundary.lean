/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingEqualTargetOnlyPreStoppedCompiler
import ErdosProblems.Erdos599.GroundingPathPrefix

/-!
# The source-reachable target-only grounding boundary

The full essential terminal cut can contain terminals which no original
source reaches.  Such points are irrelevant to separation and, for a hanging
limiting-ladder component untouched by the decoded routes, cannot be rooted
in the canonical repaired relation.  The sound target-only boundary therefore
keeps precisely the terminal-cut points admitting an ambient finite path from
the original source.

This file proves that this smaller set is still a separator and packages the
corresponding equal-branch compiler.  No collision carrier is added to the
boundary; collision hulls remain routing metadata for proving the remaining
active absorption statement.
-/

noncomputable section

open Cardinal Set

namespace Erdos599

open DirectedPath Alternating

universe u

variable {V : Type u} {Gamma : DWeb V}

namespace DWeb.KappaLadder

open GroundingEqualActiveSelection
open GroundingRootedReachabilityWarp

variable {kappa : Cardinal.{u}}

private abbrev MaximalWarp
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {q : FinitePath (EqualInput L hL).lambda.graph}
    (M : Popular.MaximalDecodedTargetPureAvoidingRestrictedXSWarp
      (EqualInput L hL)
      ((EqualInput L hL).lambda.source \ {q.start})
      (collisionCarrier (EqualInput L hL) q)) :=
  ReservedMaximalDecodedActiveSupply.toXSWarp M

/-- Vertices admitting an ambient finite directed path from an original
source. -/
def ambientSourceReachable (Gamma : DWeb V) : Set V :=
  {x | ∃ p : FinitePath Gamma.graph,
    p.start ∈ Gamma.source ∧ p.finish = x}

/-- The target-only boundary after discarding terminals irrelevant to every
source--target path. -/
def reachableTerminalCut
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance) : Set V :=
  (EqualInput L hL).terminalCut ∩ ambientSourceReachable Gamma

/-- Every source--target path meets a terminal-cut vertex which its own
initial segment witnesses to be source-reachable. -/
theorem reachableTerminalCut_isSeparator
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance) :
    Popular.IsSeparator Gamma (reachableTerminalCut L hL) := by
  intro p hpSource hpTarget
  obtain ⟨x, hxp, hxCut⟩ :=
    L.popularAuxiliaryInput_terminalCut_isSeparator hL.legal
      p hpSource hpTarget
  obtain ⟨r, hrStart, hrFinish, _hrSupport, _hrEdges⟩ :=
    GroundingPathPrefix.exists_initialFinitePrefix
      (Sum.inl p : Gamma.DPath) (by
        change x ∈ p.support
        exact hxp)
  refine ⟨x, hxp, hxCut, r, ?_, hrFinish⟩
  simpa only [hrStart, Path.initial] using hpSource

/-- Restricting the terminal cut preserves the reachability-antichain
property of the canonical repaired relation. -/
theorem reachableTerminalCut_isReachabilityAntichain
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (W : Popular.XSWarp
      (EqualInput L hL).lambda (EqualInput L hL).lambda.target) :
    IsReachabilityAntichain
      (canonicalErasedRepairedEdges (EqualInput L hL) W)
      (reachableTerminalCut L hL) := by
  intro b hb c hc hbc
  exact terminalCut_isReachabilityAntichain_canonicalErasedRepairedEdges
    L hL W hb.1 hc.1 hbc

/-- Compile source-rooting of only the relevant target-only boundary.  The
reserved source is removed internally, exactly as for the full terminal cut:
it cannot reach any terminal-cut point in the repaired relation. -/
theorem ReservedGroundedParent.exists_hindrance_of_reachableTerminalCut_sourceRooted
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {q : FinitePath (EqualInput L hL).lambda.graph}
    {hqsource : q.start ∈ (EqualInput L hL).lambda.source}
    (R : L.ReservedGroundedParent hL q hqsource)
    (W : Popular.XSWarp
      (EqualInput L hL).lambda (EqualInput L hL).lambda.target)
    (hWdisjoint : W.paths.PairwiseDisjoint
      (EqualInput L hL).decodedVertexCarrier)
    (havoid : ∀ p ∈ W.paths,
      Disjoint p.support (collisionCarrier (EqualInput L hL) q))
    (hroot : ∀ b ∈ reachableTerminalCut L hL,
      ∃ a ∈ Gamma.source,
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈
            canonicalErasedRepairedEdges (EqualInput L hL) W) a b) :
    ∃ H : Set Gamma.DPath, Gamma.IsHindrance H := by
  let A : Set V := Gamma.source \ {R.parent.initial}
  apply
    GroundingRootedReachabilityHindrance.exists_hindrance_of_rootedSeparatingAntichain
      (canonicalErasedRepairedEdges (EqualInput L hL) W)
      A (reachableTerminalCut L hL) (unused := R.parent.initial)
  · exact canonicalErasedRepairedEdges_subset_adj (EqualInput L hL) W
  · exact canonicalErasedRepairedEdges_biUnique
      (EqualInput L hL) W hWdisjoint
  · exact Set.sdiff_subset
  · exact reachableTerminalCut_isReachabilityAntichain L hL W
  · intro b hb
    obtain ⟨a, haSource, hab⟩ := hroot b hb
    have hane : a ≠ R.parent.initial := by
      intro hae
      subst a
      exact R.not_reaches_terminalCut W havoid hb.1 hab
    exact ⟨a, ⟨haSource, by simpa using hane⟩, hab⟩
  · exact reachableTerminalCut_isSeparator L hL
  · exact R.parent_initial_source
  · simp [A]

/-- Coverage alternatives for a point of the sound target-only boundary.
In the only genuinely new case, the untouched hanging terminal comes with
the ambient source path which makes it relevant to separation. -/
theorem reachableTerminalCut_sourceRooted_or_routeContact_or_untouchedHanging
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    (W : Popular.XSWarp
      (EqualInput L hL).lambda (EqualInput L hL).lambda.target)
    {b : V} (hb : b ∈ reachableTerminalCut L hL) :
    (∃ a ∈ Gamma.source,
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈
          canonicalErasedRepairedEdges (EqualInput L hL) W) a b) ∨
    (∃ Y : Gamma.DPath,
      Y ∈ Gamma.essentialWarpPart L.limitWarp ∧
      Y.terminal? = some b ∧
      ∃ r : WarpPath W,
        ((canonicalErasedRoute (EqualInput L hL) W r).vertexSet ∩
          Y.support).Nonempty) ∨
    ∃ Y : Gamma.DPath,
      Y ∈ Gamma.essentialWarpPart L.limitWarp ∧
      Y.terminal? = some b ∧
      PopularAuxiliary.IsHangingPath Gamma Y ∧
      (∀ r : WarpPath W,
        Disjoint
          (canonicalErasedRoute (EqualInput L hL) W r).vertexSet
          Y.support) ∧
      ∃ p : FinitePath Gamma.graph,
        p.start ∈ Gamma.source ∧ p.finish = b := by
  rcases terminalCut_sourceRooted_or_routeContact_or_untouchedHanging
      W hb.1 with hroot | hcontact | hhanging
  · exact Or.inl hroot
  · exact Or.inr (Or.inl hcontact)
  · obtain ⟨Y, hY, hYterminal, hhang, hdisjoint⟩ := hhanging
    exact Or.inr <| Or.inr
      ⟨Y, hY, hYterminal, hhang, hdisjoint, hb.2⟩

/-- Strongest current unconditional target-only compiler for the maximal
decoded route supply.  All structural relation facts and the reduction from
the full terminal cut to its source-reachable part are internal.  The two
callbacks are local active transactions: absorb an actual route contact, or
absorb an untouched hanging component together with a concrete ambient path
from the source to its terminal. -/
theorem ReservedGroundedParent.exists_hindrance_of_reachableTargetOnlyCases
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {q : FinitePath (EqualInput L hL).lambda.graph}
    {hqsource : q.start ∈ (EqualInput L hL).lambda.source}
    (R : L.ReservedGroundedParent hL q hqsource)
    (M : Popular.MaximalDecodedTargetPureAvoidingRestrictedXSWarp
      (EqualInput L hL)
      ((EqualInput L hL).lambda.source \ {q.start})
      (collisionCarrier (EqualInput L hL) q))
    (absorbContact : ∀ (b : V), b ∈ reachableTerminalCut L hL →
      ∀ (Y : Gamma.DPath),
      Y ∈ Gamma.essentialWarpPart L.limitWarp →
      Y.terminal? = some b →
      (∃ r : WarpPath (MaximalWarp M),
        ((canonicalErasedRoute (EqualInput L hL) (MaximalWarp M) r).vertexSet
          ∩ Y.support).Nonempty) →
      ∃ a ∈ Gamma.source,
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ canonicalErasedRepairedEdges
            (EqualInput L hL) (MaximalWarp M)) a b)
    (absorbUntouchedHanging : ∀ (b : V),
      b ∈ reachableTerminalCut L hL →
      ∀ (Y : Gamma.DPath),
      Y ∈ Gamma.essentialWarpPart L.limitWarp →
      Y.terminal? = some b →
      PopularAuxiliary.IsHangingPath Gamma Y →
      (∀ r : WarpPath (MaximalWarp M),
        Disjoint
          (canonicalErasedRoute (EqualInput L hL) (MaximalWarp M) r).vertexSet
          Y.support) →
      (∃ p : FinitePath Gamma.graph,
        p.start ∈ Gamma.source ∧ p.finish = b) →
      ∃ a ∈ Gamma.source,
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ canonicalErasedRepairedEdges
            (EqualInput L hL) (MaximalWarp M)) a b) :
    ∃ H : Set Gamma.DPath, Gamma.IsHindrance H := by
  apply R.exists_hindrance_of_reachableTerminalCut_sourceRooted
    (MaximalWarp M)
    (ReservedMaximalDecodedActiveSupply.decodedCarriers_pairwiseDisjoint M)
    (fun p hp ↦ M.paths_avoid hp)
  intro b hb
  rcases
      reachableTerminalCut_sourceRooted_or_routeContact_or_untouchedHanging
        (MaximalWarp M) hb with hroot | hcontact | hhanging
  · exact hroot
  · obtain ⟨Y, hY, hYterminal, hcontact⟩ := hcontact
    exact absorbContact b hb Y hY hYterminal hcontact
  · obtain ⟨Y, hY, hYterminal, hhang, hdisjoint, hambient⟩ := hhanging
    exact absorbUntouchedHanging b hb Y hY hYterminal hhang hdisjoint hambient

end DWeb.KappaLadder
end Erdos599

#print axioms Erdos599.DWeb.KappaLadder.reachableTerminalCut_isSeparator
#print axioms Erdos599.DWeb.KappaLadder.reachableTerminalCut_isReachabilityAntichain
#print axioms Erdos599.DWeb.KappaLadder.ReservedGroundedParent.exists_hindrance_of_reachableTerminalCut_sourceRooted
#print axioms Erdos599.DWeb.KappaLadder.reachableTerminalCut_sourceRooted_or_routeContact_or_untouchedHanging
#print axioms Erdos599.DWeb.KappaLadder.ReservedGroundedParent.exists_hindrance_of_reachableTargetOnlyCases
