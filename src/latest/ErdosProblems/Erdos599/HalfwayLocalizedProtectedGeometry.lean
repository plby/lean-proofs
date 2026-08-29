/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.DeferredLadderRoofTransport
import ErdosProblems.Erdos599.HalfwayLocalizedProtectedOutput
import ErdosProblems.Erdos599.SingularLinkageGeometry

/-!
# Exact geometry of the protected final families

The localized selected-reference remainder is terminal-clean at the actual
ladder frontier and lies below its roof.  The realized source-root family
links all of its own initials to the original target.  These are the
properties needed by protected continuation arguments; the realized family
is deliberately not asserted to be terminal-clean at the ladder frontier.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace Blueprint
namespace LinkageBlueprint

universe u

variable {V : Type u} {Gamma : DWeb V}
variable {kappa rho : Cardinal.{u}}

/-- Protected output together with the exact additional geometry needed by
regular and singular continuation. -/
structure CardinalInduction.LocalizedProtectedHalfwayGeometry
    (Gamma : DWeb V) (A0 : Set V) (kappa : Cardinal.{u})
    extends CardinalInduction.LocalizedProtectedHalfwayOutput Gamma A0 kappa where
  remainder_terminalClean :
    CardinalInduction.SingularContinuation.TerminalCleanAt
      Gamma remainder stopover
  remainder_carrier_roof :
    Gamma.vertexSet remainder ⊆ Gamma.roof stopover
  original_quotient_unhindered : (Gamma.quotient stopover).IsUnhindered
  targetPaths_link_initial : CardinalInduction.LinksToTarget Gamma targetPaths
    (Gamma.initialSet targetPaths)

/-- The finite selected-reference remainder meets the selected frontier only
at the terminal vertex of each member. -/
theorem localizedReferenceRemainder_terminalClean
    (L : Gamma.KappaLadder kappa) (a : Ladder.Stage kappa)
    (U : LinkageBlueprint Gamma L.limitWarp rho)
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L) :
    CardinalInduction.SingularContinuation.TerminalCleanAt Gamma
      (localizedReferenceRemainder L a U) (L.frontier a) := by
  intro p hp x hxp hxFrontier
  obtain ⟨q, rfl⟩ := localizedReferenceRemainder_finiteCharacter L a U hp
  have hxTerminalFrontier :
      x ∈ Gamma.terminalFrontier (ladderReference L a) := by
    rw [ladderReference.terminalFrontier_eq hL]
    exact hxFrontier
  have hxFinish : x = q.finish := Set.mem_singleton_iff.1
    (DWeb.IsWarp.finite_support_inter_terminalFrontier Gamma
      (ladderReference.isWarp hL) hp.1 ⟨hxp, hxTerminalFrontier⟩)
  subst x
  exact Gamma.terminal?_finite q

/-- The localized remainder inherits the self-roofing property of the
selected ladder reference. -/
theorem localizedReferenceRemainder_vertexSet_subset_roof
    (L : Gamma.KappaLadder kappa) (a : Ladder.Stage kappa)
    (U : LinkageBlueprint Gamma L.limitWarp rho)
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L) :
    Gamma.vertexSet (localizedReferenceRemainder L a U) ⊆
      Gamma.roof (L.frontier a) := by
  apply Set.Subset.trans (b := Gamma.vertexSet (ladderReference L a))
  · rintro x ⟨p, hp, hxp⟩
    exact ⟨p, localizedReferenceRemainder_subset L a U hp, hxp⟩
  · exact ladderReference.vertexSet_subset_roof hL
      (DWeb.KappaLadder.Deferred.vertexSet_warpAt_subset_roof_terminalFrontier
        hL a)

namespace IndexedTerminalResolutionState
namespace ReachableResolutionRecursor
namespace ResolutionChain

universe v w

variable {L : Gamma.KappaLadder (succ kappa)}
variable {persistent : Set V}
variable {Stage : Type w} [LinearOrder Stage]
variable {slice closure : Stage → Set V}
variable {I : Type v} [LinearOrder I] [Nonempty I]
variable {C : ResolutionChain
  (Gamma := Gamma) (Y := L.limitWarp) (kappa := kappa)
  (persistent := persistent) (B := Gamma.target)
  (slice := slice) (closure := closure) I}
variable {seed : IndexedTerminalResolutionState
  (Gamma := Gamma) (Y := L.limitWarp) (kappa := kappa)
  (persistent := persistent) (B := Gamma.target) slice closure}

namespace FairResolutionLimit

/-- Every realized source-root component, not merely the designated
subfamily, links its own initial vertex to the original target. -/
theorem sourceRoot_realFamily_linksToTarget_initialSet
    (R : FairResolutionLimit C seed)
    (hGamma : Gamma.IsNormalized)
    (hinc : HasHereditarySubdivisionIncidence Gamma.graph)
    (hkappa : aleph0 ≤ kappa) :
    CardinalInduction.LinksToTarget Gamma
      ((sourceRootBlueprint R.limit.blueprint).realFamily
        R.sourceRoot_isEdgeReal)
      (Gamma.initialSet
        ((sourceRootBlueprint R.limit.blueprint).realFamily
          R.sourceRoot_isEdgeReal)) := by
  let U := sourceRootBlueprint R.limit.blueprint
  let hreal : U.IsEdgeReal := R.sourceRoot_isEdgeReal
  let P := U.realFamily hreal
  have hnoRay : ¬ Alternating.ContainsDirectedRay
      R.limit.blueprint.edgeSet :=
    R.no_directedRay_of_subdivision hGamma hinc hkappa
  have hfinite : Gamma.HasFiniteCharacter P := by
    apply U.finiteCharacter_realFamily hreal
    exact allFinite_of_no_directedRay U
      (sourceRootBlueprint_no_directedRay R.limit.blueprint hnoRay)
  apply CardinalInduction.SingularContinuation.linksToTarget_of_initial_terminal
    Gamma hGamma hfinite
  · change Gamma.initialSet (U.realFamily hreal) ⊆ Gamma.source
    rw [U.initialSet_realFamily]
    exact sourceRootBlueprint_initialSet_subset_source R.limit.blueprint
  · intro x hx
    obtain ⟨p, hp, hpx⟩ := hx
    obtain ⟨q, rfl⟩ := hfinite hp
    refine ⟨.inl q, hp, hpx, q.finish, ?_, ?_⟩
    · exact R.sourceRoot_realTerminals_target
        (by
          rw [U.realPart_terminals_eq_terminalSet_of_isEdgeReal hreal]
          rw [← U.terminalFrontier_realFamily hreal]
          exact ⟨.inl q, hp, rfl⟩)
    · exact Gamma.terminal?_finite q

/-- The actual protected payload, including the terminal-clean local
remainder, both quotient facts, and target-linking for every realized
source-root component. -/
noncomputable def localizedProtectedGeometry_of_ladder
    (R : FairResolutionLimit C seed)
    (a : Ladder.Stage (succ kappa))
    (hslice : slice R.limit.stageIndex = L.frontier a)
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    (hGamma : Gamma.IsNormalized)
    (hinc : HasHereditarySubdivisionIncidence Gamma.graph)
    (hkappa : aleph0 ≤ kappa)
    (hstage : (L.stageWeb a).IsUnhindered)
    {A0 : Set V}
    (hA0source : A0 ⊆ Gamma.source)
    (hA0initial : A0 ⊆ R.limit.blueprint.initialSet) :
    CardinalInduction.LocalizedProtectedHalfwayGeometry Gamma A0 kappa := by
  let O := R.localizedProtectedOutput_of_ladder a hslice hL hGamma hinc
    hkappa hstage hA0source hA0initial
  let hex := R.exists_localizedTerminalBoundaryHalfway_of_ladder a hslice hL
    hGamma hinc hkappa hstage hA0source hA0initial
  let W := Classical.choose hex
  have hstop := (Classical.choose_spec hex).1
  refine {
    toLocalizedProtectedHalfwayOutput := O
    remainder_terminalClean := ?_
    remainder_carrier_roof := ?_
    original_quotient_unhindered := hstop.quotient_unhindered
    targetPaths_link_initial := ?_ }
  · change CardinalInduction.SingularContinuation.TerminalCleanAt Gamma
      (localizedReferenceRemainder L a
        (sourceRootBlueprint R.limit.blueprint)) (L.frontier a)
    exact localizedReferenceRemainder_terminalClean L a
      (sourceRootBlueprint R.limit.blueprint) hL
  · change Gamma.vertexSet
      (localizedReferenceRemainder L a
        (sourceRootBlueprint R.limit.blueprint)) ⊆
      Gamma.roof (L.frontier a)
    exact localizedReferenceRemainder_vertexSet_subset_roof L a
      (sourceRootBlueprint R.limit.blueprint) hL
  · change CardinalInduction.LinksToTarget Gamma
      ((sourceRootBlueprint R.limit.blueprint).realFamily
        R.sourceRoot_isEdgeReal)
      (Gamma.initialSet
        ((sourceRootBlueprint R.limit.blueprint).realFamily
          R.sourceRoot_isEdgeReal))
    exact R.sourceRoot_realFamily_linksToTarget_initialSet hGamma hinc hkappa

end FairResolutionLimit
end ResolutionChain
end ReachableResolutionRecursor
end IndexedTerminalResolutionState
end LinkageBlueprint
end Blueprint
end Erdos599
