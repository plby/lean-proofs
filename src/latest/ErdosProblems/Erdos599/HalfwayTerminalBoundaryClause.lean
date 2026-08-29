/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayLocalizedReferenceRemainder
import ErdosProblems.Erdos599.HalfwaySourceRootFinalBoundary
import ErdosProblems.Erdos599.HalfwaySourceRootTargetLink
import ErdosProblems.Erdos599.HalfwaySubdivisionFinalNoRay

/-!
# The terminal-boundary half-way conclusion

The printed final construction proves that the completed warp starts at all
sources, has finite character, ends on the chosen stopover, and links the
designated sources to the original target.  It does not prove that a path
cannot meet an earlier persistent stopover vertex internally.  This module
records exactly the conclusion supported by the construction.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace CardinalInduction

universe u

variable {V : Type u}

/-- A finite warp with the required initial and terminal boundaries, without
the generally false assertion that it meets the outer terminal boundary only
at its final vertex. -/
structure IsTerminalBoundaryLinkage (Gamma : DWeb V) (A C : Set V)
    (W : Set Gamma.DPath) : Prop where
  isWarp : Gamma.IsWarp W
  finiteCharacter : Gamma.HasFiniteCharacter W
  initialSet_eq : Gamma.initialSet W = A
  terminalFrontier_subset : Gamma.terminalFrontier W ⊆ C

/-- The stopover geometry paired with the honest terminal-boundary linkage. -/
structure IsSeparatingTerminalBoundaryStopover
    (Gamma : DWeb V) (W : Set Gamma.DPath) (C : Set V) : Prop where
  linkage : IsTerminalBoundaryLinkage Gamma Gamma.source C W
  separator : IsSeparatorFrom Gamma Gamma.source C
  trimmed : IsTrimmedSeparator Gamma C
  quotient_unhindered : (Gamma.quotient C).IsUnhindered

/-- Corrected half-way conclusion supported by the final scheduler. -/
def TerminalBoundaryHalfwayClauseAt
    (Gamma : DWeb V) (kappa : Cardinal.{u}) : Prop :=
  ∀ A0 : Set V, A0 ⊆ Gamma.source → #A0 = kappa →
    ∃ (W : Set Gamma.DPath) (C : Set V),
      IsSeparatingTerminalBoundaryStopover Gamma W C ∧
      LinksToTarget Gamma W A0 ∧ HeightAtMost Gamma C kappa

end CardinalInduction

namespace Blueprint
namespace LinkageBlueprint

open Alternating

namespace IndexedTerminalResolutionState
namespace ReachableResolutionRecursor
namespace ResolutionChain

universe u v w

variable {V : Type u} {Gamma : DWeb V}
variable {kappa theta : Cardinal.{u}}
variable {L : Gamma.KappaLadder theta}
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

/-- The fair source-rooted limit produces the completed terminal-boundary
warp at the actual final ladder frontier.  Unlike the stronger
`IsLinkageBetween` conversion, this theorem needs no stopover-sink premise. -/
theorem exists_localizedTerminalBoundaryHalfway
    (R : FairResolutionLimit C seed)
    (a : Ladder.Stage theta)
    (hslice : slice R.limit.stageIndex = L.frontier a)
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    (hGamma : Gamma.IsNormalized)
    (hinc : HasHereditarySubdivisionIncidence Gamma.graph)
    (hkappa : aleph0 ≤ kappa)
    {A0 : Set V}
    (hA0source : A0 ⊆ Gamma.source)
    (hA0initial : A0 ⊆ R.limit.blueprint.initialSet)
    (hseparator : CardinalInduction.IsSeparatorFrom
      Gamma Gamma.source (L.frontier a))
    (htrimmed : Gamma.essential (L.frontier a) = L.frontier a)
    (hunhindered : (Gamma.quotient (L.frontier a)).IsUnhindered)
    (heightDelete : Set V)
    (heightWave : Set (Gamma.quotient heightDelete).DPath)
    (hheightDelete : heightDelete ⊆ Gamma.sourceᶜ)
    (hheightWave : (Gamma.quotient heightDelete).IsWave heightWave)
    (hroofed : L.frontier a ⊆ Gamma.roof
      ((Gamma.quotient heightDelete).terminalFrontier heightWave))
    (hheightCard : #heightDelete ≤ kappa) :
    ∃ W : Set Gamma.DPath,
      CardinalInduction.IsSeparatingTerminalBoundaryStopover
        Gamma W (L.frontier a) ∧
      CardinalInduction.LinksToTarget Gamma W A0 ∧
      CardinalInduction.HeightAtMost Gamma (L.frontier a) kappa := by
  let U := sourceRootBlueprint R.limit.blueprint
  let localR := localizedReferenceRemainder L a U
  let W := U.completedFamily R.sourceRoot_isEdgeReal localR
  have hUblueprint : R.limit.blueprint.IsLinkageBlueprint
      (L.frontier a) (closure R.limit.stageIndex) persistent := by
    simpa only [hslice] using R.limit.isBlueprint
  have hterminal : U.terminalSet ⊆ L.frontier a := by
    simpa only [U, hslice] using R.sourceRoot_terminalSet_subset_finalSlice
  have hnoRay : ¬ ContainsDirectedRay R.limit.blueprint.edgeSet :=
    R.no_directedRay_of_subdivision hGamma hinc hkappa
  have hUfinite : ∀ p ∈ U.paths,
      ∃ q : DirectedPath.FinitePath
        (imaginaryGraph Gamma L.limitWarp kappa), p = .inl q :=
    allFinite_of_no_directedRay U
      (sourceRootBlueprint_no_directedRay R.limit.blueprint hnoRay)
  have hlinks : U.BlueprintLinksToTarget A0 := by
    apply sourceRootBlueprint_blueprintLinksToTarget_of_noRay
      R.limit.blueprint hGamma R.real_limit hnoRay hA0source
    · exact R.designated_initial_sourceRoot hA0source hA0initial
    · exact R.sourceRoot_realTerminals_target
  refine ⟨W, ?_, ?_, ?_⟩
  · refine {
      linkage := {
        isWarp := U.isWarp_completedFamily R.sourceRoot_isEdgeReal
          (localizedReferenceRemainder_isWarp L a U hL)
          (localizedReferenceRemainder_disjoint L a U)
        finiteCharacter := U.finiteCharacter_completedFamily
          R.sourceRoot_isEdgeReal hUfinite
          (localizedReferenceRemainder_finiteCharacter L a U)
        initialSet_eq := by
          change Gamma.initialSet
            (U.completedFamily R.sourceRoot_isEdgeReal localR) = Gamma.source
          rw [U.initialSet_completedFamily]
          exact sourceRootBlueprint_initial_union_localizedReferenceRemainder
            L a R.limit.blueprint hL hUblueprint
        terminalFrontier_subset := by
          change Gamma.terminalFrontier
            (U.completedFamily R.sourceRoot_isEdgeReal localR) ⊆ L.frontier a
          rw [U.terminalFrontier_completedFamily]
          exact Set.union_subset hterminal
            (localizedReferenceRemainder_terminalFrontier_subset L a U hL) }
      separator := hseparator
      trimmed := htrimmed
      quotient_unhindered := hunhindered }
  · exact U.linksToTarget_completedFamily R.sourceRoot_isEdgeReal localR hlinks
  · exact ⟨heightDelete,
      ⟨hheightDelete, heightWave, hheightWave, hroofed⟩, hheightCard⟩

end FairResolutionLimit
end ResolutionChain
end ReachableResolutionRecursor
end IndexedTerminalResolutionState
end LinkageBlueprint
end Blueprint
end Erdos599
