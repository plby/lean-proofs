/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayLocalizedReferenceRemainder
import ErdosProblems.Erdos599.HalfwaySourceRootFinalBoundary
import ErdosProblems.Erdos599.HalfwaySubdivisionFinalEndpoint
import ErdosProblems.Erdos599.HalfwayTerminalBoundarySubset

/-!
# Final certificate with an explicit finite remainder

The final reference family need not be the literal set-theoretic remainder
of the global limit warp.  It is the finite selected-stage prefix family.
This certificate therefore stores the remainder explicitly and is compiled
by the general terminal-boundary-inclusion theorem.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace CardinalInduction

open Blueprint LinkageBlueprint

universe u

variable {V : Type u}

/-- Globally resolved data with an explicit finite remainder family. -/
structure SeparatingResolvedBlueprintRemainderCertificate
    (Gamma : DWeb V) (A0 : Set V) (kappa : Cardinal.{u}) where
  reference : Set Gamma.DPath
  blueprint : Blueprint.LinkageBlueprint Gamma reference kappa
  remainder : Set Gamma.DPath
  stopover : Set V
  heightDelete : Set V
  heightWave : Set (Gamma.quotient heightDelete).DPath
  remainder_isWarp : Gamma.IsWarp remainder
  remainder_disjoint : ∀ p ∈ blueprint.paths, ∀ q ∈ remainder,
    Disjoint p.support q.support
  edge_real : blueprint.IsEdgeReal
  real_terminals_target : blueprint.realPart.terminals ⊆ Gamma.target
  designated_source : A0 ⊆ Gamma.source
  designated_initial : A0 ⊆ blueprint.initialSet
  source_cover : blueprint.initialSet ∪ Gamma.initialSet remainder =
    Gamma.source
  terminal_boundary : blueprint.terminalSet ∪
    Gamma.terminalFrontier remainder ⊆ stopover
  blueprint_endpointPure : ∀ p ∈ blueprint.paths,
    blueprint.IsPathBetween Gamma.source stopover p
  remainder_endpointPure : ∀ p ∈ remainder,
    IsPathBetween Gamma Gamma.source stopover p
  stopover_separator : IsSeparatorFrom Gamma Gamma.source stopover
  stopover_trimmed : Gamma.essential stopover = stopover
  quotient_unhindered : (Gamma.quotient stopover).IsUnhindered
  heightDelete_nonSource : heightDelete ⊆ Gamma.sourceᶜ
  heightWave_isWave : (Gamma.quotient heightDelete).IsWave heightWave
  stopover_roofed : stopover ⊆ Gamma.roof
    ((Gamma.quotient heightDelete).terminalFrontier heightWave)
  heightDelete_card : #heightDelete ≤ kappa

namespace SeparatingResolvedBlueprintRemainderCertificate

theorem exists_separatingHalfwayLinkage
    {Gamma : DWeb V} {A0 : Set V} {kappa : Cardinal.{u}}
    (C : SeparatingResolvedBlueprintRemainderCertificate Gamma A0 kappa) :
    ∃ W : Set Gamma.DPath,
      IsSeparatingHalfwayStopover Gamma W C.stopover ∧
      LinksToTarget Gamma W A0 ∧
      HeightAtMost Gamma C.stopover kappa := by
  have hterminalTarget : C.blueprint.terminalSet ⊆ Gamma.target := by
    rw [← C.blueprint.realPart_terminals_eq_terminalSet_of_isEdgeReal
      C.edge_real]
    exact C.real_terminals_target
  have hlinks : C.blueprint.BlueprintLinksToTarget A0 :=
    C.blueprint.blueprintLinksToTarget_of_initial_terminal
      C.designated_source C.designated_initial C.blueprint_endpointPure
      hterminalTarget
  exact exists_separatingHalfwayStopover_of_terminalBlueprint_withReference_subset
    C.blueprint C.edge_real C.remainder C.remainder_isWarp
    C.remainder_disjoint C.source_cover C.terminal_boundary
    C.blueprint_endpointPure C.remainder_endpointPure C.stopover_trimmed
    C.quotient_unhindered C.stopover_separator hlinks
    C.heightDelete_nonSource C.heightWave C.heightWave_isWave
    C.stopover_roofed C.heightDelete_card

end SeparatingResolvedBlueprintRemainderCertificate
end CardinalInduction

namespace Blueprint
namespace LinkageBlueprint
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

/-- Assemble every final field from the fair source-rooted limit and the
finite localized reference.  The only remaining path-geometric premise is
that non-source carrier points on the chosen frontier are sinks.  Standard
ladder geometry supplies the separator, trimmedness, quotient, and height
arguments passed explicitly below. -/
noncomputable def localizedSeparatingCertificate
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
    (hstopSink : ∀ x,
      x ∈ (sourceRootBlueprint R.limit.blueprint).vertexSet →
        x ∈ L.frontier a → x ∉ Gamma.source →
          ¬ ∃ y, (x, y) ∈
            (sourceRootBlueprint R.limit.blueprint).edgeSet)
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
    CardinalInduction.SeparatingResolvedBlueprintRemainderCertificate
      Gamma A0 kappa := by
  let U := sourceRootBlueprint R.limit.blueprint
  let localR := localizedReferenceRemainder L a U
  have hUblueprint : R.limit.blueprint.IsLinkageBlueprint
      (L.frontier a) (closure R.limit.stageIndex) persistent := by
    simpa only [hslice] using R.limit.isBlueprint
  have hterminal : U.terminalSet ⊆ L.frontier a := by
    simpa only [U, hslice] using R.sourceRoot_terminalSet_subset_finalSlice
  exact {
    reference := L.limitWarp
    blueprint := U
    remainder := localR
    stopover := L.frontier a
    heightDelete := heightDelete
    heightWave := heightWave
    remainder_isWarp := localizedReferenceRemainder_isWarp L a U hL
    remainder_disjoint := localizedReferenceRemainder_disjoint L a U
    edge_real := R.sourceRoot_isEdgeReal
    real_terminals_target := R.sourceRoot_realTerminals_target
    designated_source := hA0source
    designated_initial := R.designated_initial_sourceRoot
      hA0source hA0initial
    source_cover :=
      sourceRootBlueprint_initial_union_localizedReferenceRemainder
        L a R.limit.blueprint hL hUblueprint
    terminal_boundary := Set.union_subset hterminal
      (localizedReferenceRemainder_terminalFrontier_subset L a U hL)
    blueprint_endpointPure := by
      simpa only [U] using
        R.sourceRoot_endpointPure_of_subdivision_nonSource hGamma hinc hkappa
          hterminal hstopSink
    remainder_endpointPure :=
      localizedReferenceRemainder_endpointPure L a U hGamma hL
    stopover_separator := hseparator
    stopover_trimmed := htrimmed
    quotient_unhindered := hunhindered
    heightDelete_nonSource := hheightDelete
    heightWave_isWave := hheightWave
    stopover_roofed := hroofed
    heightDelete_card := hheightCard }

end FairResolutionLimit
end ResolutionChain
end ReachableResolutionRecursor
end IndexedTerminalResolutionState
end LinkageBlueprint
end Blueprint
end Erdos599
