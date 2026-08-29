/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwaySourceRootRealFamily
import ErdosProblems.Erdos599.HalfwayTerminalBoundaryLadder
import ErdosProblems.Erdos599.RoofedDeletionQuotient

/-!
# Protected final output of the fair half-way scheduler

The realized source-root blueprint family is kept separate from the finite
localized reference remainder.  Its carrier is roofed by the actual ladder
frontier, so deleting it before quotienting by that frontier preserves
unhinderedness.  No claim is made that the realized target paths avoid
persistent frontier vertices internally.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace CardinalInduction

universe u

variable {V : Type u}

/-- Exact protected payload supported by the fair final construction. -/
structure LocalizedProtectedHalfwayOutput
    (Gamma : DWeb V) (A0 : Set V) (kappa : Cardinal.{u}) where
  targetPaths : Set Gamma.DPath
  remainder : Set Gamma.DPath
  stopover : Set V
  targetPaths_isWarp : Gamma.IsWarp targetPaths
  targetPaths_finite : Gamma.HasFiniteCharacter targetPaths
  targetPaths_card : #targetPaths ≤ kappa
  targetPaths_initial_subset_source :
    Gamma.initialSet targetPaths ⊆ Gamma.source
  designated_initial : A0 ⊆ Gamma.initialSet targetPaths
  targetPaths_terminal_target :
    Gamma.terminalFrontier targetPaths ⊆ Gamma.target
  targetPaths_carrier_roof :
    Gamma.vertexSet targetPaths ⊆ Gamma.roof stopover
  targetPaths_link_designated : LinksToTarget Gamma targetPaths A0
  remainder_isWarp : Gamma.IsWarp remainder
  remainder_finite : Gamma.HasFiniteCharacter remainder
  remainder_initial_subset_source :
    Gamma.initialSet remainder ⊆ Gamma.source
  remainder_terminal_stopover :
    Gamma.terminalFrontier remainder ⊆ stopover
  remainder_endpointPure : ∀ p ∈ remainder,
    IsPathBetween Gamma Gamma.source stopover p
  families_disjoint : ∀ p ∈ targetPaths, ∀ q ∈ remainder,
    Disjoint p.support q.support
  source_cover : Gamma.initialSet targetPaths ∪
    Gamma.initialSet remainder = Gamma.source
  stopover_separator : IsSeparatorFrom Gamma Gamma.source stopover
  stopover_trimmed : IsTrimmedSeparator Gamma stopover
  protected_quotient_unhindered :
    ((Gamma.delete (Gamma.vertexSet targetPaths)).quotient
      stopover).IsUnhindered
  height : HeightAtMost Gamma stopover kappa

end CardinalInduction

namespace Blueprint
namespace LinkageBlueprint
namespace IndexedTerminalResolutionState
namespace ReachableResolutionRecursor
namespace ResolutionChain

universe u v w

variable {V : Type u} {Gamma : DWeb V}
variable {kappa : Cardinal.{u}}
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

/-- Extract the two literal original-web families and their protected
quotient from the fair source-rooted limit at an actual deferred-ladder
stage. -/
noncomputable def localizedProtectedOutput_of_ladder
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
    CardinalInduction.LocalizedProtectedHalfwayOutput Gamma A0 kappa := by
  let U := sourceRootBlueprint R.limit.blueprint
  let hreal : U.IsEdgeReal := R.sourceRoot_isEdgeReal
  let P := U.realFamily hreal
  let remainder := localizedReferenceRemainder L a U
  have hUblueprint : R.limit.blueprint.IsLinkageBlueprint
      (L.frontier a) (closure R.limit.stageIndex) persistent := by
    simpa only [hslice] using R.limit.isBlueprint
  have hnoRay : ¬ Alternating.ContainsDirectedRay
      R.limit.blueprint.edgeSet :=
    R.no_directedRay_of_subdivision hGamma hinc hkappa
  have hUfinite : ∀ p ∈ U.paths,
      ∃ q : DirectedPath.FinitePath
        (imaginaryGraph Gamma L.limitWarp kappa), p = .inl q :=
    allFinite_of_no_directedRay U
      (sourceRootBlueprint_no_directedRay R.limit.blueprint hnoRay)
  have hblueprintLinks : U.BlueprintLinksToTarget A0 := by
    apply sourceRootBlueprint_blueprintLinksToTarget_of_noRay
      R.limit.blueprint hGamma R.real_limit hnoRay hA0source
    · exact R.designated_initial_sourceRoot hA0source hA0initial
    · exact R.sourceRoot_realTerminals_target
  let hex := R.exists_localizedTerminalBoundaryHalfway_of_ladder a hslice hL
    hGamma hinc hkappa hstage hA0source hA0initial
  let W := Classical.choose hex
  have hchosen := Classical.choose_spec hex
  have hstop := hchosen.1
  have hheight := hchosen.2.2
  have hProot : Gamma.vertexSet P ⊆ Gamma.roof (L.frontier a) := by
    change Gamma.vertexSet (U.realFamily hreal) ⊆ Gamma.roof (L.frontier a)
    rw [U.vertexSet_realFamily]
    exact (sourceRootBlueprint_isLinkageBlueprint
      R.limit.blueprint hUblueprint).vertices_roofed
  exact {
    targetPaths := P
    remainder := remainder
    stopover := L.frontier a
    targetPaths_isWarp := U.isWarp_realFamily hreal
    targetPaths_finite := U.finiteCharacter_realFamily hreal hUfinite
    targetPaths_card := U.mk_realFamily_le hreal
      (sourceRootBlueprint_isLinkageBlueprint
        R.limit.blueprint hUblueprint).card_paths
    targetPaths_initial_subset_source := by
      change Gamma.initialSet (U.realFamily hreal) ⊆ Gamma.source
      rw [U.initialSet_realFamily]
      exact sourceRootBlueprint_initialSet_subset_source R.limit.blueprint
    designated_initial := by
      change A0 ⊆ Gamma.initialSet (U.realFamily hreal)
      rw [U.initialSet_realFamily]
      exact R.designated_initial_sourceRoot hA0source hA0initial
    targetPaths_terminal_target := by
      exact terminalFrontier_realFamily_sourceRoot_subset_target
        R.limit.blueprint R.real_limit R.sourceRoot_realTerminals_target
    targetPaths_carrier_roof := hProot
    targetPaths_link_designated :=
      U.linksToTarget_realFamily hreal hblueprintLinks
    remainder_isWarp := localizedReferenceRemainder_isWarp L a U hL
    remainder_finite := localizedReferenceRemainder_finiteCharacter L a U
    remainder_initial_subset_source :=
      localizedReferenceRemainder_initialSet_subset_source L a U
    remainder_terminal_stopover :=
      localizedReferenceRemainder_terminalFrontier_subset L a U hL
    remainder_endpointPure :=
      localizedReferenceRemainder_endpointPure L a U hGamma hL
    families_disjoint := by
      intro p hp q hq
      obtain ⟨ps, rfl⟩ := hp
      rw [U.support_realPath hreal]
      exact localizedReferenceRemainder_disjoint L a U
        ps.1 ps.2 q hq
    source_cover := by
      change Gamma.initialSet (U.realFamily hreal) ∪
        Gamma.initialSet (localizedReferenceRemainder L a U) = Gamma.source
      rw [U.initialSet_realFamily]
      exact sourceRootBlueprint_initial_union_localizedReferenceRemainder
        L a R.limit.blueprint hL hUblueprint
    stopover_separator := hstop.separator
    stopover_trimmed := hstop.trimmed
    protected_quotient_unhindered :=
      Gamma.delete_quotient_isUnhindered_of_subset_roof hProot
        hstop.trimmed hstop.separator hstop.quotient_unhindered
    height := hheight }

end FairResolutionLimit
end ResolutionChain
end ReachableResolutionRecursor
end IndexedTerminalResolutionState
end LinkageBlueprint
end Blueprint
end Erdos599
