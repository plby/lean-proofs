/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayCofinalJointSurvivor

/-!
# Cofinal survivors with an honest hybrid stop-over

After a nontrivial target tail is attached, its first contact with
`C.newSlice` is an internal point of the accumulated real relation.  Hence
the reference-filtering slice and the final terminal stop-over have different
roles.  This file keeps `C.newSlice` as the slice used to select the untouched
ladder-reference components, but lets the scheduler export the actual hybrid
stop-over separately.

This avoids the fixed-frontier target-route obstruction.  The cofinal run is
still the concrete two-track `CofinalRoofedFrontSurvivor`, so its target phase,
fairness, edge reality, bi-uniqueness, and reverse well-foundedness are all
constructed.  Exact root/sink equations derive orbit endpoint purity.  The
only path-purity field retained explicitly is for the untouched reference
remainder, whose terminal set can change when the hybrid stop-over differs
from the reference-filtering slice.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace Blueprint
namespace LinkageBlueprint

open DirectedPath _root_.Erdos599.Alternating

universe u v

variable {V : Type u}
variable {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}} {I : Type v}
variable [Preorder I] [Nonempty I] [IsDirectedOrder I]

/-- Exact final data for a cofinal real-part run whose local club slice and
actual terminal stop-over need not coincide. -/
structure CofinalHybridFrontierSurvivor
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (A0 : Set V) where
  run : CofinalRoofedFrontSurvivor Gamma Y kappa Gamma.target I
  reference_eq : Y = C.selectedReference
  stopover : Set V
  designated_source : A0 ⊆ Gamma.source
  designated_root : A0 ⊆
    {x | x ∈ run.toCofinalBlueprintRelationRun.finalCarrier ∧
      ¬ ∃ y, (y, x) ∈ run.toCofinalBlueprintRelationRun.finalEdge}
  source_boundary :
    {x | x ∈ run.toCofinalBlueprintRelationRun.finalCarrier ∧
      ¬ ∃ y, (y, x) ∈ run.toCofinalBlueprintRelationRun.finalEdge} ∪
        Gamma.initialSet
          (referencePathsMeeting Y C.newSlice \
            referencePathsMeeting Y
              run.toCofinalBlueprintRelationRun.finalCarrier) =
      Gamma.source
  terminal_boundary :
    {x | x ∈ run.toCofinalBlueprintRelationRun.finalCarrier ∧
      ¬ ∃ y, (x, y) ∈ run.toCofinalBlueprintRelationRun.finalEdge} ∪
        Gamma.terminalFrontier
          (referencePathsMeeting Y C.newSlice \
            referencePathsMeeting Y
              run.toCofinalBlueprintRelationRun.finalCarrier) =
      stopover
  no_directedRay :
    ¬ ContainsDirectedRay run.toCofinalBlueprintRelationRun.finalEdge
  reference_endpointPure :
    ∀ p ∈
        (referencePathsMeeting Y C.newSlice \
          referencePathsMeeting Y
            run.toCofinalBlueprintRelationRun.finalCarrier),
      CardinalInduction.IsPathBetween Gamma Gamma.source stopover p
  stopover_separator :
    CardinalInduction.IsSeparatorFrom Gamma Gamma.source stopover
  stopover_trimmed : Gamma.essential stopover = stopover
  quotient_unhindered : (Gamma.quotient stopover).IsUnhindered
  height : CardinalInduction.HeightAtMost Gamma stopover kappa
  source_disjoint : Disjoint Gamma.source stopover

namespace CofinalHybridFrontierSurvivor

variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
variable {A0 : Set V}

/-- The exact hybrid root/sink boundary excludes forward rays and therefore
makes every canonical orbit a finite source-to-stop-over path. -/
theorem blueprint_endpointPure
    (S : CofinalHybridFrontierSurvivor (I := I) C A0) :
    ∀ p ∈
        (orientationBlueprint
          S.run.toCofinalBlueprintRelationRun.rankedFairGlobalRelation.oriented.orientation).paths,
      (orientationBlueprint
        S.run.toCofinalBlueprintRelationRun.rankedFairGlobalRelation.oriented.orientation).IsPathBetween
          Gamma.source S.stopover p := by
  exact blueprintEndpointPure_of_boundary
    S.run.toCofinalBlueprintRelationRun.rankedFairGlobalRelation S.stopover
    (by simpa only [CofinalBlueprintRelationRun.rankedFairGlobalRelation_edge]
      using S.no_directedRay)
    (by simpa only [CofinalBlueprintRelationRun.rankedFairGlobalRelation_carrier,
        CofinalBlueprintRelationRun.rankedFairGlobalRelation_edge]
      using S.source_boundary)
    (by simpa only [CofinalBlueprintRelationRun.rankedFairGlobalRelation_carrier,
        CofinalBlueprintRelationRun.rankedFairGlobalRelation_edge]
      using S.terminal_boundary)

/-- Compile the honest hybrid survivor to the existing global geometry,
without identifying its stop-over with the club slice. -/
theorem exists_finalGeometry
    (S : CofinalHybridFrontierSurvivor (I := I) C A0) :
    Nonempty (CardinalInduction.HalfwayScheduler.RankedFairFinalGeometry
      S.run.toCofinalBlueprintRelationRun.rankedFairGlobalRelation A0) := by
  obtain ⟨X, ⟨hXsource, Q, hQwave, hroof⟩, hXcard⟩ := S.height
  exact ⟨{
    slice := C.newSlice
    stopover := S.stopover
    heightDelete := X
    heightWave := Q
    reference_isWarp := by
      rw [S.reference_eq]
      exact C.selectedReference_isWarp
    designated_source := S.designated_source
    designated_root := by
      simpa only [CofinalBlueprintRelationRun.rankedFairGlobalRelation_carrier,
        CofinalBlueprintRelationRun.rankedFairGlobalRelation_edge] using
        S.designated_root
    source_cover := by
      simpa only [CofinalBlueprintRelationRun.rankedFairGlobalRelation_carrier,
        CofinalBlueprintRelationRun.rankedFairGlobalRelation_edge] using
        S.source_boundary
    terminal_frontier := by
      simpa only [CofinalBlueprintRelationRun.rankedFairGlobalRelation_carrier,
        CofinalBlueprintRelationRun.rankedFairGlobalRelation_edge] using
        S.terminal_boundary
    blueprint_endpointPure := S.blueprint_endpointPure
    reference_endpointPure := S.reference_endpointPure
    stopover_separator := S.stopover_separator
    stopover_trimmed := S.stopover_trimmed
    quotient_unhindered := S.quotient_unhindered
    heightDelete_nonSource := hXsource
    heightWave_isWave := hQwave
    stopover_roofed := hroof
    heightDelete_card := hXcard }⟩

/-- The hybrid survivor yields the proper, source-disjoint exact-frontier
output directly. -/
theorem exists_properExactFrontierHalfwayLinkage
    (S : CofinalHybridFrontierSurvivor (I := I) C A0) :
    ∃ W : Set Gamma.DPath,
      CardinalInduction.ProperExactFrontierHalfwayLinkageOfAltitude
        Gamma A0 kappa W := by
  obtain ⟨F⟩ := S.exists_finalGeometry
  apply F.certificate.exists_properExactFrontierHalfwayLinkage
  exact S.source_disjoint

/-- Public exact-frontier projection. -/
theorem exists_exactFrontierHalfwayLinkage
    (S : CofinalHybridFrontierSurvivor (I := I) C A0) :
    ∃ W : Set Gamma.DPath,
      CardinalInduction.ExactFrontierHalfwayLinkageOfAltitude
        Gamma A0 kappa W := by
  obtain ⟨W, hW⟩ := S.exists_properExactFrontierHalfwayLinkage
  exact ⟨W, hW.toExactFrontier⟩

end CofinalHybridFrontierSurvivor

/-- Exact public producer signature for an honest `Nat`-indexed hybrid
scheduler. -/
theorem exactFrontierHalfwayClauseAt_of_natHybridSurvivors
    (produce : ∀ A0 : Set V, A0 ⊆ Gamma.source → #A0 = kappa →
      ∃ (Y : Set Gamma.DPath)
        (C : ClubStageGeometry Gamma Y kappa (succ kappa)),
        Nonempty (CofinalHybridFrontierSurvivor (I := ℕ) C A0)) :
    CardinalInduction.ExactFrontierHalfwayClauseAt Gamma kappa := by
  intro A0 hA0 hcard
  obtain ⟨Y, C, ⟨S⟩⟩ := produce A0 hA0 hcard
  exact S.exists_exactFrontierHalfwayLinkage

#print axioms CofinalHybridFrontierSurvivor.blueprint_endpointPure
#print axioms CofinalHybridFrontierSurvivor.exists_finalGeometry
#print axioms
  CofinalHybridFrontierSurvivor.exists_properExactFrontierHalfwayLinkage
#print axioms exactFrontierHalfwayClauseAt_of_natHybridSurvivors

end LinkageBlueprint
end Blueprint
end Erdos599
