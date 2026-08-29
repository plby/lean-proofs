/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayScheduler
import ErdosProblems.Erdos599.HalfwayStageGeometry
import ErdosProblems.Erdos599.HalfwayNormalizationHeight

/-!
# Closing the half-way scheduler at a club ladder stage

This file is the thin interface between the Section 9 scheduler and the
legal-ladder geometry.  A scheduler has to prove only its genuine boundary
facts: the roots cover the source together with the untouched reference
paths, the sinks give the selected club frontier, and both path families
have the right endpoints.  Essentiality, quotient unhinderedness, and the
explicit height witness are then consequences of legality and club
avoidance, rather than additional scheduler assumptions.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace HalfwayScheduler

open DirectedPath
open Blueprint
open Blueprint.LinkageBlueprint
open HalfwayNormalizationHeight.GloballyResolvedBlueprintCertificate

universe u v

variable {V : Type u}
variable {Gamma : DWeb V} {reference : Set Gamma.DPath}
variable {kappa : Cardinal.{u}} {I : Type v}
variable [Preorder I] [Nonempty I] [IsDirectedOrder I]

/-- The facts which really belong to the final scheduler relation at the
later club stage.  All ladder-geometric fields of
`RankedFairFinalGeometry` are deliberately absent. -/
structure RankedClubFrontierBoundary
    (C : ClubStageGeometry Gamma reference kappa (Order.succ kappa))
    (R : RankedFairGlobalRelation Gamma reference kappa Gamma.target I)
    (A0 : Set V) : Prop where
  reference_isWarp : Gamma.IsWarp reference
  designated_source : A0 ⊆ Gamma.source
  designated_root : A0 ⊆
    {x | x ∈ R.carrier ∧ ¬ ∃ y, (y, x) ∈ R.edge}
  source_cover :
    {x | x ∈ R.carrier ∧ ¬ ∃ y, (y, x) ∈ R.edge} ∪
        Gamma.initialSet
          (referencePathsMeeting reference C.newSlice \
            referencePathsMeeting reference R.carrier) =
      Gamma.source
  terminal_frontier :
    {x | x ∈ R.carrier ∧ ¬ ∃ y, (x, y) ∈ R.edge} ∪
        Gamma.terminalFrontier
          (referencePathsMeeting reference C.newSlice \
            referencePathsMeeting reference R.carrier) =
      C.newSlice
  blueprint_endpointPure :
    ∀ p ∈ (orientationBlueprint R.oriented.orientation).paths,
      (orientationBlueprint R.oriented.orientation).IsPathBetween
        Gamma.source C.newSlice p
  reference_endpointPure :
    ∀ p ∈
        (referencePathsMeeting reference C.newSlice \
          referencePathsMeeting reference R.carrier),
      CardinalInduction.IsPathBetween Gamma Gamma.source C.newSlice p

namespace RankedClubFrontierBoundary

variable {C : ClubStageGeometry Gamma reference kappa (Order.succ kappa)}
variable {R : RankedFairGlobalRelation
  Gamma reference kappa Gamma.target I}
variable {A0 : Set V}

/-- Club avoidance supplies stage unhinderedness; legality supplies the
trimmed frontier; and `frontier_heightAtMost` supplies the deletion set and
quotient wave.  Thus a checked scheduler boundary extends to the complete
final geometry without any additional hypotheses. -/
theorem exists_finalGeometry (B : RankedClubFrontierBoundary C R A0) :
    Nonempty (RankedFairFinalGeometry R A0) := by
  exact exists_rankedFairFinalGeometry_of_ladderFrontier
    C.normalized C.legal C.capacity_infinite C.newStage
    C.newStage_isUnhindered B.reference_isWarp B.designated_source
    B.designated_root B.source_cover B.terminal_frontier
    B.blueprint_endpointPure B.reference_endpointPure

/-- Strengthened form retaining the definitional identity of the selected
stop-over.  This identity is needed when a construction carried out in the
normalized web is transported back to an arbitrary ambient web. -/
theorem exists_finalGeometry_at_frontier
    (B : RankedClubFrontierBoundary C R A0) :
    ∃ F : RankedFairFinalGeometry R A0,
      F.stopover = C.newSlice := by
  obtain ⟨X, ⟨hXsource, Q, hQ, hroof⟩, hXcard⟩ :=
    HalfwayFrontierHeight.frontier_heightAtMost
      C.normalized C.legal C.capacity_infinite C.newStage
  refine ⟨{
    slice := C.newSlice
    stopover := C.newSlice
    heightDelete := X
    heightWave := Q
    reference_isWarp := B.reference_isWarp
    designated_source := B.designated_source
    designated_root := B.designated_root
    source_cover := B.source_cover
    terminal_frontier := B.terminal_frontier
    blueprint_endpointPure := B.blueprint_endpointPure
    reference_endpointPure := B.reference_endpointPure
    stopover_separator :=
      source_subset_roof_ladderFrontier C.legal C.newStage
    stopover_trimmed := C.legal.frontiersEssential C.newStage
    quotient_unhindered :=
      quotient_ladderFrontier_isUnhindered C.legal C.newStage
        C.newStage_isUnhindered
    heightDelete_nonSource := hXsource
    heightWave_isWave := hQ
    stopover_roofed := hroof
    heightDelete_card := hXcard }, rfl⟩

/-- The same boundary data, compiled all the way through the canonical
root-orbit orientation into the final scheduler interface. -/
theorem exists_globalResolution (B : RankedClubFrontierBoundary C R A0) :
    Nonempty (OrientedGlobalResolution Gamma A0 kappa) := by
  obtain ⟨F⟩ := B.exists_finalGeometry
  exact ⟨F.globalResolution⟩

/-- The final club-stage boundary already implies the exact qualified
half-way linkage for the designated source set. -/
theorem exists_halfwayLinkage (B : RankedClubFrontierBoundary C R A0) :
    ∃ W : Set Gamma.DPath,
      IsHalfwayLinkageOfAltitude Gamma A0 kappa W := by
  obtain ⟨F⟩ := B.exists_finalGeometry
  exact F.exists_halfwayLinkage

/-- If the entire club-stage scheduler is run in the normalization of an
arbitrary web, its frontier geometry transports back to the original web.
The legal ladder itself supplies the sole additional input required by the
normalization theorem: its selected frontier roofs the source. -/
theorem exists_original_halfwayLinkage
    {G : DWeb V}
    {normalizedReference : Set G.normalized.DPath}
    {C₀ : ClubStageGeometry G.normalized normalizedReference kappa
      (Order.succ kappa)}
    {R₀ : RankedFairGlobalRelation G.normalized normalizedReference
      kappa G.normalized.target I}
    {A₀ : Set V}
    (B : RankedClubFrontierBoundary C₀ R₀ A₀) :
    ∃ W : Set G.DPath,
      IsHalfwayLinkageOfAltitude G A₀ kappa W := by
  obtain ⟨F, hFstop⟩ := B.exists_finalGeometry_at_frontier
  have hsourceFrontier : G.source ⊆
      G.normalized.roof C₀.newSlice := by
    simpa using
      (source_subset_roof_ladderFrontier C₀.legal C₀.newStage)
  have hsourceStopover : G.source ⊆
      G.normalized.roof F.certificate.stopover := by
    change G.source ⊆ G.normalized.roof F.stopover
    rw [hFstop]
    exact hsourceFrontier
  exact exists_original_halfwayLinkage_of_source_roof
    F.certificate hsourceStopover

end RankedClubFrontierBoundary

end HalfwayScheduler
end CardinalInduction
end Erdos599
