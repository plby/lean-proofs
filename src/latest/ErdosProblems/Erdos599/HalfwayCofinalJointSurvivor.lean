/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayRoofedFrontCofinal
import ErdosProblems.Erdos599.HalfwayProperClubFinalGeometry

/-!
# The minimal joint survivor consumed by the cofinal half-way compiler

The roofed front and the ambient target tails have different jobs.  The
front supplies the local club boundary, while target tails witness resolution
of scheduled real terminals.  They must not be identified: an ambient target
tail generally leaves the selected club frontier.

This file records the exact remaining scheduler invariant.  Its `run` is an
actual cofinal run of monotone blueprint real parts, so edge reality,
bi-uniqueness, reverse well-foundedness, fairness, and target resolution are
already constructive data.  The extra fields are precisely the joint-survivor
facts not supplied by tail attachment: preservation of the selected-reference
source boundary, the exact later-frontier sink boundary, exclusion of a
forward ray, designated roots, and source-disjointness of the stop-over.

Both path-level endpoint-purity conditions are derived below; they are not
fields of the survivor.  Thus this is strictly smaller than a
`RankedClubFrontierBoundary` or a resolved-certificate callback.
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

/-- The minimal honest output of the two-track scheduler.

`run` is the accumulated real track.  The two exact boundary equations say
that the roofed front/reference track is compatible with that accumulation.
Target tails occur only through `run.resolved`; they are not required to lie
in `C.outerRoof` or to end on `C.newSlice`. -/
structure CofinalJointFrontierSurvivor
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (A0 : Set V) where
  run : CofinalRoofedFrontSurvivor Gamma Y kappa Gamma.target I
  reference_eq : Y = C.selectedReference
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
      C.newSlice
  no_directedRay :
    ¬ ContainsDirectedRay run.toCofinalBlueprintRelationRun.finalEdge
  source_disjoint : Disjoint Gamma.source C.newSlice

namespace CofinalJointFrontierSurvivor

variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
variable {A0 : Set V}

/-- The untouched selected-reference remainder is endpoint-pure.  Marker
components cannot remain on the reference side of `source_boundary`, since
their initial vertices are outside the ambient source. -/
theorem reference_endpointPure
    (S : CofinalJointFrontierSurvivor (I := I) C A0) :
    ∀ p ∈
        (referencePathsMeeting Y C.newSlice \
          referencePathsMeeting Y
            S.run.toCofinalBlueprintRelationRun.finalCarrier),
      CardinalInduction.IsPathBetween Gamma Gamma.source C.newSlice p := by
  intro p hp
  have hpSource : p.initial ∈ Gamma.source := by
    rw [← S.source_boundary]
    exact Or.inr ⟨p, hp, rfl⟩
  have hpSelected : p ∈ C.selectedReference := by
    rw [← S.reference_eq]
    exact hp.1.1
  exact ladderReference.endpointPure_of_initial_mem_source
    C.normalized C.legal hpSelected hpSource

/-- Exact relation boundaries and forward-ray exclusion derive endpoint
purity of every canonical root orbit. -/
theorem blueprint_endpointPure
    (S : CofinalJointFrontierSurvivor (I := I) C A0) :
    ∀ p ∈
        (orientationBlueprint
          S.run.toCofinalBlueprintRelationRun.rankedFairGlobalRelation.oriented.orientation).paths,
      (orientationBlueprint
        S.run.toCofinalBlueprintRelationRun.rankedFairGlobalRelation.oriented.orientation).IsPathBetween
          Gamma.source C.newSlice p := by
  exact blueprintEndpointPure_of_boundary
    S.run.toCofinalBlueprintRelationRun.rankedFairGlobalRelation C.newSlice
    (by simpa only [CofinalBlueprintRelationRun.rankedFairGlobalRelation_edge]
      using S.no_directedRay)
    (by simpa only [CofinalBlueprintRelationRun.rankedFairGlobalRelation_carrier,
        CofinalBlueprintRelationRun.rankedFairGlobalRelation_edge]
      using S.source_boundary)
    (by simpa only [CofinalBlueprintRelationRun.rankedFairGlobalRelation_carrier,
        CofinalBlueprintRelationRun.rankedFairGlobalRelation_edge]
      using S.terminal_boundary)

/-- Compile the minimal survivor into the boundary expected by the global
cofinal relation theorem. -/
theorem toRankedClubFrontierBoundary
    (S : CofinalJointFrontierSurvivor (I := I) C A0) :
    CardinalInduction.HalfwayScheduler.RankedClubFrontierBoundary C
      S.run.toCofinalBlueprintRelationRun.rankedFairGlobalRelation A0 where
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

/-- The same survivor retains the quotient-domain condition on the selected
frontier. -/
theorem toProperRankedClubFrontierBoundary
    (S : CofinalJointFrontierSurvivor (I := I) C A0) :
    ProperRankedClubFrontierBoundary C
      S.run.toCofinalBlueprintRelationRun.rankedFairGlobalRelation A0 where
  boundary := S.toRankedClubFrontierBoundary
  source_disjoint := S.source_disjoint

/-- A minimal joint survivor closes all the way to the source-disjoint exact
frontier linkage. -/
theorem exists_properExactFrontierHalfwayLinkage
    (S : CofinalJointFrontierSurvivor (I := I) C A0) :
    ∃ W : Set Gamma.DPath,
      CardinalInduction.ProperExactFrontierHalfwayLinkageOfAltitude
        Gamma A0 kappa W := by
  exact S.run.toCofinalBlueprintRelationRun.exists_properExactFrontierHalfwayLinkage
    S.toProperRankedClubFrontierBoundary

/-- Public exact-frontier projection of the same concrete survivor. -/
theorem exists_exactFrontierHalfwayLinkage
    (S : CofinalJointFrontierSurvivor (I := I) C A0) :
    ∃ W : Set Gamma.DPath,
      CardinalInduction.ExactFrontierHalfwayLinkageOfAltitude
        Gamma A0 kappa W := by
  obtain ⟨W, hW⟩ := S.exists_properExactFrontierHalfwayLinkage
  exact ⟨W, hW.toExactFrontier⟩

end CofinalJointFrontierSurvivor

/-- Concrete `Nat`-scheduler producer signature sufficient for the public
exact-frontier half-way clause.  The geometry and its selected reference may
depend on the designated set; no fixed-reference callback is assumed. -/
theorem exactFrontierHalfwayClauseAt_of_natJointSurvivors
    (produce : ∀ A0 : Set V, A0 ⊆ Gamma.source → #A0 = kappa →
      ∃ (Y : Set Gamma.DPath)
        (C : ClubStageGeometry Gamma Y kappa (succ kappa)),
        Nonempty (CofinalJointFrontierSurvivor (I := ℕ) C A0)) :
    CardinalInduction.ExactFrontierHalfwayClauseAt Gamma kappa := by
  intro A0 hA0 hcard
  obtain ⟨Y, C, ⟨S⟩⟩ := produce A0 hA0 hcard
  exact S.exists_exactFrontierHalfwayLinkage

#print axioms CofinalJointFrontierSurvivor.reference_endpointPure
#print axioms CofinalJointFrontierSurvivor.blueprint_endpointPure
#print axioms CofinalJointFrontierSurvivor.toRankedClubFrontierBoundary
#print axioms CofinalJointFrontierSurvivor.exists_properExactFrontierHalfwayLinkage
#print axioms exactFrontierHalfwayClauseAt_of_natJointSurvivors

end LinkageBlueprint
end Blueprint
end Erdos599
