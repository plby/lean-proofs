/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import ErdosProblems.Erdos735.ConcreteStage4BeltClassification
import ErdosProblems.Erdos735.Stage4ContinuationExtraction

/-!
# Assembly of the antipodally correct Stage-4 continuation

This module joins the canonical endpoint triangles to projective belt
exhaustion.  Its two inputs are the exact remaining geometric statements:
coverage of projective interval starts, and exclusion of the outside face
at each endpoint interval.
-/

open Classical
noncomputable section

namespace Erdos735.ConcreteStage4ProjectiveContinuation

open ProjectiveArrangement ProjectiveBoundaryExtraction
open SignVector SignVectorArrangement

abbrev Point := ProjectiveArrangement.Point

variable {P : Finset Point} {w : Point → ℝ} {c : ℝ}
variable (hred : IsReducedMagic P w c)
variable {a b d : Point}
variable (ha : a ∈ nonordinaryPoints P) (hb : b ∈ nonordinaryPoints P)
variable (hd : d ∈ nonordinaryPoints P)
variable (hncol : ¬ ProjectiveDuality.Collinear3 a b d)
variable [Nonempty (ProjectiveBoundaryExtraction.Line (nonordinaryPoints P))]

private abbrev B := nonordinaryPoints P
private abbrev D := ConcretePolarABKPRData.concreteData hred ha hb hd hncol
private abbrev Line := ProjectiveBoundaryExtraction.Line (B (P := P))

variable (hAcard : 3 ≤ (ordinaryPoints P).card)
variable (hnotFF : ¬ IsFailedFano P)

private abbrev L := ConcreteStage4FlankComplete.flankSystem
  hred ha hb hd hncol hAcard hnotFF
private abbrev G := (L hred ha hb hd hncol hAcard hnotFF).toHelpingGraph

/-- The two checked local/global belt outputs assemble directly to the
corrected continuation package. -/
noncomputable def continuationOfOccupied
    (hHall : ¬ (G hred ha hb hd hncol hAcard hnotFF).NoEvilEvilPath)
    (hoccupied : ConcreteStage4OccupiedBelt.occupiedStarts
      hred ha hb hd hncol hAcard hnotFF hHall = Finset.univ)
    (hendpointOther : ∀ k : Fin 2,
      strictFaceDegree (normals (B (P := P)))
        (edgeFace (normals (B (P := P))) (normals_ne_zero (B (P := P)))
          (ConcreteStage4OccupiedBelt.endpointStrictEdge
            hred ha hb hd hncol hAcard hnotFF hHall k)
          (!(ConcreteStage4ContinuationEndpoints.endpointTriangle
            hred ha hb hd hncol hAcard hnotFF hHall k).1
            (ConcreteStage4OccupiedBelt.endpointStrictEdge
              hred ha hb hd hncol hAcard hnotFF hHall k).1.1)) ≠ 3) :
    ABKPR.Data.ProjectiveDeficientPathContinuation
      (L hred ha hb hd hncol hAcard hnotFF) hHall where
  endpointTriangle := ConcreteStage4ContinuationEndpoints.endpointTriangle
    hred ha hb hd hncol hAcard hnotFF hHall
  endpointTriangle_incident_own :=
    ConcreteStage4ContinuationEndpoints.endpointTriangle_incident_own
      hred ha hb hd hncol hAcard hnotFF hHall
  endpointTriangle_degree_three :=
    ConcreteStage4ContinuationEndpoints.endpointTriangle_degree_three
      hred ha hb hd hncol hAcard hnotFF hHall
  allIncidentTrianglesAreEndpointOrAntipode :=
    ConcreteStage4BeltClassification.all_incident_triangles_are_endpoint_or_antipode_of_occupied
      hred ha hb hd hncol hAcard hnotFF hHall hoccupied hendpointOther

/-- Assembly through the topology-correct joint endpoint-slot classifier.
This form permits the two endpoint intervals to coincide. -/
noncomputable def continuationOfOccupiedAndEndpointSlots
    (hHall : ¬ (G hred ha hb hd hncol hAcard hnotFF).NoEvilEvilPath)
    (hoccupied : ConcreteStage4OccupiedBelt.occupiedStarts
      hred ha hb hd hncol hAcard hnotFF hHall = Finset.univ)
    (hendpoint : ConcreteStage4BeltClassification.EndpointSlotsClassified
      hred ha hb hd hncol hAcard hnotFF hHall) :
    ABKPR.Data.ProjectiveDeficientPathContinuation
      (L hred ha hb hd hncol hAcard hnotFF) hHall where
  endpointTriangle := ConcreteStage4ContinuationEndpoints.endpointTriangle
    hred ha hb hd hncol hAcard hnotFF hHall
  endpointTriangle_incident_own :=
    ConcreteStage4ContinuationEndpoints.endpointTriangle_incident_own
      hred ha hb hd hncol hAcard hnotFF hHall
  endpointTriangle_degree_three :=
    ConcreteStage4ContinuationEndpoints.endpointTriangle_degree_three
      hred ha hb hd hncol hAcard hnotFF hHall
  allIncidentTrianglesAreEndpointOrAntipode :=
    ConcreteStage4BeltClassification.all_incident_triangles_are_endpoint_or_antipode_of_endpointSlots
      hred ha hb hd hncol hAcard hnotFF hHall hoccupied hendpoint

end Erdos735.ConcreteStage4ProjectiveContinuation
