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

import ErdosProblems.Erdos735.ConcreteStage4ProjectiveContinuation
import ErdosProblems.Erdos735.ConcreteOppositeLineCoherence
import ErdosProblems.Erdos735.ConcreteStage4EndpointSlots

/-!
# Concrete projective Levi-path extraction

This is the final assembly adapter for the Stage-4 line belt.  Once occupied
projective intervals cover the selected line and the two endpoint slots are
classified, it constructs the antipodally correct `ProjectiveLeviPathExtraction`.
-/

open Classical
noncomputable section

namespace Erdos735.ConcreteProjectiveLeviPathExtraction

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
private abbrev X := ConcretePolarCellulation.boundaryExtraction
  (B (P := P)) ha hb hd hncol

variable (hAcard : 3 ≤ (ordinaryPoints P).card)
variable (hnotFF : ¬ IsFailedFano P)

private abbrev L := ConcreteStage4FlankComplete.flankSystem
  hred ha hb hd hncol hAcard hnotFF
private abbrev G := (L hred ha hb hd hncol hAcard hnotFF).toHelpingGraph

/-- Exact adapter from the two literal belt facts to the corrected global
path extraction. -/
theorem projectiveLeviPathExtraction_of_resolvers
    (hoccupied : ∀ hHall :
      ¬ (G hred ha hb hd hncol hAcard hnotFF).NoEvilEvilPath,
      ConcreteStage4OccupiedBelt.occupiedStarts
        hred ha hb hd hncol hAcard hnotFF hHall = Finset.univ)
    (hendpoint : ∀ hHall :
      ¬ (G hred ha hb hd hncol hAcard hnotFF).NoEvilEvilPath,
      ConcreteStage4BeltClassification.EndpointSlotsClassified
        hred ha hb hd hncol hAcard hnotFF hHall) :
    Nonempty (ABKPR.Data.ProjectiveLeviPathExtraction
      (B := X ha hb hd hncol)
      (L hred ha hb hd hncol hAcard hnotFF)) := by
  let LL := L hred ha hb hd hncol hAcard hnotFF
  have hedgeConcrete : LL.edgeLine = ConcretePolarFlankBounds.edgeLine :=
    ConcreteStage4FlankComplete.flankSystem_edgeLine
      hred ha hb hd hncol hAcard hnotFF
  have hedge : LL.edgeLine = strictEdgeOwner := by
    calc
      LL.edgeLine = ConcretePolarFlankBounds.edgeLine := hedgeConcrete
      _ = strictEdgeOwner := by funext e; rfl
  let K := ConcreteOppositeLineCoherence.oppositeLineCoherence
    hred ha hb hd hncol LL hedgeConcrete
  apply ABKPR.Data.projectiveLeviPathExtraction_of_not_exceptional
    LL K hedge (Exceptional := IsFailedFano P) _ hnotFF
  intro hHall
  exact Or.inr ⟨
    ConcreteStage4ProjectiveContinuation.continuationOfOccupiedAndEndpointSlots
      hred ha hb hd hncol hAcard hnotFF hHall
      (hoccupied hHall) (hendpoint hHall)⟩

/-- After the concrete endpoint-slot theorem, only global coverage of the
occupied projective interval starts remains. -/
theorem projectiveLeviPathExtraction_of_occupied
    (hoccupied : ∀ hHall :
      ¬ (G hred ha hb hd hncol hAcard hnotFF).NoEvilEvilPath,
      ConcreteStage4OccupiedBelt.occupiedStarts
        hred ha hb hd hncol hAcard hnotFF hHall = Finset.univ) :
    Nonempty (ABKPR.Data.ProjectiveLeviPathExtraction
      (B := X ha hb hd hncol)
      (L hred ha hb hd hncol hAcard hnotFF)) :=
  projectiveLeviPathExtraction_of_resolvers
    hred ha hb hd hncol hAcard hnotFF hoccupied
    (ConcreteStage4EndpointSlots.endpointSlotsClassified
      hred ha hb hd hncol hAcard hnotFF)

end Erdos735.ConcreteProjectiveLeviPathExtraction
