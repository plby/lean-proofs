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

/-!
# Noncollision in the concrete Stage-4 projective belt

This file turns local literal polar geometry into the collision exclusions
needed by the cyclic occupied-belt argument.  An evil--helper adjacency has
distinct projective opposite intervals by the two-edge face argument in
`ConcreteStage4BeltStep`.  An endpoint triangle cannot collide with its
endpoint evil's interval because every face slot above a component-cell
interval is nontriangular.
-/

open Classical
noncomputable section

namespace Erdos735.ConcreteStage4BeltNoncollision

open ProjectiveArrangement ProjectiveBoundaryExtraction
open ChartOrder SignVector SignVectorArrangement

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

variable (hAcard : 3 ≤ (ordinaryPoints P).card)
variable (hnotFF : ¬ IsFailedFano P)

private abbrev L := ConcreteStage4FlankComplete.flankSystem
  hred ha hb hd hncol hAcard hnotFF
private abbrev G := (L hred ha hb hd hncol hAcard hnotFF).toHelpingGraph

/-- An endpoint triangle's projective interval cannot equal the interval
of any component cell: the former carries a triangular incident face,
whereas the latter's complete projective slot was proved nontriangular. -/
theorem endpointEdge_ne_componentCell
    (hHall : ¬ (G hred ha hb hd hncol hAcard hnotFF).NoEvilEvilPath)
    (k : Fin 2)
    (x : ConcreteStage4OccupiedBelt.ComponentCell
      hred ha hb hd hncol hAcard hnotFF hHall) :
    ConcreteStage4OccupiedBelt.endpointCyclicEdge
        hred ha hb hd hncol hAcard hnotFF hHall k ≠
      ConcreteStage4OccupiedBelt.cellCyclicEdge
        hred ha hb hd hncol hAcard hnotFF hHall x := by
  intro heq
  apply ConcreteStage4BeltClassification.componentCell_projective_slot_not_triangle
    hred ha hb hd hncol hAcard hnotFF hHall x
    (ConcreteStage4OccupiedBelt.endpointStrictEdge
      hred ha hb hd hncol hAcard hnotFF hHall k)
    (ConcreteStage4ContinuationEndpoints.endpointTriangle
      hred ha hb hd hncol hAcard hnotFF hHall k)
  · rw [ConcreteStage4OccupiedBelt.endpointStrictEdge_lifted_base]
    exact heq
  · exact ConcreteStage4BeltClassification.endpointStrictEdge_incident
      hred ha hb hd hncol hAcard hnotFF hHall k
  · exact ConcreteStage4BeltClassification.endpointTriangle_strictFaceDegree_three
      hred ha hb hd hncol hAcard hnotFF hHall k

/-- Every augmented-belt adjacency other than the permitted
endpoint--endpoint closing pair joins two distinct projective intervals. -/
theorem adjacent_intervals_ne_of_not_endpoint_pair
    (hHall : ¬ (G hred ha hb hd hncol hAcard hnotFF).NoEvilEvilPath)
    {x y : ConcreteStage4OccupiedBelt.BeltItem
      hred ha hb hd hncol hAcard hnotFF hHall}
    (hxy : ConcreteStage4OccupiedBelt.BeltAdjacent
      hred ha hb hd hncol hAcard hnotFF hHall x y)
    (hnot : ¬ ∃ k l : Fin 2, x = Sum.inr k ∧ y = Sum.inr l) :
    ConcreteStage4OccupiedBelt.beltCyclicEdge
        hred ha hb hd hncol hAcard hnotFF hHall x ≠
      ConcreteStage4OccupiedBelt.beltCyclicEdge
        hred ha hb hd hncol hAcard hnotFF hHall y := by
  let LL := L hred ha hb hd hncol hAcard hnotFF
  rcases x with (e | h) | k <;> rcases y with (e' | h') | l
  · exact False.elim hxy
  · exact ConcreteStage4BeltStep.oppositeBeltEdges_ne_of_adj
      hred ha hb hd hncol
      (ConcreteStage4OccupiedBelt.pick ha hb hncol) LL
      (ConcreteStage4FlankComplete.flankSystem_edgeLine
        hred ha hb hd hncol hAcard hnotFF) hxy
  · exact (endpointEdge_ne_componentCell
      hred ha hb hd hncol hAcard hnotFF hHall l (Sum.inl e)).symm
  · exact (ConcreteStage4BeltStep.oppositeBeltEdges_ne_of_adj
      hred ha hb hd hncol
      (ConcreteStage4OccupiedBelt.pick ha hb hncol) LL
      (ConcreteStage4FlankComplete.flankSystem_edgeLine
        hred ha hb hd hncol hAcard hnotFF) hxy).symm
  · exact False.elim hxy
  · exact False.elim hxy
  · exact endpointEdge_ne_componentCell
      hred ha hb hd hncol hAcard hnotFF hHall k (Sum.inl e')
  · exact False.elim hxy
  · exfalso
    apply hnot
    exact ⟨k, l, rfl, rfl⟩

/-- To prove the collision callback used by cyclic closure, it suffices to
handle centers that are genuine deficient-component cells.  At an endpoint
triangle center the two graph neighbors are its endpoint evil and the
other endpoint triangle; a collision between those intervals is ruled out
by `endpointEdge_ne_componentCell`. -/
theorem collision_forward_of_component
    (hHall : ¬ (G hred ha hb hd hncol hAcard hnotFF).NoEvilEvilPath)
    (hcomponent : ∀
      (x : ConcreteStage4OccupiedBelt.ComponentCell
        hred ha hb hd hncol hAcard hnotFF hHall)
      {y z : ConcreteStage4OccupiedBelt.BeltItem
        hred ha hb hd hncol hAcard hnotFF hHall},
      ConcreteStage4OccupiedBelt.BeltAdjacent
          hred ha hb hd hncol hAcard hnotFF hHall (Sum.inl x) y →
      ConcreteStage4OccupiedBelt.BeltAdjacent
          hred ha hb hd hncol hAcard hnotFF hHall (Sum.inl x) z →
      y ≠ z →
      (¬ ∃ k l : Fin 2, y = Sum.inr k ∧ z = Sum.inr l) →
      ConcreteStage4OccupiedBelt.beltCyclicEdge
          hred ha hb hd hncol hAcard hnotFF hHall y =
        ConcreteStage4OccupiedBelt.beltCyclicEdge
          hred ha hb hd hncol hAcard hnotFF hHall z →
      cyclicEdgeFinish
          (Finset.univ : Finset (ProjectiveBoundaryExtraction.Vertex (B (P := P))))
          (OnLine (B (P := P))) (vertexCoord (B (P := P)))
          (ConcreteStage4OccupiedBelt.beltCyclicEdge
            hred ha hb hd hncol hAcard hnotFF hHall (Sum.inl x)) =
        cyclicEdgeStart
          (ConcreteStage4OccupiedBelt.beltCyclicEdge
            hred ha hb hd hncol hAcard hnotFF hHall y)) :
    ∀ {x y z : ConcreteStage4OccupiedBelt.BeltItem
        hred ha hb hd hncol hAcard hnotFF hHall},
      ConcreteStage4OccupiedBelt.BeltAdjacent
          hred ha hb hd hncol hAcard hnotFF hHall x y →
      ConcreteStage4OccupiedBelt.BeltAdjacent
          hred ha hb hd hncol hAcard hnotFF hHall x z →
      y ≠ z →
      (¬ ∃ k l : Fin 2, y = Sum.inr k ∧ z = Sum.inr l) →
      ConcreteStage4OccupiedBelt.beltCyclicEdge
          hred ha hb hd hncol hAcard hnotFF hHall y =
        ConcreteStage4OccupiedBelt.beltCyclicEdge
          hred ha hb hd hncol hAcard hnotFF hHall z →
      cyclicEdgeFinish
          (Finset.univ : Finset (ProjectiveBoundaryExtraction.Vertex (B (P := P))))
          (OnLine (B (P := P))) (vertexCoord (B (P := P)))
          (ConcreteStage4OccupiedBelt.beltCyclicEdge
            hred ha hb hd hncol hAcard hnotFF hHall x) =
        cyclicEdgeStart
          (ConcreteStage4OccupiedBelt.beltCyclicEdge
            hred ha hb hd hncol hAcard hnotFF hHall y) := by
  intro x y z hxy hxz hyz hnot heq
  rcases x with x | k
  · exact hcomponent x hxy hxz hyz hnot heq
  · rcases y with (e | h) | l <;> rcases z with (e' | h') | m
    · exact hyz (congrArg (fun q ↦ Sum.inl (Sum.inl q))
        (Subtype.ext (hxy.trans hxz.symm))) |>.elim
    · exact False.elim hxz
    · exact (endpointEdge_ne_componentCell
        hred ha hb hd hncol hAcard hnotFF hHall m (Sum.inl e)) heq.symm |>.elim
    · exact False.elim hxy
    · exact False.elim hxy
    · exact False.elim hxy
    · exact (endpointEdge_ne_componentCell
        hred ha hb hd hncol hAcard hnotFF hHall l (Sum.inl e')) heq |>.elim
    · exact False.elim hxz
    · exfalso
      apply hnot
      exact ⟨l, m, rfl, rfl⟩

end Erdos735.ConcreteStage4BeltNoncollision
