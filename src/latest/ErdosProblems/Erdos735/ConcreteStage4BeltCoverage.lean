/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import ErdosProblems.Erdos735.ConcreteStage4BeltCollisionHelper
import ErdosProblems.Erdos735.ConcreteStage4EndpointIntervalSeparation
import ErdosProblems.Erdos735.ConcreteProjectiveLeviPathExtraction

/-!
# Exhaustion of the concrete Stage-4 projective belt

The two different graph incidences at a deficient-component cell meet the
cell's opposite edge at its two different projective endpoints.  Therefore,
if the two neighboring cells collapse to the same projective interval, that
interval is the reverse of the center interval.  Together with endpoint
separation this supplies the collision-safe cyclic closure theorem and shows
that every projective interval on the selected line is occupied.
-/

open Classical
noncomputable section

namespace Erdos735.ConcreteStage4BeltCoverage

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
private abbrev X := ConcretePolarCellulation.boundaryExtraction
  (B (P := P)) ha hb hd hncol
private abbrev Line := ProjectiveBoundaryExtraction.Line (B (P := P))
private abbrev Vertex := ProjectiveBoundaryExtraction.Vertex (B (P := P))

variable (hAcard : 3 ≤ (ordinaryPoints P).card)
variable (hnotFF : ¬ IsFailedFano P)

private abbrev L := ConcreteStage4FlankComplete.flankSystem
  hred ha hb hd hncol hAcard hnotFF
private abbrev G := (L hred ha hb hd hncol hAcard hnotFF).toHelpingGraph

/-- If two distinct intervals on the selected line contain the same two
distinct projective vertices, the first finishes where the second starts. -/
private theorem finish_eq_start_of_shared_vertices
    (hHall : ¬ (G hred ha hb hd hncol hAcard hnotFF).NoEvilEvilPath)
    (x y : ConcreteStage4OccupiedBelt.BeltItem
      hred ha hb hd hncol hAcard hnotFF hHall)
    (hne : ConcreteStage4OccupiedBelt.beltCyclicEdge
        hred ha hb hd hncol hAcard hnotFF hHall x ≠
      ConcreteStage4OccupiedBelt.beltCyclicEdge
        hred ha hb hd hncol hAcard hnotFF hHall y)
    (v u : Vertex (P := P)) (hvu : v ≠ u)
    (hvx : v ∈ cyclicEdgeVertices (Finset.univ : Finset (Vertex (P := P)))
      (OnLine (B (P := P))) (vertexCoord (B (P := P)))
      (ConcreteStage4OccupiedBelt.beltCyclicEdge
        hred ha hb hd hncol hAcard hnotFF hHall x))
    (hux : u ∈ cyclicEdgeVertices (Finset.univ : Finset (Vertex (P := P)))
      (OnLine (B (P := P))) (vertexCoord (B (P := P)))
      (ConcreteStage4OccupiedBelt.beltCyclicEdge
        hred ha hb hd hncol hAcard hnotFF hHall x))
    (hvy : v ∈ cyclicEdgeVertices (Finset.univ : Finset (Vertex (P := P)))
      (OnLine (B (P := P))) (vertexCoord (B (P := P)))
      (ConcreteStage4OccupiedBelt.beltCyclicEdge
        hred ha hb hd hncol hAcard hnotFF hHall y))
    (huy : u ∈ cyclicEdgeVertices (Finset.univ : Finset (Vertex (P := P)))
      (OnLine (B (P := P))) (vertexCoord (B (P := P)))
      (ConcreteStage4OccupiedBelt.beltCyclicEdge
        hred ha hb hd hncol hAcard hnotFF hHall y)) :
    cyclicEdgeFinish (Finset.univ : Finset (Vertex (P := P)))
        (OnLine (B (P := P))) (vertexCoord (B (P := P)))
        (ConcreteStage4OccupiedBelt.beltCyclicEdge
          hred ha hb hd hncol hAcard hnotFF hHall x) =
      cyclicEdgeStart
        (ConcreteStage4OccupiedBelt.beltCyclicEdge
          hred ha hb hd hncol hAcard hnotFF hHall y) := by
  exact ChartOrder.finish_eq_start_of_distinct_of_two_common_vertices
    (Finset.univ : Finset (Vertex (P := P)))
    (OnLine (B (P := P))) (vertexCoord (B (P := P)))
    (vertexCoord_injective (B (P := P)))
    (two_vertices_on_every_line (B (P := P)) ha hb hd hncol)
    (ConcreteStage4OccupiedBelt.beltCyclicEdge
      hred ha hb hd hncol hAcard hnotFF hHall x)
    (ConcreteStage4OccupiedBelt.beltCyclicEdge
      hred ha hb hd hncol hAcard hnotFF hHall y)
    ((ConcreteStage4OccupiedBelt.beltCyclicEdge_line
      hred ha hb hd hncol hAcard hnotFF hHall x).trans
      (ConcreteStage4OccupiedBelt.beltCyclicEdge_line
        hred ha hb hd hncol hAcard hnotFF hHall y).symm)
    hne v u hvu hvx hux hvy huy

/-- At a genuine component-cell center, a collision of its two different
neighbor intervals has the forced forward orientation. -/
theorem component_collision_forward
    (hHall : ¬ (G hred ha hb hd hncol hAcard hnotFF).NoEvilEvilPath) :
    ∀ (x : ConcreteStage4OccupiedBelt.ComponentCell
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
      cyclicEdgeFinish (Finset.univ : Finset (Vertex (P := P)))
          (OnLine (B (P := P))) (vertexCoord (B (P := P)))
          (ConcreteStage4OccupiedBelt.beltCyclicEdge
            hred ha hb hd hncol hAcard hnotFF hHall (Sum.inl x)) =
        cyclicEdgeStart
          (ConcreteStage4OccupiedBelt.beltCyclicEdge
            hred ha hb hd hncol hAcard hnotFF hHall y) := by
  intro x y z hxy hxz hyz hnot heq
  let LL := L hred ha hb hd hncol hAcard hnotFF
  let hedge := ConcreteStage4FlankComplete.flankSystem_edgeLine
    hred ha hb hd hncol hAcard hnotFF
  rcases x with e | h
  · rcases y with (ey | hy) | ky <;> rcases z with (ez | hz) | kz
    · exact False.elim hxy
    · exact False.elim hxy
    · exact False.elim hxy
    · exact False.elim hxz
    ·
      have hhk : hy.1 ≠ hz.1 := by
        intro hval
        apply hyz
        exact congrArg (fun q ↦ Sum.inl (Sum.inr q)) (Subtype.ext hval)
      obtain ⟨v, u, hvu, hvE, huE, hvH, huK⟩ :=
        ConcreteStage4BeltCollision.two_helpers_distinct_projective_vertices
          hred ha hb hd hncol
          (ConcreteStage4OccupiedBelt.pick ha hb hncol) LL hedge hxy hxz hhk
      have hne := ConcreteStage4BeltNoncollision.adjacent_intervals_ne_of_not_endpoint_pair
        hred ha hb hd hncol hAcard hnotFF hHall hxy (by
          rintro ⟨k, l, hk, -⟩
          cases hk)
      apply finish_eq_start_of_shared_vertices
        hred ha hb hd hncol hAcard hnotFF hHall
        (Sum.inl (Sum.inl e)) (Sum.inl (Sum.inr hy)) hne v u hvu
      · exact hvE
      · exact huE
      · exact hvH
      · rw [heq]
        exact huK
    · exact (ConcreteStage4BeltNoncollision.endpointEdge_ne_componentCell
        hred ha hb hd hncol hAcard hnotFF hHall kz (Sum.inr hy)) heq.symm |>.elim
    · exact False.elim hxz
    · exact (ConcreteStage4BeltNoncollision.endpointEdge_ne_componentCell
        hred ha hb hd hncol hAcard hnotFF hHall ky (Sum.inr hz)) heq |>.elim
    · exfalso
      apply hnot
      exact ⟨ky, kz, rfl, rfl⟩
  · rcases y with (ey | hy) | ky <;> rcases z with (ez | hz) | kz
    ·
      have hek : ey.1 ≠ ez.1 := by
        intro hval
        apply hyz
        exact congrArg (fun q ↦ Sum.inl (Sum.inl q)) (Subtype.ext hval)
      obtain ⟨v, u, hvu, hvH, huH, hvE, huK⟩ :=
        ConcreteStage4BeltCollisionHelper.two_evils_distinct_projective_vertices
          hred ha hb hd hncol
          (ConcreteStage4OccupiedBelt.pick ha hb hncol) LL hedge hxy hxz hek
      have hne := ConcreteStage4BeltNoncollision.adjacent_intervals_ne_of_not_endpoint_pair
        hred ha hb hd hncol hAcard hnotFF hHall hxy (by
          rintro ⟨k, l, hk, -⟩
          cases hk)
      apply finish_eq_start_of_shared_vertices
        hred ha hb hd hncol hAcard hnotFF hHall
        (Sum.inl (Sum.inr h)) (Sum.inl (Sum.inl ey)) hne v u hvu
      · exact hvH
      · exact huH
      · exact hvE
      · rw [heq]
        exact huK
    · exact False.elim hxz
    · exact False.elim hxz
    · exact False.elim hxy
    · exact False.elim hxy
    · exact False.elim hxy
    · exact False.elim hxy
    · exact False.elim hxy
    · exact False.elim hxy

/-- The augmented deficient component occupies every cyclic start on its
selected common opposite line. -/
theorem occupiedStarts_eq_univ
    (hHall : ¬ (G hred ha hb hd hncol hAcard hnotFF).NoEvilEvilPath) :
    ConcreteStage4OccupiedBelt.occupiedStarts
      hred ha hb hd hncol hAcard hnotFF hHall = Finset.univ := by
  apply ConcreteStage4EndpointBeltClosure.occupiedStarts_eq_univ_of_local_noncollision
    hred ha hb hd hncol hAcard hnotFF hHall
  · exact ConcreteStage4BeltNoncollision.adjacent_intervals_ne_of_not_endpoint_pair
      hred ha hb hd hncol hAcard hnotFF hHall
  · exact ConcreteStage4BeltNoncollision.collision_forward_of_component
      hred ha hb hd hncol hAcard hnotFF hHall
      (component_collision_forward
        hred ha hb hd hncol hAcard hnotFF hHall)
  · intro heq
    exact (ConcreteStage4EndpointIntervalSeparation.endpointCyclicEdges_ne
      hred ha hb hd hncol hAcard hnotFF hHall heq).elim

/-- Assumption-free concrete extraction of the projective Levi path for the
canonical geometric flank system. -/
theorem projectiveLeviPathExtraction :
    Nonempty (ABKPR.Data.ProjectiveLeviPathExtraction
      (B := X ha hb hd hncol)
      (L hred ha hb hd hncol hAcard hnotFF)) := by
  apply ConcreteProjectiveLeviPathExtraction.projectiveLeviPathExtraction_of_occupied
    hred ha hb hd hncol hAcard hnotFF
  exact occupiedStarts_eq_univ
    hred ha hb hd hncol hAcard hnotFF

end Erdos735.ConcreteStage4BeltCoverage
