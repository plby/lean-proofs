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

import ErdosProblems.Erdos735.ConcreteStage4BeltCollisionHelper
import ErdosProblems.Erdos735.ConcreteStage4EndpointIntervalSeparation

/-!
# Exhaustion of the concrete Stage-4 opposite-line belt

The deficient helping component, augmented by its two continuation
triangles, occupies every cyclic interval of the selected projective line.
The only delicate case is when two graph neighbors project to one interval;
literal far-corner geometry then supplies both distinct endpoints and fixes
the direction of the resulting two-interval cycle.
-/

open Classical
noncomputable section

namespace Erdos735.ConcreteStage4OccupiedBeltCoverage

open ProjectiveArrangement ProjectiveBoundaryExtraction
open ChartOrder SignVector SignVectorArrangement
open SignVector.ProjectiveEdgeEndpointEquiv
open ConcretePolarOrientedVertex ConcretePolarEdgeVertices

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
private abbrev Vertex := ProjectiveBoundaryExtraction.Vertex (B (P := P))

variable (hAcard : 3 ≤ (ordinaryPoints P).card)
variable (hnotFF : ¬ IsFailedFano P)

private abbrev L := ConcreteStage4FlankComplete.flankSystem
  hred ha hb hd hncol hAcard hnotFF
private abbrev G := (L hred ha hb hd hncol hAcard hnotFF).toHelpingGraph

/-- Literal membership in an item's strict edge projects to membership in
that item's projective cyclic belt interval. -/
theorem fst_mem_beltCyclicEdge_of_mem
    (hHall : ¬ (G hred ha hb hd hncol hAcard hnotFF).NoEvilEvilPath)
    (x : ConcreteStage4OccupiedBelt.BeltItem
      hred ha hb hd hncol hAcard hnotFF hHall)
    {v : OrientedVertex (B (P := P))}
    (hv : v ∈ concreteEdgeVertices
      (ConcretePolarABKPRData.hspan ha hb hd hncol)
      (ConcreteStage4OccupiedBelt.beltStrictEdge
        hred ha hb hd hncol hAcard hnotFF hHall x)) :
    v.1 ∈ cyclicEdgeVertices (Finset.univ : Finset (Vertex (P := P)))
      (OnLine (B (P := P))) (vertexCoord (B (P := P)))
      (ConcreteStage4OccupiedBelt.beltCyclicEdge
        hred ha hb hd hncol hAcard hnotFF hHall x) := by
  have hm := ConcreteStage4BeltCollision.fst_mem_cyclicEdgeVertices_of_mem_concrete
    ha hb hd hncol (ConcreteStage4OccupiedBelt.pick ha hb hncol)
    (ConcreteStage4OccupiedBelt.beltStrictEdge
      hred ha hb hd hncol hAcard hnotFF hHall x) hv
  simpa only [ConcreteStage4OccupiedBelt.beltStrictEdge_lifted_base] using hm

/-- If two distinct neighbors of a genuine component cell collapse to one
projective interval, the literal far corners orient that interval forward
from the center cell. -/
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
  let vertices := (Finset.univ : Finset (Vertex (P := P)))
  let onLine := OnLine (B (P := P))
  let coord := vertexCoord (B (P := P))
  have finish_of_common
      (v u : Vertex (P := P)) (hvu : v ≠ u)
      (hvx : v ∈ cyclicEdgeVertices vertices onLine coord
        (ConcreteStage4OccupiedBelt.beltCyclicEdge
          hred ha hb hd hncol hAcard hnotFF hHall (Sum.inl x)))
      (hux : u ∈ cyclicEdgeVertices vertices onLine coord
        (ConcreteStage4OccupiedBelt.beltCyclicEdge
          hred ha hb hd hncol hAcard hnotFF hHall (Sum.inl x)))
      (hvy : v ∈ cyclicEdgeVertices vertices onLine coord
        (ConcreteStage4OccupiedBelt.beltCyclicEdge
          hred ha hb hd hncol hAcard hnotFF hHall y))
      (huy : u ∈ cyclicEdgeVertices vertices onLine coord
        (ConcreteStage4OccupiedBelt.beltCyclicEdge
          hred ha hb hd hncol hAcard hnotFF hHall y)) :
      cyclicEdgeFinish vertices onLine coord
          (ConcreteStage4OccupiedBelt.beltCyclicEdge
            hred ha hb hd hncol hAcard hnotFF hHall (Sum.inl x)) =
        cyclicEdgeStart
          (ConcreteStage4OccupiedBelt.beltCyclicEdge
            hred ha hb hd hncol hAcard hnotFF hHall y) := by
    apply ChartOrder.finish_eq_start_of_distinct_of_two_common_vertices
      vertices onLine coord (vertexCoord_injective (B (P := P)))
      (two_vertices_on_every_line (B (P := P)) ha hb hd hncol)
      _ _
    · exact (ConcreteStage4OccupiedBelt.beltCyclicEdge_line
        hred ha hb hd hncol hAcard hnotFF hHall (Sum.inl x)).trans
        (ConcreteStage4OccupiedBelt.beltCyclicEdge_line
          hred ha hb hd hncol hAcard hnotFF hHall y).symm
    · exact ConcreteStage4BeltNoncollision.adjacent_intervals_ne_of_not_endpoint_pair
        hred ha hb hd hncol hAcard hnotFF hHall hxy (by simp)
    · exact hvu
    · exact hvx
    · exact hux
    · exact hvy
    · exact huy
  rcases x with e | h
  · rcases y with (e' | h') | k <;> rcases z with (e'' | h'') | l
    · exact False.elim hxy
    · exact False.elim hxy
    · exact False.elim hxy
    · exact False.elim hxz
    · have hhne : h'.1 ≠ h''.1 := by
        intro hh
        apply hyz
        congr 3
        exact Subtype.ext hh
      obtain ⟨v, u, hvu, hvE, huE, hvH, huK⟩ :=
        ConcreteStage4BeltCollision.two_helpers_distinct_shared_vertices
          hred ha hb hd hncol LL hedge hxy hxz hhne
      have hvu' : v.1 ≠ u.1 := by
        intro hvu'
        apply hvu
        apply ConcreteStage4BeltCollision.fst_injective_on_concreteEdgeVertices
          ha hb hd hncol
          (ConcreteStage4OccupiedBelt.beltStrictEdge
            hred ha hb hd hncol hAcard hnotFF hHall
            (Sum.inl (Sum.inl e))) hvE huE hvu'
      apply finish_of_common v.1 u.1 hvu'
      · exact fst_mem_beltCyclicEdge_of_mem
          hred ha hb hd hncol hAcard hnotFF hHall _ hvE
      · exact fst_mem_beltCyclicEdge_of_mem
          hred ha hb hd hncol hAcard hnotFF hHall _ huE
      · exact fst_mem_beltCyclicEdge_of_mem
          hred ha hb hd hncol hAcard hnotFF hHall _ hvH
      · rw [heq]
        exact fst_mem_beltCyclicEdge_of_mem
          hred ha hb hd hncol hAcard hnotFF hHall _ huK
    · exact (ConcreteStage4BeltNoncollision.endpointEdge_ne_componentCell
        hred ha hb hd hncol hAcard hnotFF hHall l (Sum.inr h')) heq.symm |>.elim
    · exact False.elim hxz
    · exact (ConcreteStage4BeltNoncollision.endpointEdge_ne_componentCell
        hred ha hb hd hncol hAcard hnotFF hHall k (Sum.inr h'')) heq |>.elim
    · exfalso
      apply hnot
      exact ⟨k, l, rfl, rfl⟩
  · rcases y with (e | h') | k <;> rcases z with (e' | h'') | l
    · have hene : e.1 ≠ e'.1 := by
        intro he
        apply hyz
        congr 3
        exact Subtype.ext he
      obtain ⟨v, u, hvu, hvE, huE, hvH, huH⟩ :=
        ConcreteStage4BeltCollisionHelper.two_evils_distinct_shared_vertices
          hred ha hb hd hncol LL hedge hxy hxz hene
      have hvu' : v.1 ≠ u.1 := by
        intro hvu'
        apply hvu
        apply ConcreteStage4BeltCollision.fst_injective_on_concreteEdgeVertices
          ha hb hd hncol
          (ConcreteStage4OccupiedBelt.beltStrictEdge
            hred ha hb hd hncol hAcard hnotFF hHall
            (Sum.inl (Sum.inr h))) hvH huH hvu'
      apply finish_of_common v.1 u.1 hvu'
      · exact fst_mem_beltCyclicEdge_of_mem
          hred ha hb hd hncol hAcard hnotFF hHall _ hvH
      · exact fst_mem_beltCyclicEdge_of_mem
          hred ha hb hd hncol hAcard hnotFF hHall _ huH
      · exact fst_mem_beltCyclicEdge_of_mem
          hred ha hb hd hncol hAcard hnotFF hHall _ hvE
      · rw [heq]
        exact fst_mem_beltCyclicEdge_of_mem
          hred ha hb hd hncol hAcard hnotFF hHall _ huE
    · exact False.elim hxz
    · exact False.elim hxz
    · exact False.elim hxy
    · exact False.elim hxy
    · exact False.elim hxy
    · exact False.elim hxy
    · exact False.elim hxy
    · exact False.elim hxy

/-- The augmented deficient component exhausts every cyclic interval on
its selected opposite line. -/
theorem occupiedStarts_eq_univ
    (hHall : ¬ (G hred ha hb hd hncol hAcard hnotFF).NoEvilEvilPath) :
    ConcreteStage4OccupiedBelt.occupiedStarts
      hred ha hb hd hncol hAcard hnotFF hHall = Finset.univ := by
  apply ConcreteStage4EndpointBeltClosure.occupiedStarts_eq_univ_of_local_noncollision
    hred ha hb hd hncol hAcard hnotFF hHall
  · intro x y hxy hnot
    exact ConcreteStage4BeltNoncollision.adjacent_intervals_ne_of_not_endpoint_pair
      hred ha hb hd hncol hAcard hnotFF hHall hxy hnot
  · apply ConcreteStage4BeltNoncollision.collision_forward_of_component
      hred ha hb hd hncol hAcard hnotFF hHall
    exact component_collision_forward
      hred ha hb hd hncol hAcard hnotFF hHall
  · intro hendpoint _hevil
    exact (ConcreteStage4EndpointIntervalSeparation.endpointCyclicEdges_ne
      hred ha hb hd hncol hAcard hnotFF hHall) hendpoint |>.elim

end Erdos735.ConcreteStage4OccupiedBeltCoverage
