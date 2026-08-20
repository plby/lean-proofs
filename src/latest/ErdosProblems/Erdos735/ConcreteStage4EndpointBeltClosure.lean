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

import ErdosProblems.Erdos735.ConcreteStage4OccupiedBelt

/-!
# Closing the two endpoint intervals of the Stage-4 belt

Each continuation triangle has one edge on the common path line and one
edge on the common opposite line.  Their intersection is unique in the
projective plane, so the two opposite-line intervals meet at that common
crossing.
-/

open Classical
noncomputable section

namespace Erdos735.ConcreteStage4EndpointBeltClosure

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
private abbrev C := ConcretePolarCellulation.blueCellulation
  (B (P := P)) ha hb hd hncol
private abbrev D := ConcretePolarABKPRData.concreteData hred ha hb hd hncol
private abbrev Line := ProjectiveBoundaryExtraction.Line (B (P := P))
private abbrev Vertex := ProjectiveBoundaryExtraction.Vertex (B (P := P))

variable (hAcard : 3 ≤ (ordinaryPoints P).card)
variable (hnotFF : ¬ IsFailedFano P)

private abbrev L := ConcreteStage4FlankComplete.flankSystem
  hred ha hb hd hncol hAcard hnotFF
private abbrev G := (L hred ha hb hd hncol hAcard hnotFF).toHelpingGraph
private abbrev component
    (hHall : ¬ (G hred ha hb hd hncol hAcard hnotFF).NoEvilEvilPath) :=
  (G hred ha hb hd hncol hAcard hnotFF).deficientPathComponent hHall

/-- The endpoint interval contains the crossing of its path owner and its
opposite owner. -/
theorem endpointCyclicEdge_has_path_crossing
    (hHall : ¬ (G hred ha hb hd hncol hAcard hnotFF).NoEvilEvilPath)
    (k : Fin 2) :
    let e := (component hred ha hb hd hncol hAcard hnotFF hHall).endpoint k
    ∃ v : Vertex (P := P),
      v ∈ cyclicEdgeVertices (Finset.univ : Finset (Vertex (P := P)))
        (OnLine (B (P := P))) (vertexCoord (B (P := P)))
        (ConcreteStage4OccupiedBelt.endpointCyclicEdge
          hred ha hb hd hncol hAcard hnotFF hHall k) ∧
      OnLine (B (P := P)) v
        ((L hred ha hb hd hncol hAcard hnotFF).edgeLine
          ((D hred ha hb hd hncol).boundaryEdge
            e.1 ((D hred ha hb hd hncol).evilIndex e))) := by
  let LL := L hred ha hb hd hncol hAcard hnotFF
  let e := (component hred ha hb hd hncol hAcard hnotFF hHall).endpoint k
  let j := ConcreteStage4ContinuationEndpoints.endpointIndex
    hred ha hb hd hncol hAcard hnotFF hHall k
  let hadj := ConcreteStage4ContinuationEndpoints.endpointIndex_adjacent
    hred ha hb hd hncol hAcard hnotFF hHall k
  let htri :=
    ConcreteStage4ContinuationEndpoints.endpointTriangle_faceDegree_three
      hred ha hb hd hncol hAcard hnotFF hHall k
  change ∃ v : Vertex (P := P),
    v ∈ cyclicEdgeVertices (Finset.univ : Finset (Vertex (P := P)))
      (OnLine (B (P := P))) (vertexCoord (B (P := P)))
      (ConcreteStage4BeltStep.triangleFlankBeltEdge
        hred ha hb hd hncol
        (ConcreteStage4OccupiedBelt.pick ha hb hncol) LL
        (ConcreteStage4FlankComplete.flankSystem_edgeLine
          hred ha hb hd hncol hAcard hnotFF)
        e j hadj htri).1.1 ∧
    OnLine (B (P := P)) v
      (LL.edgeLine ((D hred ha hb hd hncol).boundaryEdge
        e.1 ((D hred ha hb hd hncol).evilIndex e)))
  exact ConcreteStage4BeltStep.triangleFlankBeltEdge_has_path_crossing
    hred ha hb hd hncol
    (ConcreteStage4OccupiedBelt.pick ha hb hncol) LL
    (ConcreteStage4FlankComplete.flankSystem_edgeLine
      hred ha hb hd hncol hAcard hnotFF)
    e j hadj htri

private theorem onLine_of_mem_cyclicEdgeVertices
    (edge : CyclicSkeletonEdge (Finset.univ : Finset (Vertex (P := P)))
      (OnLine (B (P := P))))
    {v : Vertex (P := P)}
    (hv : v ∈ cyclicEdgeVertices (Finset.univ : Finset (Vertex (P := P)))
      (OnLine (B (P := P))) (vertexCoord (B (P := P))) edge) :
    OnLine (B (P := P)) v (cyclicEdgeLine edge) := by
  simp only [cyclicEdgeVertices, Finset.mem_insert,
    Finset.mem_singleton] at hv
  rcases hv with rfl | rfl
  · exact cyclicEdgeStart_incident
      (Finset.univ : Finset (Vertex (P := P)))
      (OnLine (B (P := P))) edge
  · exact cyclicEdgeFinish_incident
      (Finset.univ : Finset (Vertex (P := P)))
      (OnLine (B (P := P))) (vertexCoord (B (P := P))) edge

/-- The two canonical endpoint-triangle intervals share the unique
projective intersection of the common path and opposite lines. -/
theorem endpointCyclicEdges_share_crossing
    (hHall : ¬ (G hred ha hb hd hncol hAcard hnotFF).NoEvilEvilPath) :
    ∃ v : Vertex (P := P),
      v ∈ cyclicEdgeVertices (Finset.univ : Finset (Vertex (P := P)))
        (OnLine (B (P := P))) (vertexCoord (B (P := P)))
        (ConcreteStage4OccupiedBelt.endpointCyclicEdge
          hred ha hb hd hncol hAcard hnotFF hHall 0) ∧
      v ∈ cyclicEdgeVertices (Finset.univ : Finset (Vertex (P := P)))
        (OnLine (B (P := P))) (vertexCoord (B (P := P)))
        (ConcreteStage4OccupiedBelt.endpointCyclicEdge
          hred ha hb hd hncol hAcard hnotFF hHall 1) := by
  let LL := L hred ha hb hd hncol hAcard hnotFF
  let H := component hred ha hb hd hncol hAcard hnotFF hHall
  let edge0 := ConcreteStage4OccupiedBelt.endpointCyclicEdge
    hred ha hb hd hncol hAcard hnotFF hHall 0
  let edge1 := ConcreteStage4OccupiedBelt.endpointCyclicEdge
    hred ha hb hd hncol hAcard hnotFF hHall 1
  obtain ⟨v0, hv0edge, hv0path⟩ := endpointCyclicEdge_has_path_crossing
    hred ha hb hd hncol hAcard hnotFF hHall 0
  obtain ⟨v1, hv1edge, hv1path⟩ := endpointCyclicEdge_has_path_crossing
    hred ha hb hd hncol hAcard hnotFF hHall 1
  have hv0opp : OnLine (B (P := P)) v0
      (ConcreteStage4OccupiedBelt.selectedLine
        hred ha hb hd hncol hAcard hnotFF hHall) := by
    have hv := onLine_of_mem_cyclicEdgeVertices edge0 hv0edge
    rw [ConcreteStage4OccupiedBelt.endpointCyclicEdge_line
      hred ha hb hd hncol hAcard hnotFF hHall 0] at hv
    exact hv
  have hv1opp : OnLine (B (P := P)) v1
      (ConcreteStage4OccupiedBelt.selectedLine
        hred ha hb hd hncol hAcard hnotFF hHall) := by
    have hv := onLine_of_mem_cyclicEdgeVertices edge1 hv1edge
    rw [ConcreteStage4OccupiedBelt.endpointCyclicEdge_line
      hred ha hb hd hncol hAcard hnotFF hHall 1] at hv
    exact hv
  have hpath := ABKPR.Data.deficientPath_endpoints_badEdgeLine_eq
    (D hred ha hb hd hncol) LL hHall (1 : Fin 2)
  have hv1path0 : OnLine (B (P := P)) v1
      (LL.edgeLine ((D hred ha hb hd hncol).boundaryEdge
        (H.endpoint 0).1
        ((D hred ha hb hd hncol).evilIndex (H.endpoint 0)))) := by
    rw [hpath]
    exact hv1path
  have hlinesNe : ConcreteStage4OccupiedBelt.selectedLine
      hred ha hb hd hncol hAcard hnotFF hHall ≠
      LL.edgeLine ((D hred ha hb hd hncol).boundaryEdge
        (H.endpoint 0).1
        ((D hred ha hb hd hncol).evilIndex (H.endpoint 0))) := by
    exact ConcreteOppositeLineCoherence.evilOppositeLine_ne_badEdgeLine
      hred ha hb hd hncol LL
        (ConcreteStage4FlankComplete.flankSystem_edgeLine
          hred ha hb hd hncol hAcard hnotFF)
        (H.endpoint 0)
  have hpointsNe :
      (ConcreteStage4OccupiedBelt.selectedLine
        hred ha hb hd hncol hAcard hnotFF hHall).1 ≠
      (LL.edgeLine ((D hred ha hb hd hncol).boundaryEdge
        (H.endpoint 0).1
        ((D hred ha hb hd hncol).evilIndex (H.endpoint 0)))).1 := by
    intro h
    exact hlinesNe (Subtype.ext h)
  have hv01 : v0 = v1 := by
    apply Subtype.ext
    exact ProjectiveArrangement.eq_of_two_common_lines hpointsNe
      hv0opp hv0path hv1opp hv1path0
  refine ⟨v0, hv0edge, ?_⟩
  rw [hv01]
  exact hv1edge

/-- Consequently the two endpoint intervals are equal or consecutive in
one of the two cyclic orientations. -/
theorem endpointCyclicEdges_eq_or_end_start
    (hHall : ¬ (G hred ha hb hd hncol hAcard hnotFF).NoEvilEvilPath) :
    let e0 := ConcreteStage4OccupiedBelt.endpointCyclicEdge
      hred ha hb hd hncol hAcard hnotFF hHall 0
    let e1 := ConcreteStage4OccupiedBelt.endpointCyclicEdge
      hred ha hb hd hncol hAcard hnotFF hHall 1
    e0 = e1 ∨
      cyclicEdgeFinish (Finset.univ : Finset (Vertex (P := P)))
          (OnLine (B (P := P))) (vertexCoord (B (P := P))) e0 =
        cyclicEdgeStart e1 ∨
      cyclicEdgeFinish (Finset.univ : Finset (Vertex (P := P)))
          (OnLine (B (P := P))) (vertexCoord (B (P := P))) e1 =
        cyclicEdgeStart e0 := by
  let e0 := ConcreteStage4OccupiedBelt.endpointCyclicEdge
    hred ha hb hd hncol hAcard hnotFF hHall 0
  let e1 := ConcreteStage4OccupiedBelt.endpointCyclicEdge
    hred ha hb hd hncol hAcard hnotFF hHall 1
  obtain ⟨v, hv0, hv1⟩ := endpointCyclicEdges_share_crossing
    hred ha hb hd hncol hAcard hnotFF hHall
  have hline : cyclicEdgeLine e0 = cyclicEdgeLine e1 := by
    rw [ConcreteStage4OccupiedBelt.endpointCyclicEdge_line
      hred ha hb hd hncol hAcard hnotFF hHall 0,
      ConcreteStage4OccupiedBelt.endpointCyclicEdge_line
      hred ha hb hd hncol hAcard hnotFF hHall 1]
  exact ConcreteStage4BeltStep.cyclicEdges_eq_or_end_start
    (Finset.univ : Finset (Vertex (P := P)))
    (OnLine (B (P := P))) (vertexCoord (B (P := P)))
    (vertexCoord_injective (B (P := P))) e0 e1 hline v hv0 hv1

/-- The checked endpoint closing edge plus local noncollision turns the
augmented deficient component into a successor-closed set of projective
interval starts, hence exhausts the selected line. -/
theorem occupiedStarts_eq_univ_of_local_noncollision
    (hHall : ¬ (G hred ha hb hd hncol hAcard hnotFF).NoEvilEvilPath)
    (hself : ∀ {x y : ConcreteStage4OccupiedBelt.BeltItem
        hred ha hb hd hncol hAcard hnotFF hHall},
      ConcreteStage4OccupiedBelt.BeltAdjacent
          hred ha hb hd hncol hAcard hnotFF hHall x y →
      (¬ ∃ k l : Fin 2, x = Sum.inr k ∧ y = Sum.inr l) →
        ConcreteStage4OccupiedBelt.beltCyclicEdge
            hred ha hb hd hncol hAcard hnotFF hHall x ≠
          ConcreteStage4OccupiedBelt.beltCyclicEdge
            hred ha hb hd hncol hAcard hnotFF hHall y)
    (hcollision : ∀ {x y z : ConcreteStage4OccupiedBelt.BeltItem
        hred ha hb hd hncol hAcard hnotFF hHall},
      ConcreteStage4OccupiedBelt.BeltAdjacent
          hred ha hb hd hncol hAcard hnotFF hHall x y →
      ConcreteStage4OccupiedBelt.BeltAdjacent
          hred ha hb hd hncol hAcard hnotFF hHall x z → y ≠ z →
      (¬ ∃ k l : Fin 2, y = Sum.inr k ∧ z = Sum.inr l) →
      ConcreteStage4OccupiedBelt.beltCyclicEdge
          hred ha hb hd hncol hAcard hnotFF hHall y =
        ConcreteStage4OccupiedBelt.beltCyclicEdge
          hred ha hb hd hncol hAcard hnotFF hHall z →
      cyclicEdgeFinish (Finset.univ : Finset (Vertex (P := P)))
          (OnLine (B (P := P))) (vertexCoord (B (P := P)))
          (ConcreteStage4OccupiedBelt.beltCyclicEdge
            hred ha hb hd hncol hAcard hnotFF hHall x) =
        cyclicEdgeStart
          (ConcreteStage4OccupiedBelt.beltCyclicEdge
            hred ha hb hd hncol hAcard hnotFF hHall y))
    (hendpointDouble :
      ConcreteStage4OccupiedBelt.beltCyclicEdge
          hred ha hb hd hncol hAcard hnotFF hHall (Sum.inr (0 : Fin 2)) =
        ConcreteStage4OccupiedBelt.beltCyclicEdge
          hred ha hb hd hncol hAcard hnotFF hHall (Sum.inr (1 : Fin 2)) →
      ConcreteStage4OccupiedBelt.beltCyclicEdge
          hred ha hb hd hncol hAcard hnotFF hHall
          (ConcreteStage4OccupiedBelt.endpointEvilItem
            hred ha hb hd hncol hAcard hnotFF hHall 0) =
        ConcreteStage4OccupiedBelt.beltCyclicEdge
          hred ha hb hd hncol hAcard hnotFF hHall
          (ConcreteStage4OccupiedBelt.endpointEvilItem
            hred ha hb hd hncol hAcard hnotFF hHall 1) →
      cyclicEdgeFinish (Finset.univ : Finset (Vertex (P := P)))
          (OnLine (B (P := P))) (vertexCoord (B (P := P)))
          (ConcreteStage4OccupiedBelt.beltCyclicEdge
            hred ha hb hd hncol hAcard hnotFF hHall (Sum.inr (0 : Fin 2))) =
        cyclicEdgeStart
          (ConcreteStage4OccupiedBelt.beltCyclicEdge
            hred ha hb hd hncol hAcard hnotFF hHall
            (ConcreteStage4OccupiedBelt.endpointEvilItem
              hred ha hb hd hncol hAcard hnotFF hHall 0))) :
    ConcreteStage4OccupiedBelt.occupiedStarts
      hred ha hb hd hncol hAcard hnotFF hHall = Finset.univ := by
  have hend : ConcreteStage4OccupiedBelt.BeltEdgeNeighbor
      hred ha hb hd hncol hAcard hnotFF hHall
      (Sum.inr (0 : Fin 2)) (Sum.inr (1 : Fin 2)) := by
    exact endpointCyclicEdges_eq_or_end_start
      hred ha hb hd hncol hAcard hnotFF hHall
  have hfinish := ConcreteStage4OccupiedBelt.finish_covered_allow_endpoint_edge_eq
    hred ha hb hd hncol hAcard hnotFF hHall hend hself hcollision hendpointDouble
  have hclosed := ConcreteStage4OccupiedBelt.occupiedStarts_successor_closed_of_finish_covered
    hred ha hb hd hncol hAcard hnotFF hHall hfinish
  exact ConcreteStage4OccupiedBelt.occupiedStarts_eq_univ_of_successor_closed
    hred ha hb hd hncol hAcard hnotFF hHall hclosed

end Erdos735.ConcreteStage4EndpointBeltClosure
