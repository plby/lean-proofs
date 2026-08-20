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

import ErdosProblems.Erdos735.ConcreteStage4OccupiedBelt
import ErdosProblems.Erdos735.ConcreteStage4ContinuationLocal
import ErdosProblems.Erdos735.ConcreteStage4HelperOpposite

/-!
# Projective-slot classification for Stage-4 component cells

Every bad or helping quadrangle in the canonical deficient component
contributes the projective interval carried by its opposite boundary edge.
Both face orbits above that interval are nontriangular: one orbit contains
the quadrangle itself and the other contains the checked across-opposite
face.  This file packages that local fact in the exact lifted-belt form
needed by the global exhaustion argument.
-/

open Classical
noncomputable section

namespace Erdos735.ConcreteStage4BeltClassification

open ProjectiveArrangement ProjectiveBoundaryExtraction
open ChartOrder SignVector SignVectorArrangement
open SignVector.ProjectiveEdgeEndpointEquiv

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

variable (hAcard : 3 ≤ (ordinaryPoints P).card)
variable (hnotFF : ¬ IsFailedFano P)

private abbrev L := ConcreteStage4FlankComplete.flankSystem
  hred ha hb hd hncol hAcard hnotFF
private abbrev G := (L hred ha hb hd hncol hAcard hnotFF).toHelpingGraph
private abbrev component
    (hHall : ¬ (G hred ha hb hd hncol hAcard hnotFF).NoEvilEvilPath) :=
  (G hred ha hb hd hncol hAcard hnotFF).deficientPathComponent hHall

private theorem boundaryEdge_incident
    (q : StrictFace (normals (B (P := P))))
    (i : Fin ((C ha hb hd hncol).faceDegree q)) :
    FaceEdgeIncident (normals (B (P := P))) q
      ((D hred ha hb hd hncol).boundaryEdge q i) := by
  rw [← mem_faceEdges_iff]
  rw [← (ConcretePolarCellulation.boundaryExtraction
    (B (P := P)) ha hb hd hncol).faceBoundary_toFinset]
  exact List.mem_toFinset.mpr
    ((D hred ha hb hd hncol).boundaryEdge_mem q i)

private theorem strictDegree_ne_three_of_faceDegree_eq_four
    (q : StrictFace (normals (B (P := P))))
    (hq : (C ha hb hd hncol).faceDegree q = 4) :
    strictFaceDegree (normals (B (P := P))) q ≠ 3 := by
  intro hthree
  rw [← ABKPR.Data.boundaryExtraction_faceDegree_eq_strictFaceDegree
    (B := ConcretePolarCellulation.boundaryExtraction
      (B (P := P)) ha hb hd hncol)] at hthree
  have h43 : (4 : ℕ) = 3 := hq.symm.trans hthree
  norm_num at h43

private theorem strictDegree_ne_three_of_faceDegree_ne_three
    (q : StrictFace (normals (B (P := P))))
    (hq : (C ha hb hd hncol).faceDegree q ≠ 3) :
    strictFaceDegree (normals (B (P := P))) q ≠ 3 := by
  rw [← ABKPR.Data.boundaryExtraction_faceDegree_eq_strictFaceDegree
    (B := ConcretePolarCellulation.boundaryExtraction
      (B (P := P)) ha hb hd hncol)]
  exact hq

/-- The selected opposite-line boundary edge of an endpoint continuation
triangle is genuinely one of that triangle's strict boundary edges. -/
theorem endpointStrictEdge_incident
    (hHall : ¬ (G hred ha hb hd hncol hAcard hnotFF).NoEvilEvilPath)
    (k : Fin 2) :
    FaceEdgeIncident (normals (B (P := P)))
      (ConcreteStage4ContinuationEndpoints.endpointTriangle
        hred ha hb hd hncol hAcard hnotFF hHall k)
      (ConcreteStage4OccupiedBelt.endpointStrictEdge
        hred ha hb hd hncol hAcard hnotFF hHall k) := by
  let evil := (component hred ha hb hd hncol hAcard hnotFF hHall).endpoint k
  let j := ConcreteStage4ContinuationEndpoints.endpointIndex
    hred ha hb hd hncol hAcard hnotFF hHall k
  let flank := (D hred ha hb hd hncol).across
    ⟨((D hred ha hb hd hncol).across
      ((D hred ha hb hd hncol).evilDart evil)).1, j⟩
  let u := ConcreteStage4BeltStep.triangleFlankOppositeIndex
    hred ha hb hd hncol (L hred ha hb hd hncol hAcard hnotFF)
    (ConcreteStage4FlankComplete.flankSystem_edgeLine
      hred ha hb hd hncol hAcard hnotFF)
    evil j
    (ConcreteStage4ContinuationEndpoints.endpointIndex_adjacent
      hred ha hb hd hncol hAcard hnotFF hHall k)
    (ConcreteStage4ContinuationEndpoints.endpointTriangle_faceDegree_three
      hred ha hb hd hncol hAcard hnotFF hHall k)
  change FaceEdgeIncident (normals (B (P := P))) flank.1
    ((D hred ha hb hd hncol).boundaryEdge flank.1 u)
  exact boundaryEdge_incident hred ha hb hd hncol flank.1 u

/-- Endpoint continuations are triangular also in the sign-vector
`strictFaceDegree` convention used by the projective belt. -/
theorem endpointTriangle_strictFaceDegree_three
    (hHall : ¬ (G hred ha hb hd hncol hAcard hnotFF).NoEvilEvilPath)
    (k : Fin 2) :
    strictFaceDegree (normals (B (P := P)))
      (ConcreteStage4ContinuationEndpoints.endpointTriangle
        hred ha hb hd hncol hAcard hnotFF hHall k) = 3 := by
  rw [← ABKPR.Data.boundaryExtraction_faceDegree_eq_strictFaceDegree
    (B := ConcretePolarCellulation.boundaryExtraction
      (B (P := P)) ha hb hd hncol)]
  exact ConcreteStage4ContinuationEndpoints.endpointTriangle_faceDegree_three
    hred ha hb hd hncol hAcard hnotFF hHall k

/-- No triangular strict face can be carried by either spherical lift of
the projective interval belonging to a component bad/helping cell. -/
theorem componentCell_projective_slot_not_triangle
    (hHall : ¬ (G hred ha hb hd hncol hAcard hnotFF).NoEvilEvilPath)
    (x : ConcreteStage4OccupiedBelt.ComponentCell
      hred ha hb hd hncol hAcard hnotFF hHall)
    (e' : StrictEdge (normals (B (P := P))))
    (f : StrictFace (normals (B (P := P))))
    (hbase :
      (strictEdgeLiftedCyclicEquiv (B (P := P)) ha hb hd hncol
        (ConcreteStage4OccupiedBelt.pick ha hb hncol) e').1 =
      ConcreteStage4OccupiedBelt.cellCyclicEdge
        hred ha hb hd hncol hAcard hnotFF hHall x)
    (hf : FaceEdgeIncident (normals (B (P := P))) f e') :
    strictFaceDegree (normals (B (P := P))) f ≠ 3 := by
  let DD := D hred ha hb hd hncol
  let edge := ConcreteStage4OccupiedBelt.cellStrictEdge
    hred ha hb hd hncol hAcard hnotFF hHall x
  have hbase' :
      (strictEdgeLiftedCyclicEquiv (B (P := P)) ha hb hd hncol
        (ConcreteStage4OccupiedBelt.pick ha hb hncol) edge).1 =
      (strictEdgeLiftedCyclicEquiv (B (P := P)) ha hb hd hncol
        (ConcreteStage4OccupiedBelt.pick ha hb hncol) e').1 := by
    rw [ConcreteStage4OccupiedBelt.cellStrictEdge_lifted_base]
    exact hbase.symm
  rcases x with e | h
  · let q := (DD.evilBadOppositeDart e.1).1
    let i := (DD.evilBadOppositeDart e.1).2
    have hqinc : FaceEdgeIncident (normals (B (P := P))) q edge := by
      exact boundaryEdge_incident hred ha hb hd hncol q i
    have hq4 : (C ha hb hd hncol).faceDegree q = 4 :=
      (DD.evilDart_across_bad e.1).1.1
    have hqnot : strictFaceDegree (normals (B (P := P))) q ≠ 3 :=
      strictDegree_ne_three_of_faceDegree_eq_four
        (ha := ha) (hb := hb) (hd := hd) (hncol := hncol) q hq4
    have hacrossC : (C ha hb hd hncol).faceDegree
        (DD.across (DD.evilBadOppositeDart e.1)).1 ≠ 3 :=
      ConcreteStage4ContinuationLocal.evilBadOpposite_across_not_triangle
        hred ha hb hd hncol hAcard hnotFF e.1
    have hacross : strictFaceDegree (normals (B (P := P)))
        (edgeFace (normals (B (P := P))) (normals_ne_zero (B (P := P)))
          edge (!(q.1 edge.1.1))) ≠ 3 := by
      have hedge : edge = DD.boundaryEdge q i := rfl
      rw [hedge]
      rw [← ConcretePolarABKPRData.concreteData_across_face_eq_edgeFace_flip
        hred ha hb hd hncol q i]
      exact strictDegree_ne_three_of_faceDegree_ne_three
        (ha := ha) (hb := hb) (hd := hd) (hncol := hncol) _ hacrossC
    intro htri
    rcases ConcretePolarLineBelt.triangular_face_eq_or_antipodal_of_liftedCyclic_base_eq
        (B (P := P)) ha hb hd hncol
        (ConcreteStage4OccupiedBelt.pick ha hb hncol)
        edge e' q f hqinc hf hbase' hacross htri with hqf | hqf
    · exact hqnot (by simpa [hqf] using htri)
    · apply hqnot
      have hant : strictFaceDegree (normals (B (P := P)))
          (antipodalStrictFace q) = 3 := by simpa [hqf] using htri
      rwa [strictFaceDegree_antipodalStrictFace] at hant
  · let q := h.1.face
    let i := (DD.helpingOppositeDart h.1).2
    have hqinc : FaceEdgeIncident (normals (B (P := P))) q edge := by
      exact boundaryEdge_incident hred ha hb hd hncol q i
    have hq4 : (C ha hb hd hncol).faceDegree q = 4 := h.1.isZeroDiagonal.1
    have hqnot : strictFaceDegree (normals (B (P := P))) q ≠ 3 :=
      strictDegree_ne_three_of_faceDegree_eq_four
        (ha := ha) (hb := hb) (hd := hd) (hncol := hncol) q hq4
    have hadj := ConcreteStage4OccupiedBelt.helperEvil_adj
      hred ha hb hd hncol hAcard hnotFF hHall h
    have hacrossC : (C ha hb hd hncol).faceDegree
        (DD.across (DD.helpingOppositeDart h.1)).1 ≠ 3 :=
      ConcreteStage4HelperOpposite.helpingOpposite_across_not_triangle
        hred ha hb hd hncol (L hred ha hb hd hncol hAcard hnotFF)
        (ConcreteStage4FlankComplete.flankSystem_edgeLine
          hred ha hb hd hncol hAcard hnotFF) hadj
    have hacross : strictFaceDegree (normals (B (P := P)))
        (edgeFace (normals (B (P := P))) (normals_ne_zero (B (P := P)))
          edge (!(q.1 edge.1.1))) ≠ 3 := by
      have hedge : edge = DD.boundaryEdge q i := rfl
      rw [hedge]
      rw [← ConcretePolarABKPRData.concreteData_across_face_eq_edgeFace_flip
        hred ha hb hd hncol q i]
      exact strictDegree_ne_three_of_faceDegree_ne_three
        (ha := ha) (hb := hb) (hd := hd) (hncol := hncol) _ hacrossC
    intro htri
    rcases ConcretePolarLineBelt.triangular_face_eq_or_antipodal_of_liftedCyclic_base_eq
        (B (P := P)) ha hb hd hncol
        (ConcreteStage4OccupiedBelt.pick ha hb hncol)
        edge e' q f hqinc hf hbase' hacross htri with hqf | hqf
    · exact hqnot (by simpa [hqf] using htri)
    · apply hqnot
      have hant : strictFaceDegree (normals (B (P := P)))
          (antipodalStrictFace q) = 3 := by simpa [hqf] using htri
      rwa [strictFaceDegree_antipodalStrictFace] at hant

/-- Once the face across the selected opposite-line edge of an endpoint
continuation is known to be nontriangular, the whole projective interval
contains only that endpoint triangle orbit. -/
theorem endpoint_projective_slot_triangle_eq_or_antipode
    (hHall : ¬ (G hred ha hb hd hncol hAcard hnotFF).NoEvilEvilPath)
    (k : Fin 2)
    (e' : StrictEdge (normals (B (P := P))))
    (f : StrictFace (normals (B (P := P))))
    (hbase :
      (strictEdgeLiftedCyclicEquiv (B (P := P)) ha hb hd hncol
        (ConcreteStage4OccupiedBelt.pick ha hb hncol) e').1 =
      ConcreteStage4OccupiedBelt.endpointCyclicEdge
        hred ha hb hd hncol hAcard hnotFF hHall k)
    (hf : FaceEdgeIncident (normals (B (P := P))) f e')
    (hother : strictFaceDegree (normals (B (P := P)))
      (edgeFace (normals (B (P := P))) (normals_ne_zero (B (P := P)))
        (ConcreteStage4OccupiedBelt.endpointStrictEdge
          hred ha hb hd hncol hAcard hnotFF hHall k)
        (!(ConcreteStage4ContinuationEndpoints.endpointTriangle
          hred ha hb hd hncol hAcard hnotFF hHall k).1
          (ConcreteStage4OccupiedBelt.endpointStrictEdge
            hred ha hb hd hncol hAcard hnotFF hHall k).1.1)) ≠ 3)
    (htri : strictFaceDegree (normals (B (P := P))) f = 3) :
    ConcreteStage4ContinuationEndpoints.endpointTriangle
        hred ha hb hd hncol hAcard hnotFF hHall k = f ∨
      antipodalStrictFace
        (ConcreteStage4ContinuationEndpoints.endpointTriangle
          hred ha hb hd hncol hAcard hnotFF hHall k) = f := by
  let q := ConcreteStage4ContinuationEndpoints.endpointTriangle
    hred ha hb hd hncol hAcard hnotFF hHall k
  let edge := ConcreteStage4OccupiedBelt.endpointStrictEdge
    hred ha hb hd hncol hAcard hnotFF hHall k
  let evil := (component hred ha hb hd hncol hAcard hnotFF hHall).endpoint k
  let j := ConcreteStage4ContinuationEndpoints.endpointIndex
    hred ha hb hd hncol hAcard hnotFF hHall k
  let flank := (D hred ha hb hd hncol).across
    ⟨((D hred ha hb hd hncol).across
      ((D hred ha hb hd hncol).evilDart evil)).1, j⟩
  let u := ConcreteStage4BeltStep.triangleFlankOppositeIndex
    hred ha hb hd hncol (L hred ha hb hd hncol hAcard hnotFF)
    (ConcreteStage4FlankComplete.flankSystem_edgeLine
      hred ha hb hd hncol hAcard hnotFF)
    evil j
    (ConcreteStage4ContinuationEndpoints.endpointIndex_adjacent
      hred ha hb hd hncol hAcard hnotFF hHall k)
    (ConcreteStage4ContinuationEndpoints.endpointTriangle_faceDegree_three
      hred ha hb hd hncol hAcard hnotFF hHall k)
  have hq : q = flank.1 := rfl
  have hedge : edge = (D hred ha hb hd hncol).boundaryEdge flank.1 u := rfl
  have hqinc : FaceEdgeIncident (normals (B (P := P))) q edge := by
    rw [hq, hedge]
    exact boundaryEdge_incident hred ha hb hd hncol flank.1 u
  have hbase' :
      (strictEdgeLiftedCyclicEquiv (B (P := P)) ha hb hd hncol
        (ConcreteStage4OccupiedBelt.pick ha hb hncol) edge).1 =
      (strictEdgeLiftedCyclicEquiv (B (P := P)) ha hb hd hncol
        (ConcreteStage4OccupiedBelt.pick ha hb hncol) e').1 := by
    rw [ConcreteStage4OccupiedBelt.endpointStrictEdge_lifted_base]
    exact hbase.symm
  exact ConcretePolarLineBelt.triangular_face_eq_or_antipodal_of_liftedCyclic_base_eq
    (B (P := P)) ha hb hd hncol
    (ConcreteStage4OccupiedBelt.pick ha hb hncol)
    edge e' q f hqinc hf hbase' hother htri

/-- Projective continuation exhaustion once the occupied projective starts
cover the selected line and the two endpoint outside faces are excluded.
All nonendpoint slots are discharged by
`componentCell_projective_slot_not_triangle`. -/
theorem all_incident_triangles_are_endpoint_or_antipode_of_occupied
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
    ∀ f : StrictFace (normals (B (P := P))),
      LineFaceIncident (normals (B (P := P)))
          (ConcreteStage4OccupiedBelt.selectedLine
            hred ha hb hd hncol hAcard hnotFF hHall) f →
        strictFaceDegree (normals (B (P := P))) f = 3 →
          ∃ k, ConcreteStage4ContinuationEndpoints.endpointTriangle
                hred ha hb hd hncol hAcard hnotFF hHall k = f ∨
              antipodalStrictFace
                (ConcreteStage4ContinuationEndpoints.endpointTriangle
                  hred ha hb hd hncol hAcard hnotFF hHall k) = f := by
  intro f hfinc htri
  obtain ⟨e, heface, heowner⟩ := hfinc
  have hfe : FaceEdgeIncident (normals (B (P := P))) f e :=
    (mem_faceEdges_iff _ _ _).mp heface
  let base :=
    (strictEdgeLiftedCyclicEquiv (B (P := P)) ha hb hd hncol
      (ConcreteStage4OccupiedBelt.pick ha hb hncol) e).1
  have hbaseLine : cyclicEdgeLine base =
      ConcreteStage4OccupiedBelt.selectedLine
        hred ha hb hd hncol hAcard hnotFF hHall := by
    change cyclicEdgeLine
      (strictEdgeLiftedCyclicEquiv (B (P := P)) ha hb hd hncol
        (ConcreteStage4OccupiedBelt.pick ha hb hncol) e).1 = _
    rw [strictEdgeLiftedCyclicEquiv_line]
    exact heowner
  let v : {v // v ∈ verticesOn
      (Finset.univ : Finset (ProjectiveBoundaryExtraction.Vertex (B (P := P))))
      (OnLine (B (P := P)))
      (ConcreteStage4OccupiedBelt.selectedLine
        hred ha hb hd hncol hAcard hnotFF hHall)} :=
    ⟨cyclicEdgeStart base, by
      apply (mem_verticesOn _ _).2
      refine ⟨Finset.mem_univ _, ?_⟩
      have hs := cyclicEdgeStart_incident
        (Finset.univ : Finset (ProjectiveBoundaryExtraction.Vertex (B (P := P))))
        (OnLine (B (P := P))) base
      rwa [hbaseLine] at hs⟩
  have hv : v ∈ ConcreteStage4OccupiedBelt.occupiedStarts
      hred ha hb hd hncol hAcard hnotFF hHall := by
    rw [hoccupied]
    exact Finset.mem_univ v
  obtain ⟨item, -, hitemStart⟩ := Finset.mem_image.mp hv
  have hbaseItem : base = ConcreteStage4OccupiedBelt.beltCyclicEdge
      hred ha hb hd hncol hAcard hnotFF hHall item := by
    apply Sigma.subtype_ext
    · exact hbaseLine.trans
        (ConcreteStage4OccupiedBelt.beltCyclicEdge_line
          hred ha hb hd hncol hAcard hnotFF hHall item).symm
    · exact (congrArg Subtype.val hitemStart).symm
  rcases item with x | k
  · exfalso
    exact ConcreteStage4BeltClassification.componentCell_projective_slot_not_triangle
      hred ha hb hd hncol hAcard hnotFF hHall x e f hbaseItem hfe htri
  · refine ⟨k, ?_⟩
    exact endpoint_projective_slot_triangle_eq_or_antipode
      hred ha hb hd hncol hAcard hnotFF hHall k e f hbaseItem hfe
        (hendpointOther k) htri

/-- The joint endpoint-slot statement, allowing the two endpoint intervals
to coincide and their endpoint triangles to occupy the two sides of the
same projective edge. -/
def EndpointSlotsClassified
    (hHall : ¬ (G hred ha hb hd hncol hAcard hnotFF).NoEvilEvilPath) : Prop :=
  ∀ (k : Fin 2) (e : StrictEdge (normals (B (P := P))))
      (f : StrictFace (normals (B (P := P)))),
    (strictEdgeLiftedCyclicEquiv (B (P := P)) ha hb hd hncol
      (ConcreteStage4OccupiedBelt.pick ha hb hncol) e).1 =
        ConcreteStage4OccupiedBelt.endpointCyclicEdge
          hred ha hb hd hncol hAcard hnotFF hHall k →
    FaceEdgeIncident (normals (B (P := P))) f e →
    strictFaceDegree (normals (B (P := P))) f = 3 →
      ∃ l, ConcreteStage4ContinuationEndpoints.endpointTriangle
              hred ha hb hd hncol hAcard hnotFF hHall l = f ∨
            antipodalStrictFace
              (ConcreteStage4ContinuationEndpoints.endpointTriangle
                hred ha hb hd hncol hAcard hnotFF hHall l) = f

/-- The exact case split needed for endpoint-slot classification.  When
the endpoint projective intervals differ, the opposite side at each
endpoint is nontriangular.  When they coincide, two non-antipodal endpoint
triangles already represent the two face orbits above that interval. -/
theorem endpointSlotsClassified_of_eq_or_other
    (hHall : ¬ (G hred ha hb hd hncol hAcard hnotFF).NoEvilEvilPath)
    (horbit :
      ConcreteStage4OccupiedBelt.endpointCyclicEdge
          hred ha hb hd hncol hAcard hnotFF hHall 0 =
        ConcreteStage4OccupiedBelt.endpointCyclicEdge
          hred ha hb hd hncol hAcard hnotFF hHall 1 →
      ¬ SameAntipodalFaceOrbit
        (ConcreteStage4ContinuationEndpoints.endpointTriangle
          hred ha hb hd hncol hAcard hnotFF hHall 0)
        (ConcreteStage4ContinuationEndpoints.endpointTriangle
          hred ha hb hd hncol hAcard hnotFF hHall 1))
    (hother :
      ConcreteStage4OccupiedBelt.endpointCyclicEdge
          hred ha hb hd hncol hAcard hnotFF hHall 0 ≠
        ConcreteStage4OccupiedBelt.endpointCyclicEdge
          hred ha hb hd hncol hAcard hnotFF hHall 1 →
      ∀ k : Fin 2,
        strictFaceDegree (normals (B (P := P)))
          (edgeFace (normals (B (P := P))) (normals_ne_zero (B (P := P)))
            (ConcreteStage4OccupiedBelt.endpointStrictEdge
              hred ha hb hd hncol hAcard hnotFF hHall k)
            (!(ConcreteStage4ContinuationEndpoints.endpointTriangle
              hred ha hb hd hncol hAcard hnotFF hHall k).1
              (ConcreteStage4OccupiedBelt.endpointStrictEdge
                hred ha hb hd hncol hAcard hnotFF hHall k).1.1)) ≠ 3) :
    EndpointSlotsClassified
      hred ha hb hd hncol hAcard hnotFF hHall := by
  intro k e f hbase hf htri
  let edge₀ := ConcreteStage4OccupiedBelt.endpointStrictEdge
    hred ha hb hd hncol hAcard hnotFF hHall 0
  let edge₁ := ConcreteStage4OccupiedBelt.endpointStrictEdge
    hred ha hb hd hncol hAcard hnotFF hHall 1
  let q₀ := ConcreteStage4ContinuationEndpoints.endpointTriangle
    hred ha hb hd hncol hAcard hnotFF hHall 0
  let q₁ := ConcreteStage4ContinuationEndpoints.endpointTriangle
    hred ha hb hd hncol hAcard hnotFF hHall 1
  by_cases heq : ConcreteStage4OccupiedBelt.endpointCyclicEdge
        hred ha hb hd hncol hAcard hnotFF hHall 0 =
      ConcreteStage4OccupiedBelt.endpointCyclicEdge
        hred ha hb hd hncol hAcard hnotFF hHall 1
  · have hk : ConcreteStage4OccupiedBelt.endpointCyclicEdge
          hred ha hb hd hncol hAcard hnotFF hHall k =
        ConcreteStage4OccupiedBelt.endpointCyclicEdge
          hred ha hb hd hncol hAcard hnotFF hHall 0 := by
      fin_cases k
      · rfl
      · exact heq.symm
    have hbase₁ :
        (strictEdgeLiftedCyclicEquiv (B (P := P)) ha hb hd hncol
          (ConcreteStage4OccupiedBelt.pick ha hb hncol) edge₀).1 =
        (strictEdgeLiftedCyclicEquiv (B (P := P)) ha hb hd hncol
          (ConcreteStage4OccupiedBelt.pick ha hb hncol) edge₁).1 := by
      rw [ConcreteStage4OccupiedBelt.endpointStrictEdge_lifted_base,
        ConcreteStage4OccupiedBelt.endpointStrictEdge_lifted_base]
      exact heq
    have hbase₀ :
        (strictEdgeLiftedCyclicEquiv (B (P := P)) ha hb hd hncol
          (ConcreteStage4OccupiedBelt.pick ha hb hncol) edge₀).1 =
        (strictEdgeLiftedCyclicEquiv (B (P := P)) ha hb hd hncol
          (ConcreteStage4OccupiedBelt.pick ha hb hncol) e).1 := by
      rw [ConcreteStage4OccupiedBelt.endpointStrictEdge_lifted_base]
      exact hk.symm.trans hbase.symm
    have hq₀ : FaceEdgeIncident (normals (B (P := P))) q₀ edge₀ :=
      endpointStrictEdge_incident
        hred ha hb hd hncol hAcard hnotFF hHall 0
    have hq₁ : FaceEdgeIncident (normals (B (P := P))) q₁ edge₁ :=
      endpointStrictEdge_incident
        hred ha hb hd hncol hAcard hnotFF hHall 1
    rcases ConcretePolarLineBelt.sameOrbit_endpoint_or_endpoint_of_same_projective_edge
        (B (P := P)) ha hb hd hncol
        (ConcreteStage4OccupiedBelt.pick ha hb hncol)
        edge₀ edge₁ e q₀ q₁ f hbase₁ hbase₀ hq₀ hq₁ hf (horbit heq) with h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
  · refine ⟨k, endpoint_projective_slot_triangle_eq_or_antipode
      hred ha hb hd hncol hAcard hnotFF hHall k e f hbase hf
        (hother heq k) htri⟩

/-- Belt exhaustion with the topology-correct joint endpoint condition. -/
theorem all_incident_triangles_are_endpoint_or_antipode_of_endpointSlots
    (hHall : ¬ (G hred ha hb hd hncol hAcard hnotFF).NoEvilEvilPath)
    (hoccupied : ConcreteStage4OccupiedBelt.occupiedStarts
      hred ha hb hd hncol hAcard hnotFF hHall = Finset.univ)
    (hendpoint : EndpointSlotsClassified
      hred ha hb hd hncol hAcard hnotFF hHall) :
    ∀ f : StrictFace (normals (B (P := P))),
      LineFaceIncident (normals (B (P := P)))
          (ConcreteStage4OccupiedBelt.selectedLine
            hred ha hb hd hncol hAcard hnotFF hHall) f →
        strictFaceDegree (normals (B (P := P))) f = 3 →
          ∃ k, ConcreteStage4ContinuationEndpoints.endpointTriangle
                hred ha hb hd hncol hAcard hnotFF hHall k = f ∨
              antipodalStrictFace
                (ConcreteStage4ContinuationEndpoints.endpointTriangle
                  hred ha hb hd hncol hAcard hnotFF hHall k) = f := by
  intro f hfinc htri
  obtain ⟨e, heface, heowner⟩ := hfinc
  have hfe : FaceEdgeIncident (normals (B (P := P))) f e :=
    (mem_faceEdges_iff _ _ _).mp heface
  let base :=
    (strictEdgeLiftedCyclicEquiv (B (P := P)) ha hb hd hncol
      (ConcreteStage4OccupiedBelt.pick ha hb hncol) e).1
  have hbaseLine : cyclicEdgeLine base =
      ConcreteStage4OccupiedBelt.selectedLine
        hred ha hb hd hncol hAcard hnotFF hHall := by
    change cyclicEdgeLine
      (strictEdgeLiftedCyclicEquiv (B (P := P)) ha hb hd hncol
        (ConcreteStage4OccupiedBelt.pick ha hb hncol) e).1 = _
    rw [strictEdgeLiftedCyclicEquiv_line]
    exact heowner
  let v : {v // v ∈ verticesOn
      (Finset.univ : Finset (ProjectiveBoundaryExtraction.Vertex (B (P := P))))
      (OnLine (B (P := P)))
      (ConcreteStage4OccupiedBelt.selectedLine
        hred ha hb hd hncol hAcard hnotFF hHall)} :=
    ⟨cyclicEdgeStart base, by
      apply (mem_verticesOn _ _).2
      refine ⟨Finset.mem_univ _, ?_⟩
      have hs := cyclicEdgeStart_incident
        (Finset.univ : Finset (ProjectiveBoundaryExtraction.Vertex (B (P := P))))
        (OnLine (B (P := P))) base
      rwa [hbaseLine] at hs⟩
  have hv : v ∈ ConcreteStage4OccupiedBelt.occupiedStarts
      hred ha hb hd hncol hAcard hnotFF hHall := by
    rw [hoccupied]
    exact Finset.mem_univ v
  obtain ⟨item, -, hitemStart⟩ := Finset.mem_image.mp hv
  have hbaseItem : base = ConcreteStage4OccupiedBelt.beltCyclicEdge
      hred ha hb hd hncol hAcard hnotFF hHall item := by
    apply Sigma.subtype_ext
    · exact hbaseLine.trans
        (ConcreteStage4OccupiedBelt.beltCyclicEdge_line
          hred ha hb hd hncol hAcard hnotFF hHall item).symm
    · exact (congrArg Subtype.val hitemStart).symm
  rcases item with x | k
  · exfalso
    exact componentCell_projective_slot_not_triangle
      hred ha hb hd hncol hAcard hnotFF hHall x e f hbaseItem hfe htri
  · exact hendpoint k e f hbaseItem hfe htri

end Erdos735.ConcreteStage4BeltClassification
