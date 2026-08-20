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

import ErdosProblems.Erdos735.DonationExtraction

/-!
# Local consequences of a bad neighbouring quadrangle

This file records the incidence consequences which do not use the exceptional
failed-Fano classification.  In particular, both endpoints of an edge facing
a bad two-diagonal quadrangle are multiplicity-two vertices, and an edge of a
donor which is also an edge of that bad quadrangle is free of red endpoints.
-/

open Classical
noncomputable section

namespace Erdos735.ABKPR.Data

universe uV uE uF

variable {Vertex : Type uV} {Edge : Type uE} {Face : Type uF}
variable [Fintype Vertex] [Fintype Edge] [Fintype Face]
variable [DecidableEq Vertex] [DecidableEq Edge] [DecidableEq Face]
variable {C : BlueCellulation Vertex Edge Face}
variable (A : ABKPR.Data C)

private theorem fin_three_two_edges_cover
    (i j k : Fin 3) (hij : i ≠ j) :
    k = i ∨ k = ABKPR.cyclicSucc (by omega : 0 < 3) i ∨
      k = j ∨ k = ABKPR.cyclicSucc (by omega : 0 < 3) j := by
  simp only [Fin.ext_iff, ABKPR.cyclicSucc]
  omega

private theorem fin_four_eq_opposite_of_nonadjacent
    (i j : Fin 4) (hij : i ≠ j)
    (hforward : j ≠ ABKPR.cyclicSucc (by omega : 0 < 4) i)
    (hbackward : i ≠ ABKPR.cyclicSucc (by omega : 0 < 4) j) :
    j = ABKPR.cyclicSucc (by omega : 0 < 4)
      (ABKPR.cyclicSucc (by omega : 0 < 4) i) := by
  fin_cases i <;> fin_cases j <;>
    simp_all [ABKPR.cyclicSucc, Fin.ext_iff]

/-- Every boundary vertex of a bad two-diagonal quadrangle is a
multiplicity-two blue vertex. -/
theorem badTwo_boundaryVertex_multiplicity_two
    {f : Face} (hf : A.IsBadTwoQuadrangle f)
    (i : Fin (C.faceDegree f)) :
    C.blueMultiplicity (A.boundaryVertex f i) = 2 := by
  have hend : A.redEndpoints f = Finset.univ :=
    A.redEndpoints_eq_univ_of_twoDiagonal hf.1
  have heq : A.redEndpoints f = A.stage1Corners f :=
    A.redEndpoints_eq_stage1Corners_of_badTwo hf
  have hi : i ∈ A.stage1Corners f := by
    rw [← heq, hend]
    exact Finset.mem_univ i
  exact (A.stage1Corner_iff f i).mp hi |>.2

/-- In a two-diagonal quadrangle, the chord through any chosen boundary
vertex ends at the opposite boundary vertex. -/
theorem badTwo_exists_chord_to_opposite
    {f : Face} (hf : A.IsBadTwoQuadrangle f)
    (i : Fin (C.faceDegree f)) :
    ∃ p ∈ A.redChords f,
      (p.1 = i ∧ p.2 = ABKPR.faceSucc C f (ABKPR.faceSucc C f i)) ∨
      (p.2 = i ∧ p.1 = ABKPR.faceSucc C f (ABKPR.faceSucc C f i)) := by
  have hend : A.redEndpoints f = Finset.univ :=
    A.redEndpoints_eq_univ_of_twoDiagonal hf.1
  have hi : i ∈ A.redEndpoints f := by
    rw [hend]
    exact Finset.mem_univ i
  obtain ⟨p, hp, hip⟩ := (A.redEndpoint_iff f i).mp hi
  have hnon := A.redChord_nonadjacent f p hp
  have hpne := A.redChord_distinct f p hp
  let cast : Fin (C.faceDegree f) → Fin 4 := Fin.cast hf.1.1
  have hcast_inj : Function.Injective cast := Fin.cast_injective hf.1.1
  have hcast_succ (q : Fin (C.faceDegree f)) :
      cast (ABKPR.faceSucc C f q) =
        ABKPR.cyclicSucc (by omega : 0 < 4) (cast q) := by
    apply Fin.ext
    simp [cast, ABKPR.faceSucc, ABKPR.cyclicSucc, hf.1.1]
  refine ⟨p, hp, ?_⟩
  rcases hip with hip | hip
  · left
    refine ⟨hip.symm, ?_⟩
    have hop := fin_four_eq_opposite_of_nonadjacent
      (cast p.1) (cast p.2)
      (fun h ↦ hpne (hcast_inj h))
      (fun h ↦ hnon.1 (hcast_inj (h.trans (hcast_succ p.1).symm)))
      (fun h ↦ hnon.2 (hcast_inj (h.trans (hcast_succ p.2).symm)))
    apply hcast_inj
    rw [hcast_succ, hcast_succ, hip]
    exact hop
  · right
    refine ⟨hip.symm, ?_⟩
    have hop := fin_four_eq_opposite_of_nonadjacent
      (cast p.2) (cast p.1)
      (fun h ↦ hpne (hcast_inj h).symm)
      (fun h ↦ hnon.2 (hcast_inj (h.trans (hcast_succ p.2).symm)))
      (fun h ↦ hnon.1 (hcast_inj (h.trans (hcast_succ p.1).symm)))
    apply hcast_inj
    rw [hcast_succ, hcast_succ, hip]
    exact hop

/-- The start endpoint of an edge whose opposite face is bad has
multiplicity two. -/
theorem badNeighbor_start_multiplicity_two
    (f : Face) (i : Fin (C.faceDegree f))
    (hbad : A.IsBadTwoQuadrangle (A.across ⟨f, i⟩).1) :
    C.blueMultiplicity (A.boundaryVertex f i) = 2 := by
  let d := A.across ⟨f, i⟩
  have hedge : A.boundaryEdge f i = A.boundaryEdge d.1 d.2 :=
    A.across_sameEdge ⟨f, i⟩
  have hvertices := congrArg C.edgeVertices hedge
  rw [A.boundaryEdge_vertices f i,
    A.boundaryEdge_vertices d.1 d.2] at hvertices
  have hmem : A.boundaryVertex f i ∈
      ({A.boundaryVertex d.1 d.2,
        A.boundaryVertex d.1 (ABKPR.faceSucc C d.1 d.2)} : Finset Vertex) := by
    rw [← hvertices]
    simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h | h
  · rw [h]
    exact A.badTwo_boundaryVertex_multiplicity_two hbad d.2
  · rw [h]
    exact A.badTwo_boundaryVertex_multiplicity_two hbad
      (ABKPR.faceSucc C d.1 d.2)

/-- The finish endpoint of an edge whose opposite face is bad has
multiplicity two. -/
theorem badNeighbor_finish_multiplicity_two
    (f : Face) (i : Fin (C.faceDegree f))
    (hbad : A.IsBadTwoQuadrangle (A.across ⟨f, i⟩).1) :
    C.blueMultiplicity
      (A.boundaryVertex f (ABKPR.faceSucc C f i)) = 2 := by
  let d := A.across ⟨f, i⟩
  have hedge : A.boundaryEdge f i = A.boundaryEdge d.1 d.2 :=
    A.across_sameEdge ⟨f, i⟩
  have hvertices := congrArg C.edgeVertices hedge
  rw [A.boundaryEdge_vertices f i,
    A.boundaryEdge_vertices d.1 d.2] at hvertices
  have hmem : A.boundaryVertex f (ABKPR.faceSucc C f i) ∈
      ({A.boundaryVertex d.1 d.2,
        A.boundaryVertex d.1 (ABKPR.faceSucc C d.1 d.2)} : Finset Vertex) := by
    rw [← hvertices]
    simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h | h
  · rw [h]
    exact A.badTwo_boundaryVertex_multiplicity_two hbad d.2
  · rw [h]
    exact A.badTwo_boundaryVertex_multiplicity_two hbad
      (ABKPR.faceSucc C d.1 d.2)

/-- On a triangular face, two distinct bad-neighbour edges cover all three
boundary vertices.  Consequently every boundary vertex is double. -/
theorem triangle_all_boundary_multiplicity_two_of_two_bad
    (t : Face) (ht : C.faceDegree t = 3)
    (i j : Fin (C.faceDegree t)) (hij : i ≠ j)
    (hi : i ∈ A.badNeighborIndices t)
    (hj : j ∈ A.badNeighborIndices t)
    (k : Fin (C.faceDegree t)) :
    C.blueMultiplicity (A.boundaryVertex t k) = 2 := by
  let cast : Fin (C.faceDegree t) → Fin 3 := Fin.cast ht
  have hcast_inj : Function.Injective cast := Fin.cast_injective ht
  have hcast_succ (q : Fin (C.faceDegree t)) :
      cast (ABKPR.faceSucc C t q) =
        ABKPR.cyclicSucc (by omega : 0 < 3) (cast q) := by
    apply Fin.ext
    simp [cast, ABKPR.faceSucc, ABKPR.cyclicSucc, ht]
  have hcast_ne : cast i ≠ cast j := fun h ↦ hij (hcast_inj h)
  have hbad_i : A.IsBadTwoQuadrangle (A.across ⟨t, i⟩).1 :=
    (Finset.mem_filter.mp hi).2
  have hbad_j : A.IsBadTwoQuadrangle (A.across ⟨t, j⟩).1 :=
    (Finset.mem_filter.mp hj).2
  rcases fin_three_two_edges_cover (cast i) (cast j) (cast k) hcast_ne with
      hki | hki | hkj | hkj
  · have : k = i := hcast_inj hki
    subst k
    exact A.badNeighbor_start_multiplicity_two t i hbad_i
  · have : k = ABKPR.faceSucc C t i := by
      apply hcast_inj
      rw [hcast_succ]
      exact hki
    subst k
    exact A.badNeighbor_finish_multiplicity_two t i hbad_i
  · have : k = j := hcast_inj hkj
    subst k
    exact A.badNeighbor_start_multiplicity_two t j hbad_j
  · have : k = ABKPR.faceSucc C t j := by
      apply hcast_inj
      rw [hcast_succ]
      exact hkj
    subst k
    exact A.badNeighbor_finish_multiplicity_two t j hbad_j

/-- Two faces other than `f` which contain the boundary edge indexed by
`i` are equal.  This is the exact uniqueness consequence of the fact that
every cellulation edge has two incident faces. -/
theorem face_eq_of_boundaryEdge_eq_of_ne
    {f g h : Face} {i : Fin (C.faceDegree f)}
    {j : Fin (C.faceDegree g)} {k : Fin (C.faceDegree h)}
    (hgj : A.boundaryEdge f i = A.boundaryEdge g j)
    (hhk : A.boundaryEdge f i = A.boundaryEdge h k)
    (hgf : g ≠ f) (hhf : h ≠ f) : g = h := by
  let e := A.boundaryEdge f i
  have hfmem : f ∈ C.edgeFaces e :=
    (C.faceEdge_iff f e).mp (by
      exact A.boundaryEdge_mem f i)
  have hgmem : g ∈ C.edgeFaces e :=
    (C.faceEdge_iff g e).mp (by
      change A.boundaryEdge f i ∈ C.faceBoundary g
      rw [hgj]
      exact A.boundaryEdge_mem g j)
  have hhmem : h ∈ C.edgeFaces e :=
    (C.faceEdge_iff h e).mp (by
      change A.boundaryEdge f i ∈ C.faceBoundary h
      rw [hhk]
      exact A.boundaryEdge_mem h k)
  by_contra hgh
  have hthree : ({f, g, h} : Finset Face).card = 3 := by
    rw [Finset.card_eq_three]
    exact ⟨f, g, h, fun hfg ↦ hgf hfg.symm, hhf.symm, hgh, rfl⟩
  have hsub : ({f, g, h} : Finset Face) ⊆ C.edgeFaces e := by
    intro q hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl
    · exact hfmem
    · exact hgmem
    · exact hhmem
  have hc := Finset.card_le_card hsub
  rw [hthree, C.edgeFaces_card e] at hc
  omega

/-- If a boundary edge of `f` is also a boundary edge of another face `d`,
then, provided `d ≠ f`, the across face at that edge is exactly `d`. -/
theorem across_face_eq_of_boundaryEdge_eq
    {f d : Face} {i : Fin (C.faceDegree f)}
    {j : Fin (C.faceDegree d)}
    (hedge : A.boundaryEdge f i = A.boundaryEdge d j)
    (hdf : d ≠ f) : (A.across ⟨f, i⟩).1 = d := by
  apply A.face_eq_of_boundaryEdge_eq_of_ne
    (g := (A.across ⟨f, i⟩).1) (h := d)
    (i := i) (j := (A.across ⟨f, i⟩).2) (k := j)
  · exact A.across_sameEdge ⟨f, i⟩
  · exact hedge
  · exact A.across_otherFace ⟨f, i⟩
  · exact hdf

/-- The boundary edge selected by `DonationGeometry` is free of red chord
endpoints.  No exceptional-configuration argument is needed for this field. -/
theorem donationEdgeOfGeometry_free
    (hrest : A.EndpointRestriction) (f : Face)
    (t : A.donationRecipients f) :
    A.donationEdgeOfGeometry f t ∈ A.freeEdgeIndices f := by
  obtain ⟨it, hit, jd, hedge⟩ := A.donationEdgeOfGeometry_spec f t
  let d := (A.across ⟨t.1, it⟩).1
  have hbad : A.IsBadTwoQuadrangle d := by
    exact (Finset.mem_filter.mp hit).2
  have hdegd : C.faceDegree d = 4 := hbad.1.1
  have hdegf : 5 ≤ C.faceDegree f := A.donor_degree_five_le t.2
  have hdf : d ≠ f := by
    intro h
    have hdegrees := congrArg C.faceDegree h
    omega
  have hacross : (A.across ⟨f, A.donationEdgeOfGeometry f t⟩).1 = d :=
    A.across_face_eq_of_boundaryEdge_eq hedge hdf
  have hbadAcross : A.IsBadTwoQuadrangle
      (A.across ⟨f, A.donationEdgeOfGeometry f t⟩).1 := by
    rwa [hacross]
  have hn := hrest f (A.donationEdgeOfGeometry f t) hbadAcross
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hn⟩

end Erdos735.ABKPR.Data
