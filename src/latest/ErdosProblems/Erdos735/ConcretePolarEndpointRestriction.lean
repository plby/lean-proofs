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

import ErdosProblems.Erdos735.ConcretePolarABKPRData
import ErdosProblems.Erdos735.PolarBoundaryAcrossEndpoints
import ErdosProblems.Erdos735.RedSectorGeometry

/-!
# Endpoint restriction for the concrete polar ABKPR data

This file transports the projective adjacent-sector exclusion to the literal
polar boundary used by `ConcretePolarABKPRData.concreteData`.
-/

open Classical
noncomputable section

namespace Erdos735.ConcretePolarEndpointRestriction

open ProjectiveArrangement ProjectiveBoundaryExtraction SignVector ChartOrder
open SignVector.PolarBoundaryAcross SignVector.PolarBoundaryAcrossEndpoints
open ConcretePolarOrientedVertex ConcretePolarEdgeVertices ConcretePolarABKPRData
open RedBlueDualIncidence

abbrev Point := ProjectiveArrangement.Point

variable {P : Finset Point} {w : Point → ℝ} {c : ℝ}
variable (hred : IsReducedMagic P w c)
variable {a b d : Point}
variable (ha : a ∈ nonordinaryPoints P) (hb : b ∈ nonordinaryPoints P)
variable (hd : d ∈ nonordinaryPoints P)
variable (hncol : ¬ ProjectiveDuality.Collinear3 a b d)
variable [Nonempty (ProjectiveBoundaryExtraction.Line (nonordinaryPoints P))]

private abbrev n (P : Finset Point) := normals (nonordinaryPoints P)

private abbrev hs : Submodule.span ℝ (Set.range (n P)) = ⊤ :=
  ConcretePolarABKPRData.hspan ha hb hd hncol

/-- If the opposite polar face has a red chord through every corner, neither
endpoint of the crossed edge is a red endpoint of the original face. -/
theorem polar_endpoint_not_red_of_across_all_red
    (f : StrictFace (n P)) (i q : BoundaryIndex (n P) f)
    (hq : q = i ∨ q = Erdos957.cyclicSucc i)
    (hall : PolarRedChordExtraction.redEndpoints hred (hs ha hb hd hncol)
        (PolarBoundaryAcross.across (n P) (normals_ne_zero (nonordinaryPoints P))
          normal_cross (hs ha hb hd hncol) ⟨f, i⟩).1 = Finset.univ) :
    q ∉ PolarRedChordExtraction.redEndpoints hred (hs ha hb hd hncol) f := by
  intro hqred
  obtain ⟨r, hrA, hrface, hrinc⟩ :=
    (ConcreteBadReceiver.mem_polarRedEndpoints_iff_exists_feasible_incident
      hred (hs ha hb hd hncol) f q).mp hqred
  let dart : PolarBoundaryAcross.IndexedDart (n P) := ⟨f, i⟩
  let g : StrictFace (n P) :=
    (PolarBoundaryAcross.across (n P) (normals_ne_zero (nonordinaryPoints P))
      normal_cross (hs ha hb hd hncol) dart).1
  let j : BoundaryIndex (n P) g :=
    (PolarBoundaryAcross.across (n P) (normals_ne_zero (nonordinaryPoints P))
      normal_cross (hs ha hb hd hncol) dart).2
  have hqAcross :
      boundaryVertex (n P) normal_cross (hs ha hb hd hncol) f q =
          boundaryVertex (n P) normal_cross (hs ha hb hd hncol) g j ∨
        boundaryVertex (n P) normal_cross (hs ha hb hd hncol) f q =
          boundaryVertex (n P) normal_cross (hs ha hb hd hncol) g
            (Erdos957.cyclicSucc j) := by
    rcases hq with rfl | rfl
    · exact boundaryVertex_start_is_across_endpoint (n P)
        (normals_ne_zero (nonordinaryPoints P)) normal_cross
        (hs ha hb hd hncol) dart
    · exact boundaryVertex_finish_is_across_endpoint (n P)
        (normals_ne_zero (nonordinaryPoints P)) normal_cross
        (hs ha hb hd hncol) dart
  obtain ⟨k, hkproj⟩ : ∃ k : BoundaryIndex (n P) g,
      boundaryVertex (n P) normal_cross (hs ha hb hd hncol) g k =
        boundaryVertex (n P) normal_cross (hs ha hb hd hncol) f q := by
    rcases hqAcross with h | h
    · exact ⟨j, h.symm⟩
    · exact ⟨Erdos957.cyclicSucc j, h.symm⟩
  have hkred : k ∈ PolarRedChordExtraction.redEndpoints hred
      (hs ha hb hd hncol) g := by
    rw [hall]
    exact Finset.mem_univ k
  obtain ⟨r', hr'A, hr'g, hr'inc⟩ :=
    (ConcreteBadReceiver.mem_polarRedEndpoints_iff_exists_feasible_incident
      hred (hs ha hb hd hncol) g k).mp hkred
  have hrr' : r = r' := by
    by_contra hne
    let v : ProjectiveBoundaryExtraction.Vertex (nonordinaryPoints P) :=
      ⟨boundaryVertex (n P) normal_cross (hs ha hb hd hncol) f q,
        boundaryVertex_mem_projectiveVertices (hs ha hb hd hncol) f q⟩
    exact RedChordIncidence.no_common_blueVertex_of_distinct_red hred
      hrA hr'A hne v hrinc (by simpa [v, hkproj] using hr'inc)
  subst r'
  let e : StrictEdge (n P) :=
    PolarBoundaryAcross.boundaryEdge (n P) normal_cross (hs ha hb hd hncol) f i
  let side : Bool := f.1 e.1.1
  have hface : f = edgeFace (n P) (normals_ne_zero (nonordinaryPoints P)) e side :=
    PolarBoundaryAcross.face_eq_edgeFace_of_mem (n P)
      (normals_ne_zero (nonordinaryPoints P)) f e
      (PolarBoundaryAcross.boundaryEdge_mem (n P) normal_cross
        (hs ha hb hd hncol) f i)
  have hg : g = edgeFace (n P) (normals_ne_zero (nonordinaryPoints P)) e (!side) := by
    exact PolarBoundaryAcross.across_face_eq_edgeFace_flip (n P)
      (normals_ne_zero (nonordinaryPoints P)) normal_cross
      (hs ha hb hd hncol) dart
  have hrside : RestrictedRealizable (n P) (normalVec r)
      (edgeFace (n P) (normals_ne_zero (nonordinaryPoints P)) e side).1 := by
    rw [← hface]
    exact hrface
  have hropp : RestrictedRealizable (n P) (normalVec r)
      (edgeFace (n P) (normals_ne_zero (nonordinaryPoints P)) e (!side)).1 := by
    rw [← hg]
    exact hr'g
  have howner : Incident
      (boundaryVertex (n P) normal_cross (hs ha hb hd hncol) f q) e.1.1.1 := by
    rcases hq with rfl | rfl
    · exact PolarBoundaryAcross.boundaryVertex_on_edge_start (n P) normal_cross
        (hs ha hb hd hncol) f q
    · exact PolarBoundaryAcross.boundaryVertex_on_edge_finish (n P) normal_cross
        (hs ha hb hd hncol) f i
  let v : ProjectiveBoundaryExtraction.Vertex (nonordinaryPoints P) :=
    ⟨boundaryVertex (n P) normal_cross (hs ha hb hd hncol) f q,
      boundaryVertex_mem_projectiveVertices (hs ha hb hd hncol) f q⟩
  exact RedBlueDualIncidence.not_redChord_both_edgeFaces_at_projective_endpoint
    (nonordinaryPoints P) e v r side howner hrinc hrside hropp

/-- Literal polar endpoint restriction for one edge. -/
theorem polar_endpointRestriction_of_across_all_red
    (f : StrictFace (n P)) (i : BoundaryIndex (n P) f)
    (hall : PolarRedChordExtraction.redEndpoints hred (hs ha hb hd hncol)
        (PolarBoundaryAcross.across (n P) (normals_ne_zero (nonordinaryPoints P))
          normal_cross (hs ha hb hd hncol) ⟨f, i⟩).1 = Finset.univ) :
    i ∉ PolarRedChordExtraction.redEndpoints hred (hs ha hb hd hncol) f ∧
      Erdos957.cyclicSucc i ∉
        PolarRedChordExtraction.redEndpoints hred (hs ha hb hd hncol) f := by
  exact ⟨polar_endpoint_not_red_of_across_all_red hred ha hb hd hncol f i i
      (Or.inl rfl) hall,
    polar_endpoint_not_red_of_across_all_red hred ha hb hd hncol f i
      (Erdos957.cyclicSucc i) (Or.inr rfl) hall⟩

/-- Endpoint restriction for the reindexed concrete ABKPR data. -/
theorem toData_endpointRestriction
    (vertex_degree :
      ∀ v : OrientedVertex (nonordinaryPoints P),
        (concreteVertexEdges (hs ha hb hd hncol) v).card =
          2 * lineMultiplicity (OnLine (nonordinaryPoints P)) v.1) :
    (ConcretePolarABKPRData.toData hred (vertex_degree := vertex_degree)
      ha hb hd hncol).EndpointRestriction := by
  let C := ConcretePolarABKPRData.C (vertex_degree := vertex_degree) ha hb hd hncol
  let D := ConcretePolarABKPRData.toData hred (vertex_degree := vertex_degree)
    ha hb hd hncol
  intro f i hbad
  let qi : BoundaryIndex (n P) f :=
    ConcretePolarABKPRData.indexEquiv (vertex_degree := vertex_degree)
      ha hb hd hncol f i
  let pd : PolarBoundaryAcross.IndexedDart (n P) := ⟨f, qi⟩
  let g : StrictFace (n P) :=
    (PolarBoundaryAcross.across (n P) (normals_ne_zero (nonordinaryPoints P))
      normal_cross (hs ha hb hd hncol) pd).1
  have hallD : D.redEndpoints (D.across ⟨f, i⟩).1 = Finset.univ :=
    D.redEndpoints_eq_univ_of_twoDiagonal hbad.1
  have hface : (D.across ⟨f, i⟩).1 = g := by
    rfl
  have hallDg : D.redEndpoints g = Finset.univ := by
    rw [← hface]
    exact hallD
  have hallPolar : PolarRedChordExtraction.redEndpoints hred
      (hs ha hb hd hncol) g = Finset.univ := by
    apply Finset.eq_univ_iff_forall.mpr
    intro k
    let j : Fin (C.faceDegree g) :=
      (ConcretePolarABKPRData.indexEquiv (vertex_degree := vertex_degree)
        ha hb hd hncol g).symm k
    have hj : j ∈ D.redEndpoints g := by
      rw [hallDg]
      exact Finset.mem_univ j
    have hp := (ConcretePolarABKPRData.redEndpoint_reindex_iff hred
      (vertex_degree := vertex_degree) ha hb hd hncol g j).mp hj
    simpa [j] using hp
  have hres := polar_endpointRestriction_of_across_all_red hred ha hb hd hncol
    f qi (by simpa [pd, g] using hallPolar)
  constructor
  · intro hi
    apply hres.1
    exact (ConcretePolarABKPRData.redEndpoint_reindex_iff hred
      (vertex_degree := vertex_degree) ha hb hd hncol f i).mp hi
  · intro hi
    apply hres.2
    have hp := (ConcretePolarABKPRData.redEndpoint_reindex_iff hred
      (vertex_degree := vertex_degree) ha hb hd hncol f (ABKPR.faceSucc C f i)).mp hi
    rwa [ConcretePolarABKPRData.indexEquiv_succ
      (vertex_degree := vertex_degree) ha hb hd hncol f i] at hp

/-- Unconditional endpoint restriction for `concreteData`. -/
theorem concreteData_endpointRestriction :
    (ConcretePolarABKPRData.concreteData hred ha hb hd hncol).EndpointRestriction := by
  exact toData_endpointRestriction hred ha hb hd hncol
    (ConcretePolarVertexDegree.concreteVertexEdges_card_eq
      (nonordinaryPoints P) ha hb hd hncol)

end Erdos735.ConcretePolarEndpointRestriction
