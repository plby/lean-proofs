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

import ErdosProblems.Erdos735.BadNeighborLocal

/-!
# Exact local exceptions to Stage-3 donation packing

For the canonically extracted donation edge and donation vertex, failure of
one of the three packing assertions has a completely finite geometric
witness.  This file records those witnesses without adding any geometric
assumption:

* an edge collision gives two distinct bad triangles incident with the same
  bad two-diagonal quadrangle;
* a vertex collision gives two distinct bad triangles through one selected
  donor corner;
* failure of the local exclusion gives two consecutive bad quadrangles at a
  selected donation corner.

Consequently endpoint restriction gives either a genuine `DonationPacking`
or one of these three precise local certificates.  The subsequent
projective recognition argument may therefore work only with the local
exceptional configurations, rather than with negated injectivity statements.
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

/-- Two distinct donation-recipient triangles whose distinguished bad edges
lead to the same bad two-diagonal quadrangle.  The donor is retained in the
certificate: it is the face whose selected donation-edge collision produced
the configuration. -/
def SharedBadQuadrangleTwoTriangles : Prop :=
  ∃ (f : Face) (t u : A.donationRecipients f), t ≠ u ∧
    ∃ (it : Fin (C.faceDegree t.1)) (iu : Fin (C.faceDegree u.1)),
      it ∈ A.badNeighborIndices t.1 ∧
      iu ∈ A.badNeighborIndices u.1 ∧
      (A.across ⟨t.1, it⟩).1 = (A.across ⟨u.1, iu⟩).1

/-- Two distinct donation-recipient triangles which contain the same
selected corner of their donor. -/
def SharedDonorVertexTwoTriangles : Prop :=
  ∃ (f : Face) (t u : A.donationRecipients f), t ≠ u ∧
    ∃ (vt : Fin (C.faceDegree t.1)) (vu : Fin (C.faceDegree u.1)),
      A.boundaryVertex t.1 vt = A.boundaryVertex u.1 vu

/-- A donation corner which is between two consecutive edges facing bad
two-diagonal quadrangles.  This is exactly the forbidden local pattern in
`DonationPacking.no_two_bad_at_donation`. -/
def ConsecutiveBadAtDonationCorner : Prop :=
  ∃ (f : Face) (t : A.donationRecipients f)
      (i : Fin (C.faceDegree f)) (vt : Fin (C.faceDegree t.1)),
    A.boundaryVertex f (ABKPR.faceSucc C f i) =
        A.boundaryVertex t.1 vt ∧
      i ∈ A.badNeighborIndices f ∧
      ABKPR.faceSucc C f i ∈ A.badNeighborIndices f

theorem sharedBadQuadrangleTwoTriangles_of_edge_collision
    {f : Face} {t u : A.donationRecipients f} (htu : t ≠ u)
    (hedge : A.donationEdgeOfGeometry f t =
      A.donationEdgeOfGeometry f u) :
    A.SharedBadQuadrangleTwoTriangles := by
  obtain ⟨it, hit, jt, htEdge⟩ := A.donationEdgeOfGeometry_spec f t
  obtain ⟨iu, hiu, ju, huEdge⟩ := A.donationEdgeOfGeometry_spec f u
  let dt := (A.across ⟨t.1, it⟩).1
  let du := (A.across ⟨u.1, iu⟩).1
  have hbad_t : A.IsBadTwoQuadrangle dt := (Finset.mem_filter.mp hit).2
  have hbad_u : A.IsBadTwoQuadrangle du := (Finset.mem_filter.mp hiu).2
  have hdegf : 5 ≤ C.faceDegree f := A.donor_degree_five_le t.2
  have hdtf : dt ≠ f := by
    intro h
    have hdeg := congrArg C.faceDegree h
    have hfour := hbad_t.1.1
    omega
  have hduf : du ≠ f := by
    intro h
    have hdeg := congrArg C.faceDegree h
    have hfour := hbad_u.1.1
    omega
  have hacross_t :
      (A.across ⟨f, A.donationEdgeOfGeometry f t⟩).1 = dt :=
    A.across_face_eq_of_boundaryEdge_eq htEdge hdtf
  have huEdge' : A.boundaryEdge f (A.donationEdgeOfGeometry f t) =
      A.boundaryEdge du ju := by
    rw [hedge]
    exact huEdge
  have hacross_u :
      (A.across ⟨f, A.donationEdgeOfGeometry f t⟩).1 = du :=
    A.across_face_eq_of_boundaryEdge_eq huEdge' hduf
  refine ⟨f, t, u, htu, it, iu, hit, hiu, ?_⟩
  exact hacross_t.symm.trans hacross_u

theorem sharedBadQuadrangleTwoTriangles_of_not_edge_injective
    (h : ¬ Function.Injective (A.donationEdgeOfGeometry f)) :
    A.SharedBadQuadrangleTwoTriangles := by
  simp only [Function.Injective] at h
  push Not at h
  obtain ⟨t, u, hedge, htu⟩ := h
  exact A.sharedBadQuadrangleTwoTriangles_of_edge_collision htu hedge

theorem sharedDonorVertexTwoTriangles_of_vertex_collision
    {f : Face} {t u : A.donationRecipients f} (htu : t ≠ u)
    (hvertex : A.donationVertexOfGeometry f t =
      A.donationVertexOfGeometry f u) :
    A.SharedDonorVertexTwoTriangles := by
  obtain ⟨vt, ht⟩ := A.donationVertexOfGeometry_spec f t
  obtain ⟨vu, hu⟩ := A.donationVertexOfGeometry_spec f u
  refine ⟨f, t, u, htu, vt, vu, ?_⟩
  exact ht.symm.trans ((congrArg (A.boundaryVertex f) hvertex).trans hu)

theorem sharedDonorVertexTwoTriangles_of_not_vertex_injective
    (h : ¬ Function.Injective (A.donationVertexOfGeometry f)) :
    A.SharedDonorVertexTwoTriangles := by
  simp only [Function.Injective] at h
  push Not at h
  obtain ⟨t, u, hvertex, htu⟩ := h
  exact A.sharedDonorVertexTwoTriangles_of_vertex_collision htu hvertex

theorem consecutiveBadAtDonationCorner_of_failure
    {f : Face} {t : A.donationRecipients f}
    {i : Fin (C.faceDegree f)}
    (hcorner : A.donationVertexOfGeometry f t = ABKPR.faceSucc C f i)
    (hi : i ∈ A.badNeighborIndices f)
    (hsucc : ABKPR.faceSucc C f i ∈ A.badNeighborIndices f) :
    A.ConsecutiveBadAtDonationCorner := by
  obtain ⟨vt, ht⟩ := A.donationVertexOfGeometry_spec f t
  refine ⟨f, t, i, vt, ?_, hi, hsucc⟩
  exact (congrArg (A.boundaryVertex f) hcorner).symm.trans ht

/-- Endpoint restriction leaves exactly three explicit local ways in which
the canonical donation witnesses can fail to form a packing. -/
theorem donationPacking_or_localException
    (hrest : A.EndpointRestriction) :
    Nonempty A.DonationPacking ∨
      A.SharedBadQuadrangleTwoTriangles ∨
      A.SharedDonorVertexTwoTriangles ∨
      A.ConsecutiveBadAtDonationCorner := by
  by_cases hedge : ∀ f, Function.Injective (A.donationEdgeOfGeometry f)
  · by_cases hvertex : ∀ f, Function.Injective (A.donationVertexOfGeometry f)
    · by_cases hlocal : ∀ f d i,
        A.donationVertexOfGeometry f d = ABKPR.faceSucc C f i →
          i ∈ A.badNeighborIndices f →
          ABKPR.faceSucc C f i ∈ A.badNeighborIndices f → False
      · left
        exact ⟨DonationPacking.ofDonationGeometry A hedge
          (A.donationEdgeOfGeometry_free hrest) hvertex hlocal⟩
      · right
        right
        right
        push Not at hlocal
        obtain ⟨f, d, i, heq, hi, hs, -⟩ := hlocal
        exact A.consecutiveBadAtDonationCorner_of_failure heq hi hs
    · right
      right
      left
      push Not at hvertex
      obtain ⟨f, hf⟩ := hvertex
      exact A.sharedDonorVertexTwoTriangles_of_not_vertex_injective hf
  · right
    left
    push Not at hedge
    obtain ⟨f, hf⟩ := hedge
    exact A.sharedBadQuadrangleTwoTriangles_of_not_edge_injective hf

end Erdos735.ABKPR.Data
