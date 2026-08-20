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

import ErdosProblems.Erdos735.Stage3Packing

/-!
# Extracting Stage-3 donation witnesses

The definition of `DonationGeometry` already contains a boundary edge and a boundary vertex of the
donating face.  This file selects those witnesses canonically and supplies the corresponding
`DonationPacking` constructor, so the lookup maps themselves are no longer independent geometric
input.
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

def DonationEdgeProperty (f : Face) (t : A.donationRecipients f)
    (jf : Fin (C.faceDegree f)) : Prop :=
  ∃ it : Fin (C.faceDegree t.1), it ∈ A.badNeighborIndices t.1 ∧
    let d := (A.across ⟨t.1, it⟩).1
    ∃ jd : Fin (C.faceDegree d),
      A.boundaryEdge f jf = A.boundaryEdge d jd

theorem exists_donationEdgeProperty (f : Face) (t : A.donationRecipients f) :
    ∃ jf, A.DonationEdgeProperty f t jf := by
  have hgeom := (A.mem_donationRecipients_iff f t.1).mp t.2
  obtain ⟨it, hit, hedge, hvertex⟩ := hgeom.2.2
  obtain ⟨jf, jd, hjd⟩ := hedge
  exact ⟨jf, it, hit, jd, hjd⟩

/-- A boundary edge of the donating face supplied directly by the
`DonationGeometry` witness. -/
noncomputable def donationEdgeOfGeometry
    (f : Face) (t : A.donationRecipients f) : Fin (C.faceDegree f) :=
  Classical.choose (A.exists_donationEdgeProperty f t)

theorem donationEdgeOfGeometry_spec
    (f : Face) (t : A.donationRecipients f) :
    ∃ it : Fin (C.faceDegree t.1), it ∈ A.badNeighborIndices t.1 ∧
      let d := (A.across ⟨t.1, it⟩).1
      ∃ jd : Fin (C.faceDegree d),
        A.boundaryEdge f (A.donationEdgeOfGeometry f t) = A.boundaryEdge d jd := by
  exact Classical.choose_spec (A.exists_donationEdgeProperty f t)

def DonationVertexProperty (f : Face) (t : A.donationRecipients f)
    (vf : Fin (C.faceDegree f)) : Prop :=
  ∃ vt : Fin (C.faceDegree t.1),
    A.boundaryVertex f vf = A.boundaryVertex t.1 vt

theorem exists_donationVertexProperty (f : Face) (t : A.donationRecipients f) :
    ∃ vf, A.DonationVertexProperty f t vf := by
  have hgeom := (A.mem_donationRecipients_iff f t.1).mp t.2
  obtain ⟨it, hit, hedge, hvertex⟩ := hgeom.2.2
  obtain ⟨vf, vt, hvt⟩ := hvertex
  exact ⟨vf, vt, hvt⟩

/-- A boundary vertex of the donating face supplied directly by the
`DonationGeometry` witness. -/
noncomputable def donationVertexOfGeometry
    (f : Face) (t : A.donationRecipients f) : Fin (C.faceDegree f) :=
  Classical.choose (A.exists_donationVertexProperty f t)

theorem donationVertexOfGeometry_spec
    (f : Face) (t : A.donationRecipients f) :
    ∃ vt : Fin (C.faceDegree t.1),
      A.boundaryVertex f (A.donationVertexOfGeometry f t) =
        A.boundaryVertex t.1 vt := by
  exact Classical.choose_spec (A.exists_donationVertexProperty f t)

/-- The existential edge and vertex choices in `DonationGeometry` determine
the two lookup maps in `DonationPacking`.  Thus only injectivity, freeness,
and the one-bad-quadrangle local exclusion remain geometric inputs. -/
noncomputable def DonationPacking.ofDonationGeometry
    (donationEdge_injective : ∀ f,
      Function.Injective (A.donationEdgeOfGeometry f))
    (donationEdge_free : ∀ f d,
      A.donationEdgeOfGeometry f d ∈ A.freeEdgeIndices f)
    (donationVertex_injective : ∀ f,
      Function.Injective (A.donationVertexOfGeometry f))
    (no_two_bad_at_donation : ∀ f d i,
      A.donationVertexOfGeometry f d = ABKPR.faceSucc C f i →
        i ∈ A.badNeighborIndices f →
        ABKPR.faceSucc C f i ∈ A.badNeighborIndices f → False) :
    A.DonationPacking where
  donationEdge := A.donationEdgeOfGeometry
  donationEdge_injective := donationEdge_injective
  donationEdge_free := donationEdge_free
  donationVertex := A.donationVertexOfGeometry
  donationVertex_injective := donationVertex_injective
  no_two_bad_at_donation := no_two_bad_at_donation

/-- The reduced Stage-3 package with all witness maps extracted from
`DonationGeometry`. -/
noncomputable def ReducedStage3Geometry.ofDonationGeometry
    (oneBadQuadranglePerTriangle : ∀ t,
      C.faceDegree t = 3 → A.badNeighborCount t ≤ 1)
    (donationEdge_injective : ∀ f,
      Function.Injective (A.donationEdgeOfGeometry f))
    (donationEdge_free : ∀ f d,
      A.donationEdgeOfGeometry f d ∈ A.freeEdgeIndices f)
    (donationVertex_injective : ∀ f,
      Function.Injective (A.donationVertexOfGeometry f))
    (no_two_bad_at_donation : ∀ f d i,
      A.donationVertexOfGeometry f d = ABKPR.faceSucc C f i →
        i ∈ A.badNeighborIndices f →
        ABKPR.faceSucc C f i ∈ A.badNeighborIndices f → False) :
    A.ReducedStage3Geometry where
  oneBadQuadranglePerTriangle := oneBadQuadranglePerTriangle
  donationPacking := DonationPacking.ofDonationGeometry A
    donationEdge_injective donationEdge_free donationVertex_injective
    no_two_bad_at_donation

end Erdos735.ABKPR.Data
