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

import ErdosProblems.Erdos735.ConcretePolarLocalSector
import ErdosProblems.Erdos735.ConcreteStage3Local

/-!
# Concrete Stage-3 donation obstructions

The local-sector theorem turns the shared-corner clauses in
`DonationGeometry` into cyclic adjacency on the bad quadrangle.  In
particular, a collision of two selected donation edges produces a bad
quadrangle with triangles across opposite edges, the exact local
failed-Fano certificate used in ABKPR.
-/

open Classical
noncomputable section

namespace Erdos735.ConcreteDonationPacking

open ProjectiveArrangement ProjectiveBoundaryExtraction SignVector ChartOrder
open ConcretePolarABKPRData

universe uV uE uF

variable {Vertex : Type uV} {Edge : Type uE} {Face : Type uF}
variable [Fintype Vertex] [Fintype Edge] [Fintype Face]
variable [DecidableEq Vertex] [DecidableEq Edge] [DecidableEq Face]
variable {C : BlueCellulation Vertex Edge Face}
variable (A : ABKPR.Data C)

/-- The canonical local exception: a bad two-diagonal quadrangle with
triangles across a pair of opposite boundary edges. -/
inductive OppositeTrianglesAtBadQuadrangle : Prop
  | intro (d : Face) (hbad : A.IsBadTwoQuadrangle d)
      (j₁ j₂ : Fin (C.faceDegree d))
      (htri₁ : C.faceDegree (A.across ⟨d, j₁⟩).1 = 3)
      (htri₂ : C.faceDegree (A.across ⟨d, j₂⟩).1 = 3)
      (hopposite : j₂ = ABKPR.faceSucc C d (ABKPR.faceSucc C d j₁))

abbrev Point := ProjectiveArrangement.Point

variable {P : Finset Point} {w : Point → ℝ} {c : ℝ}
variable (hred : IsReducedMagic P w c)
variable {a b d : Point}
variable (ha : a ∈ nonordinaryPoints P) (hb : b ∈ nonordinaryPoints P)
variable (hd : d ∈ nonordinaryPoints P)
variable (hncol : ¬ ProjectiveDuality.Collinear3 a b d)
variable [Nonempty (ProjectiveBoundaryExtraction.Line (nonordinaryPoints P))]

private abbrev B := nonordinaryPoints P
private abbrev PC := ConcretePolarCellulation.blueCellulation
  (B (P := P)) ha hb hd hncol
private abbrev D := ConcretePolarABKPRData.concreteData hred ha hb hd hncol

/-- Version of the reindexed local-sector lemma where the two across faces
are named explicitly. -/
theorem adjacent_bad_face_edges_of_common_corner
    {r f g : StrictFace (normals (B (P := P)))}
    (i j : Fin ((PC (P := P) ha hb hd hncol).faceDegree r)) (hij : i ≠ j)
    (hfi : ((D hred ha hb hd hncol).across ⟨r, i⟩).1 = f)
    (hgj : ((D hred ha hb hd hncol).across ⟨r, j⟩).1 = g)
    (vf : Fin ((PC (P := P) ha hb hd hncol).faceDegree f))
    (vg : Fin ((PC (P := P) ha hb hd hncol).faceDegree g))
    (hv : (D hred ha hb hd hncol).boundaryVertex f vf =
      (D hred ha hb hd hncol).boundaryVertex g vg) :
    ABKPR.faceSucc (PC (P := P) ha hb hd hncol) r i = j ∨
      ABKPR.faceSucc (PC (P := P) ha hb hd hncol) r j = i := by
  subst f
  subst g
  exact ConcretePolarABKPRData.concreteData_adjacent_edges_of_common_across_corner
    hred ha hb hd hncol r i j hij vf vg hv

/-- A collision of the canonical donation edges is exactly the
opposite-triangles exception around the common bad quadrangle. -/
theorem oppositeTriangles_of_donationEdgeCollision
    (f : StrictFace (normals (B (P := P))))
    (x y : (D hred ha hb hd hncol).donationRecipients f)
    (hxy : x ≠ y)
    (hedge : (D hred ha hb hd hncol).donationEdgeOfGeometry f x =
      (D hred ha hb hd hncol).donationEdgeOfGeometry f y) :
    OppositeTrianglesAtBadQuadrangle (D hred ha hb hd hncol) := by
  let A := D hred ha hb hd hncol
  let C₀ := PC (P := P) ha hb hd hncol
  obtain ⟨ix, hix, jx, hxedge⟩ := A.donationEdgeOfGeometry_spec f x
  obtain ⟨iy, hiy, jy, hyedge⟩ := A.donationEdgeOfGeometry_spec f y
  let dx := (A.across ⟨x.1, ix⟩).1
  let dy := (A.across ⟨y.1, iy⟩).1
  have hbadx : A.IsBadTwoQuadrangle dx := (Finset.mem_filter.mp hix).2
  have hbady : A.IsBadTwoQuadrangle dy := (Finset.mem_filter.mp hiy).2
  have hdegf : 5 ≤ C₀.faceDegree f := A.donor_degree_five_le x.2
  have hdxf : dx ≠ f := by
    intro h
    have hfour := hbadx.1.1
    change C₀.faceDegree dx = 4 at hfour
    have hfive : 5 ≤ C₀.faceDegree dx := by simpa [h] using hdegf
    omega
  have hdyf : dy ≠ f := by
    intro h
    have hfour := hbady.1.1
    change C₀.faceDegree dy = 4 at hfour
    have hfive : 5 ≤ C₀.faceDegree dy := by simpa [h] using hdegf
    omega
  have hfx : (A.across ⟨f, A.donationEdgeOfGeometry f x⟩).1 = dx :=
    A.across_face_eq_of_boundaryEdge_eq hxedge hdxf
  have hyedge' : A.boundaryEdge f (A.donationEdgeOfGeometry f x) =
      A.boundaryEdge dy jy := by
    rw [hedge]
    exact hyedge
  have hfy : (A.across ⟨f, A.donationEdgeOfGeometry f x⟩).1 = dy :=
    A.across_face_eq_of_boundaryEdge_eq hyedge' hdyf
  have hdxy : dx = dy := hfx.symm.trans hfy
  let kx := (A.across ⟨x.1, ix⟩).2
  have hdxkx : A.across ⟨dx, kx⟩ = ⟨x.1, ix⟩ := by
    exact A.across_involutive ⟨x.1, ix⟩
  have hdxjx : (A.across ⟨dx, jx⟩).1 = f := by
    exact A.across_face_eq_of_boundaryEdge_eq hxedge.symm (Ne.symm hdxf)
  have hxtri : C₀.faceDegree x.1 = 3 := (A.recipient_isBadTriangle x.2).1
  have hjxkx : jx ≠ kx := by
    intro h
    have hfaces : f = x.1 := by
      calc
        f = (A.across ⟨dx, jx⟩).1 := hdxjx.symm
        _ = (A.across ⟨dx, kx⟩).1 := by rw [h]
        _ = x.1 := congrArg Sigma.fst hdxkx
    have hdegrees := congrArg C₀.faceDegree hfaces
    omega
  obtain ⟨vtx, hvx⟩ := A.donationVertexOfGeometry_spec f x
  have hadjx : ABKPR.faceSucc C₀ dx jx = kx ∨
      ABKPR.faceSucc C₀ dx kx = jx := by
    apply adjacent_bad_face_edges_of_common_corner hred ha hb hd hncol
      jx kx hjxkx hdxjx (congrArg Sigma.fst hdxkx)
      (A.donationVertexOfGeometry f x) vtx
    exact hvx
  let ky : Fin (C₀.faceDegree dx) :=
    Fin.cast (congrArg C₀.faceDegree hdxy).symm (A.across ⟨y.1, iy⟩).2
  have hdart : (⟨dx, ky⟩ : ABKPR.FaceDart C₀) = A.across ⟨y.1, iy⟩ := by
    refine Sigma.ext_iff.mpr ⟨hdxy, ?_⟩
    dsimp [ky]
    rw [Fin.cast_eq_cast]
    exact cast_heq _ _
  have hdxky : A.across ⟨dx, ky⟩ = ⟨y.1, iy⟩ := by
    calc
      A.across ⟨dx, ky⟩ = A.across (A.across ⟨y.1, iy⟩) :=
        congrArg A.across hdart
      _ = ⟨y.1, iy⟩ := A.across_involutive ⟨y.1, iy⟩
  have hjxky : jx ≠ ky := by
    intro h
    have hfaces : f = y.1 := by
      calc
        f = (A.across ⟨dx, jx⟩).1 := hdxjx.symm
        _ = (A.across ⟨dx, ky⟩).1 := by rw [h]
        _ = y.1 := congrArg Sigma.fst hdxky
    have hytri : C₀.faceDegree y.1 = 3 := (A.recipient_isBadTriangle y.2).1
    have hdegrees := congrArg C₀.faceDegree hfaces
    omega
  obtain ⟨vty, hvy⟩ := A.donationVertexOfGeometry_spec f y
  have hadjy : ABKPR.faceSucc C₀ dx jx = ky ∨
      ABKPR.faceSucc C₀ dx ky = jx := by
    apply adjacent_bad_face_edges_of_common_corner hred ha hb hd hncol
      jx ky hjxky hdxjx (congrArg Sigma.fst hdxky)
      (A.donationVertexOfGeometry f y) vty
    exact hvy
  have hkxy : kx ≠ ky := by
    intro h
    apply hxy
    apply Subtype.ext
    calc
      x.1 = (A.across ⟨dx, kx⟩).1 := (congrArg Sigma.fst hdxkx).symm
      _ = (A.across ⟨dx, ky⟩).1 := by rw [h]
      _ = y.1 := congrArg Sigma.fst hdxky
  have hop : ky = ABKPR.faceSucc C₀ dx (ABKPR.faceSucc C₀ dx kx) := by
    apply Fin.ext
    have hfour : C₀.faceDegree dx = 4 := hbadx.1.1
    rcases hadjx with hadjx | hadjx <;>
      rcases hadjy with hadjy | hadjy
    · exact (hkxy (hadjx.symm.trans hadjy)).elim
    · have h₁ := congrArg Fin.val hadjx
      have h₂ := congrArg Fin.val hadjy
      simp [ABKPR.faceSucc, ABKPR.cyclicSucc, hfour] at h₁ h₂ ⊢
      omega
    · have h₁ := congrArg Fin.val hadjx
      have h₂ := congrArg Fin.val hadjy
      simp [ABKPR.faceSucc, ABKPR.cyclicSucc, hfour] at h₁ h₂ ⊢
      omega
    · have h₁ := congrArg Fin.val hadjx
      have h₂ := congrArg Fin.val hadjy
      simp [ABKPR.faceSucc, ABKPR.cyclicSucc, hfour] at h₁ h₂ ⊢
      omega
  apply OppositeTrianglesAtBadQuadrangle.intro dx hbadx kx ky
  · rw [congrArg Sigma.fst hdxkx]
    exact hxtri
  · rw [congrArg Sigma.fst hdxky]
    exact (A.recipient_isBadTriangle y.2).1
  · exact hop

end Erdos735.ConcreteDonationPacking
