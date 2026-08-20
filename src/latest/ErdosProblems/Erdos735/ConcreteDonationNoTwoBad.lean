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

import ErdosProblems.Erdos735.ConcreteDonationObstructionRecognition
import ErdosProblems.Erdos735.Stage4OppositeLine

/-!
# Two bad donor edges cannot meet at a donation corner

At a multiplicity-two corner there are four local polar sectors.  A
donation recipient is the sector opposite its donor.  Consequently, if
the two donor edges incident with the donated corner both lead to bad
quadrangles, then each of those quadrangles also borders the recipient.
That gives the bad recipient triangle two distinct bad neighbours,
contrary to the definition of a donation recipient.
-/

open Classical
noncomputable section

namespace Erdos735.ConcreteDonationObstructionRecognition

open ProjectiveArrangement ProjectiveBoundaryExtraction SignVector ChartOrder
open SignVector.PolarPlaneChart
open ConcretePolarABKPRData ConcretePolarOrientedVertex

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
private abbrev VD := ConcretePolarVertexDegree.concreteVertexEdges_card_eq
  (B (P := P)) ha hb hd hncol

private theorem faceSucc_ne_self
    (q : StrictFace (normals (B (P := P))))
    (k : Fin ((C (P := P) ha hb hd hncol).faceDegree q)) :
    ABKPR.faceSucc (C (P := P) ha hb hd hncol) q k ≠ k := by
  intro h
  have hval := congrArg Fin.val h
  simp only [ABKPR.faceSucc, ABKPR.cyclicSucc] at hval
  have hdeg := (C (P := P) ha hb hd hncol).faceDegree_three_le q
  change 3 ≤ (C (P := P) ha hb hd hncol).faceDegree q at hdeg
  by_cases hk : k.val + 1 < (C (P := P) ha hb hd hncol).faceDegree q
  · rw [Nat.mod_eq_of_lt hk] at hval
    omega
  · have hlast : k.val + 1 =
        (C (P := P) ha hb hd hncol).faceDegree q := by omega
    rw [hlast, Nat.mod_self] at hval
    omega

/-- If `v` is an endpoint of a quadrangular boundary edge, crossing that
edge and the other boundary edge through `v` produces two faces which
still share the corner `v`. -/
private theorem exists_other_crossing_at_quadrangle_endpoint
    (q : StrictFace (normals (B (P := P))))
    (hfour : (C (P := P) ha hb hd hncol).faceDegree q = 4)
    (k : Fin ((C (P := P) ha hb hd hncol).faceDegree q))
    (v : ConcretePolarOrientedVertex.OrientedVertex (B (P := P)))
    (hv : v ∈ (C (P := P) ha hb hd hncol).edgeVertices
      ((D hred ha hb hd hncol).boundaryEdge q k)) :
    ∃ r : Fin ((C (P := P) ha hb hd hncol).faceDegree q), r ≠ k ∧
      ∃ p : Fin ((C (P := P) ha hb hd hncol).faceDegree
          ((D hred ha hb hd hncol).across ⟨q, k⟩).1),
        ∃ s : Fin ((C (P := P) ha hb hd hncol).faceDegree
          ((D hred ha hb hd hncol).across ⟨q, r⟩).1),
          (D hred ha hb hd hncol).boundaryVertex
              ((D hred ha hb hd hncol).across ⟨q, k⟩).1 p =
            (D hred ha hb hd hncol).boundaryVertex
              ((D hred ha hb hd hncol).across ⟨q, r⟩).1 s ∧
          (D hred ha hb hd hncol).boundaryVertex
              ((D hred ha hb hd hncol).across ⟨q, k⟩).1 p = v := by
  let CC := C (P := P) ha hb hd hncol
  let A := D hred ha hb hd hncol
  rw [A.boundaryEdge_vertices] at hv
  simp only [Finset.mem_insert, Finset.mem_singleton] at hv
  obtain ⟨r, hrk, hvr⟩ : ∃ r : Fin (CC.faceDegree q), r ≠ k ∧
      v ∈ CC.edgeVertices (A.boundaryEdge q r) := by
    rcases hv with hv | hv
    · let r := ABKPR.faceSucc CC q
          (ABKPR.faceSucc CC q (ABKPR.faceSucc CC q k))
      have hrk : r ≠ k := by
        intro h
        have hs := congrArg (ABKPR.faceSucc CC q) h
        rw [ABKPR.faceSucc_four_of_faceDegree_eq_four CC hfour k] at hs
        exact (ABKPR.faceSucc_ne_of_faceDegree_eq_four CC hfour k) hs.symm
      refine ⟨r, hrk, ?_⟩
      rw [A.boundaryEdge_vertices]
      simp only [Finset.mem_insert, Finset.mem_singleton]
      right
      change v = A.boundaryVertex q (ABKPR.faceSucc CC q r)
      rw [ABKPR.faceSucc_four_of_faceDegree_eq_four CC hfour k]
      exact hv
    · let r := ABKPR.faceSucc CC q k
      refine ⟨r, ABKPR.faceSucc_ne_of_faceDegree_eq_four CC hfour k, ?_⟩
      rw [A.boundaryEdge_vertices]
      simp only [Finset.mem_insert, Finset.mem_singleton]
      left
      exact hv
  have hvk : v ∈ CC.edgeVertices
      (A.boundaryEdge (A.across ⟨q, k⟩).1 (A.across ⟨q, k⟩).2) := by
    rw [← A.across_sameEdge ⟨q, k⟩]
    rw [A.boundaryEdge_vertices]
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hv
  have hvr' : v ∈ CC.edgeVertices
      (A.boundaryEdge (A.across ⟨q, r⟩).1 (A.across ⟨q, r⟩).2) := by
    rw [← A.across_sameEdge ⟨q, r⟩]
    exact hvr
  rw [A.boundaryEdge_vertices] at hvk hvr'
  simp only [Finset.mem_insert, Finset.mem_singleton] at hvk hvr'
  refine ⟨r, hrk, ?_⟩
  rcases hvk with hk | hk <;> rcases hvr' with hr | hr
  · exact ⟨_, _, hk.symm.trans hr, hk.symm⟩
  · exact ⟨_, _, hk.symm.trans hr, hk.symm⟩
  · exact ⟨_, _, hk.symm.trans hr, hk.symm⟩
  · exact ⟨_, _, hk.symm.trans hr, hk.symm⟩

/-- The two bad quadrangles on the donor edges incident with a donation
corner would become two distinct bad neighbours of the recipient triangle.
Hence the final `twoBadAtDonationVertex` Stage-3 obstruction is impossible
in the concrete polar cellulation. -/
theorem no_two_bad_at_donationVertex
    (f : StrictFace (normals (B (P := P))))
    (x : (D hred ha hb hd hncol).donationRecipients f)
    (i : Fin ((C (P := P) ha hb hd hncol).faceDegree f))
    (hvertex : (D hred ha hb hd hncol).donationVertexOfGeometry f x =
      ABKPR.faceSucc (C (P := P) ha hb hd hncol) f i)
    (hi : i ∈ (D hred ha hb hd hncol).badNeighborIndices f)
    (hsucc : ABKPR.faceSucc (C (P := P) ha hb hd hncol) f i ∈
      (D hred ha hb hd hncol).badNeighborIndices f) : False := by
  let CC := C (P := P) ha hb hd hncol
  let A := D hred ha hb hd hncol
  let j := ABKPR.faceSucc CC f i
  let di := A.across ⟨f, i⟩
  let dj := A.across ⟨f, j⟩
  have hbadi : A.IsBadTwoQuadrangle di.1 := (Finset.mem_filter.mp hi).2
  have hbadj : A.IsBadTwoQuadrangle dj.1 :=
    (Finset.mem_filter.mp hsucc).2
  have hdine : di.1 ≠ dj.1 := by
    intro hfaces
    let E := ConcretePolarABKPRData.indexEquiv
      (vertex_degree := VD (P := P) ha hb hd hncol) ha hb hd hncol
    have hmap (r : ConcretePolarABKPRData.FaceDart
        (vertex_degree := VD (P := P) ha hb hd hncol) ha hb hd hncol) :
        ConcretePolarABKPRData.dartEquiv
            (vertex_degree := VD (P := P) ha hb hd hncol) ha hb hd hncol
            (A.across r) =
          SignVector.PolarBoundaryAcross.across (normals (B (P := P)))
            (normals_ne_zero (B (P := P))) normal_cross
            (ConcretePolarABKPRData.hspan ha hb hd hncol)
            (ConcretePolarABKPRData.dartEquiv
              (vertex_degree := VD (P := P) ha hb hd hncol)
              ha hb hd hncol r) := by
      simp [A, D, ConcretePolarABKPRData.concreteData,
        ConcretePolarABKPRData.toData, ConcretePolarABKPRData.across]
    have hfi : di.1 =
        (SignVector.PolarBoundaryAcross.across (normals (B (P := P)))
          (normals_ne_zero (B (P := P))) normal_cross
          (ConcretePolarABKPRData.hspan ha hb hd hncol) ⟨f, E f i⟩).1 :=
      congrArg Sigma.fst (hmap ⟨f, i⟩)
    have hfj : dj.1 =
        (SignVector.PolarBoundaryAcross.across (normals (B (P := P)))
          (normals_ne_zero (B (P := P))) normal_cross
          (ConcretePolarABKPRData.hspan ha hb hd hncol) ⟨f, E f j⟩).1 :=
      congrArg Sigma.fst (hmap ⟨f, j⟩)
    have hij : i ≠ j := faceSucc_ne_self ha hb hd hncol f i |>.symm
    have hijE : E f i ≠ E f j := fun h ↦ hij ((E f).injective h)
    have hsign := ConcretePolarLocalSector.across_sign_ne_at_first_owner
      (ConcretePolarABKPRData.hspan ha hb hd hncol) f
      (E f i) (E f j) hijE
    apply hsign
    rw [← hfi, ← hfj, hfaces]
  obtain ⟨sg, si, sj, sij, sp, sq, scommon, sdonor, srecipient,
      sdonorCorner, scornerDouble⟩ :=
    donationOppositeSector hred ha hb hd hncol f x
  let v := A.boundaryVertex f j
  have hvdi : v ∈ CC.edgeVertices (A.boundaryEdge di.1 di.2) := by
    rw [← A.across_sameEdge ⟨f, i⟩, A.boundaryEdge_vertices]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    right
    rfl
  obtain ⟨ri, hrine, pi, qi, hpqi, hpiv⟩ :=
    exists_other_crossing_at_quadrangle_endpoint
      hred ha hb hd hncol di.1 hbadi.1.1 di.2 v hvdi
  have hbacki : A.across ⟨di.1, di.2⟩ = ⟨f, i⟩ := by
    exact A.across_involutive ⟨f, i⟩
  have hfacei : (A.across ⟨sg, si⟩).1 =
      (A.across ⟨di.1, di.2⟩).1 :=
    sdonor.trans (congrArg Sigma.fst hbacki).symm
  have hcorneri : A.boundaryVertex (A.across ⟨sg, si⟩).1 sp =
      A.boundaryVertex (A.across ⟨di.1, di.2⟩).1 pi := by
    calc
      A.boundaryVertex (A.across ⟨sg, si⟩).1 sp =
          A.boundaryVertex f (A.donationVertexOfGeometry f x) := sdonorCorner
      _ = A.boundaryVertex f j := congrArg (A.boundaryVertex f) hvertex
      _ = v := rfl
      _ = A.boundaryVertex (A.across ⟨di.1, di.2⟩).1 pi := hpiv.symm
  have hopi :=
    ConcretePolarABKPRData.concreteData_opposite_across_face_unique_at_double_corner
      hred ha hb hd hncol sg si sj sij sp sq scommon
      di.1 di.2 ri hrine.symm pi qi hpqi hfacei hcorneri scornerDouble
  have hyi : (A.across ⟨di.1, ri⟩).1 = x.1 :=
    hopi.symm.trans srecipient
  have hvdj : v ∈ CC.edgeVertices (A.boundaryEdge dj.1 dj.2) := by
    rw [← A.across_sameEdge ⟨f, j⟩, A.boundaryEdge_vertices]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    left
    rfl
  obtain ⟨rj, hrjne, pj, qj, hpqj, hpjv⟩ :=
    exists_other_crossing_at_quadrangle_endpoint
      hred ha hb hd hncol dj.1 hbadj.1.1 dj.2 v hvdj
  have hbackj : A.across ⟨dj.1, dj.2⟩ = ⟨f, j⟩ := by
    exact A.across_involutive ⟨f, j⟩
  have hfacej : (A.across ⟨sg, si⟩).1 =
      (A.across ⟨dj.1, dj.2⟩).1 :=
    sdonor.trans (congrArg Sigma.fst hbackj).symm
  have hcornerj : A.boundaryVertex (A.across ⟨sg, si⟩).1 sp =
      A.boundaryVertex (A.across ⟨dj.1, dj.2⟩).1 pj := by
    calc
      A.boundaryVertex (A.across ⟨sg, si⟩).1 sp =
          A.boundaryVertex f (A.donationVertexOfGeometry f x) := sdonorCorner
      _ = A.boundaryVertex f j := congrArg (A.boundaryVertex f) hvertex
      _ = v := rfl
      _ = A.boundaryVertex (A.across ⟨dj.1, dj.2⟩).1 pj := hpjv.symm
  have hopj :=
    ConcretePolarABKPRData.concreteData_opposite_across_face_unique_at_double_corner
      hred ha hb hd hncol sg si sj sij sp sq scommon
      dj.1 dj.2 rj hrjne.symm pj qj hpqj hfacej hcornerj scornerDouble
  have hyj : (A.across ⟨dj.1, rj⟩).1 = x.1 :=
    hopj.symm.trans srecipient
  let yi := A.across ⟨di.1, ri⟩
  let yj := A.across ⟨dj.1, rj⟩
  let ui : Fin (CC.faceDegree x.1) :=
    Fin.cast (congrArg CC.faceDegree hyi) yi.2
  let uj : Fin (CC.faceDegree x.1) :=
    Fin.cast (congrArg CC.faceDegree hyj) yj.2
  have hdiDart : A.across ⟨x.1, ui⟩ = ⟨di.1, ri⟩ := by
    have hdart : (⟨x.1, ui⟩ : ABKPR.FaceDart CC) = yi := by
      refine Sigma.ext_iff.mpr ⟨hyi.symm, ?_⟩
      dsimp only [ui]
      rw [Fin.cast_eq_cast]
      exact cast_heq _ _
    rw [hdart]
    exact A.across_involutive ⟨di.1, ri⟩
  have hdjDart : A.across ⟨x.1, uj⟩ = ⟨dj.1, rj⟩ := by
    have hdart : (⟨x.1, uj⟩ : ABKPR.FaceDart CC) = yj := by
      refine Sigma.ext_iff.mpr ⟨hyj.symm, ?_⟩
      dsimp only [uj]
      rw [Fin.cast_eq_cast]
      exact cast_heq _ _
    rw [hdart]
    exact A.across_involutive ⟨dj.1, rj⟩
  have hui : ui ∈ A.badNeighborIndices x.1 := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [congrArg Sigma.fst hdiDart]
    exact hbadi
  have huj : uj ∈ A.badNeighborIndices x.1 := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [congrArg Sigma.fst hdjDart]
    exact hbadj
  have huine : ui ≠ uj := by
    intro h
    apply hdine
    calc
      di.1 = (A.across ⟨x.1, ui⟩).1 := (congrArg Sigma.fst hdiDart).symm
      _ = (A.across ⟨x.1, uj⟩).1 := by rw [h]
      _ = dj.1 := by
        simpa only using congrArg Sigma.fst hdjDart
  have hcard : 2 ≤ (A.badNeighborIndices x.1).card := by
    have hpair : ({ui, uj} : Finset (Fin (CC.faceDegree x.1))) ⊆
        A.badNeighborIndices x.1 := by
      intro k hk
      simp only [Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with rfl | rfl
      · exact hui
      · exact huj
    have hpaircard : ({ui, uj} : Finset (Fin (CC.faceDegree x.1))).card = 2 := by
      simp [huine]
    rw [← hpaircard]
    exact Finset.card_le_card hpair
  have hxcount : A.badNeighborCount x.1 = 1 :=
    (A.recipient_isBadTriangle x.2).2
  have hxcard : (A.badNeighborIndices x.1).card = 1 := by
    simpa only [ABKPR.Data.badNeighborCount] using hxcount
  rw [hxcard] at hcard
  omega

end Erdos735.ConcreteDonationObstructionRecognition
