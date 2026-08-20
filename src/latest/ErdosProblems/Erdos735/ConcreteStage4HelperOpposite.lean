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

import ErdosProblems.Erdos735.ConcreteRedOppositeSector
import ErdosProblems.Erdos735.ConcreteOppositeLineCoherence
import ErdosProblems.Erdos735.ConcretePolarAcrossSquare

/-!
# The face beyond a helping opposite edge is not triangular

At the far double corner of an evil--helper incidence, the bad quadrangle
has a red diagonal.  Continuing that red line into the opposite sector puts
a red chord in the face across the helper's opposite edge.  A triangular
face has no red chord, giving the required Stage-4 belt exclusion.
-/

open Classical
noncomputable section

namespace Erdos735.ConcreteStage4HelperOpposite

open ProjectiveArrangement ProjectiveBoundaryExtraction
open ChartOrder SignVector SignVector.RedChordSector SignVectorArrangement
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
private abbrev C := ConcretePolarCellulation.blueCellulation
  (B (P := P)) ha hb hd hncol
private abbrev D := ConcretePolarABKPRData.concreteData hred ha hb hd hncol
private abbrev Line := ProjectiveBoundaryExtraction.Line (B (P := P))
private abbrev hspan : Submodule.span ℝ
    (Set.range (normals (B (P := P)))) = ⊤ :=
  ConcretePolarABKPRData.hspan ha hb hd hncol

/-- The face across a helping quadrangle's opposite edge contains a red
chord whenever the helper is adjacent to an evil. -/
theorem helpingOpposite_across_has_redChord
    (L : (D hred ha hb hd hncol).FlankSystem (Line (P := P)))
    (hedge : L.edgeLine = ConcretePolarFlankBounds.edgeLine)
    {e : (D hred ha hb hd hncol).EvilFace}
    {h : (D hred ha hb hd hncol).HelpingPair}
    (heh : L.Adj e h) :
    0 < ((D hred ha hb hd hncol).redChords
      ((D hred ha hb hd hncol).across
        ((D hred ha hb hd hncol).helpingOppositeDart h)).1).card := by
  let DD := D hred ha hb hd hncol
  let CC := C ha hb hd hncol
  let bad := DD.across (DD.evilDart e)
  let i := bad.2
  let opp := ABKPR.faceSucc CC bad.1 (ABKPR.faceSucc CC bad.1 i)
  let hop := DD.helpingOppositeDart h
  let target := DD.across hop
  obtain ⟨j, hadj, hface, v, hvsep, hvbad, hvhelp⟩ :=
    ConcreteOppositeLineCoherence.oppositeDarts_share_orientedVertex_with_separator_of_adj
      hred ha hb hd hncol L hedge heh
  have hfaceLocal : (DD.across ⟨bad.1, j⟩).1 = h.face := hface
  have hbad : DD.IsBadTwoQuadrangle bad.1 := DD.evilDart_across_bad e
  have hmult : lineMultiplicity (OnLine (B (P := P))) v.1 = 2 :=
    ConcreteOppositeLineCoherence.lineMultiplicity_eq_two_of_mem_bad_boundaryEdge
      hred ha hb hd hncol hbad j v hvsep
  let s : Line (P := P) := ConcretePolarFlankBounds.edgeLine
    (DD.boundaryEdge bad.1 j)
  let o : Line (P := P) := ConcretePolarFlankBounds.edgeLine
    (DD.boundaryEdge bad.1 opp)
  have hso : s ≠ o := by
    exact Function.Injective.ne
      (ConcretePolarFlankBounds.data_boundary_edgeLine_injective
        hred ha hb hd hncol bad.1)
      (ABKPR.cyclicAdjacent_ne_secondSucc_of_faceDegree_eq_four
        CC hbad.1.1 i j hadj)
  have hvs : OnLine (B (P := P)) v.1 s :=
    concreteEdgeVertex_on_support (hspan ha hb hd hncol)
      (DD.boundaryEdge bad.1 j) v hvsep
  have hvo : OnLine (B (P := P)) v.1 o :=
    concreteEdgeVertex_on_support (hspan ha hb hd hncol)
      (DD.boundaryEdge bad.1 opp) v hvbad
  have weak_of_edge_mem {f : StrictFace (normals (B (P := P)))}
      (k : Fin (CC.faceDegree f))
      (hvk : v ∈ CC.edgeVertices (DD.boundaryEdge f k)) :
      WeaklyRealizes (normals (B (P := P))) f.1 (orientedRep v) := by
    rw [DD.boundaryEdge_vertices] at hvk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hvk
    rcases hvk with hvk | hvk
    · rw [hvk]
      change WeaklyRealizes (normals (B (P := P))) f.1
        (orientedRep (boundaryOrientedVertex (hspan ha hb hd hncol) f
          (ConcretePolarABKPRData.indexEquiv
            (vertex_degree :=
              ConcretePolarVertexDegree.concreteVertexEdges_card_eq
                (B (P := P)) ha hb hd hncol)
            ha hb hd hncol f k)))
      exact orientedRep_boundaryOrientedVertex_weaklyRealizes
        (hspan ha hb hd hncol) f _
    · rw [hvk]
      change WeaklyRealizes (normals (B (P := P))) f.1
        (orientedRep (boundaryOrientedVertex (hspan ha hb hd hncol) f
          (ConcretePolarABKPRData.indexEquiv
            (vertex_degree :=
              ConcretePolarVertexDegree.concreteVertexEdges_card_eq
                (B (P := P)) ha hb hd hncol)
            ha hb hd hncol f (ABKPR.faceSucc CC f k))))
      exact orientedRep_boundaryOrientedVertex_weaklyRealizes
        (hspan ha hb hd hncol) f _
  have hwbad : WeaklyRealizes (normals (B (P := P))) bad.1.1
      (orientedRep v) := weak_of_edge_mem opp hvbad
  have hvtarget : v ∈ CC.edgeVertices
      (DD.boundaryEdge target.1 target.2) := by
    rw [← DD.across_sameEdge hop]
    exact hvhelp
  have hwtarget : WeaklyRealizes (normals (B (P := P))) target.1.1
      (orientedRep v) := weak_of_edge_mem target.2 hvtarget
  obtain ⟨p, hpv⟩ : ∃ p : Fin (CC.faceDegree bad.1),
      DD.boundaryVertex bad.1 p = v := by
    change v ∈ CC.edgeVertices (DD.boundaryEdge bad.1 opp) at hvbad
    rw [DD.boundaryEdge_vertices] at hvbad
    simp only [Finset.mem_insert, Finset.mem_singleton] at hvbad
    rcases hvbad with hv | hv
    · exact ⟨opp, hv.symm⟩
    · exact ⟨ABKPR.faceSucc CC bad.1 opp, hv.symm⟩
  have hpD : p ∈ DD.redEndpoints bad.1 := by
    rw [DD.redEndpoints_eq_univ_of_twoDiagonal hbad.1]
    exact Finset.mem_univ p
  let E := ConcretePolarABKPRData.indexEquiv
    (vertex_degree := ConcretePolarVertexDegree.concreteVertexEdges_card_eq
      (B (P := P)) ha hb hd hncol) ha hb hd hncol
  have hpPolar : E bad.1 p ∈ PolarRedChordExtraction.redEndpoints
      hred (hspan ha hb hd hncol) bad.1 :=
    (ConcretePolarABKPRData.redEndpoint_reindex_iff
      hred
      (vertex_degree := ConcretePolarVertexDegree.concreteVertexEdges_card_eq
        (B (P := P)) ha hb hd hncol)
      ha hb hd hncol bad.1 p).mp hpD
  obtain ⟨red, hredOrd, hbadRest, hredInc⟩ :=
    (ConcreteBadReceiver.mem_polarRedEndpoints_iff_exists_feasible_incident
      hred (hspan ha hb hd hncol) bad.1 (E bad.1 p)).mp hpPolar
  have hredIncV : Incident v.1.1 red := by
    rw [← hpv]
    change Incident
      (boundaryOrientedVertex (hspan ha hb hd hncol) bad.1
        (E bad.1 p)).1.1 red
    exact hredInc
  have hOppOwner : ConcretePolarFlankBounds.edgeLine
      (DD.boundaryEdge h.face hop.2) = o := by
    have hcoh := (ConcreteOppositeLineCoherence.oppositeLineCoherence
      hred ha hb hd hncol L hedge).eq_of_adj e h heh
    unfold ABKPR.Data.evilOppositeLine ABKPR.Data.helperOppositeLine at hcoh
    rw [hedge] at hcoh
    exact hcoh.symm
  have hsgn : bad.1.1 s ≠ target.1.1 s := by
    have h1 : h.face.1 s = !(bad.1.1 s) := by
      rw [← hfaceLocal]
      have hx := ConcretePolarABKPRData.concreteData_across_face_sign
        hred ha hb hd hncol bad.1 j s
      change (DD.across ⟨bad.1, j⟩).1.1 s =
        if s = s then !(bad.1.1 s) else bad.1.1 s at hx
      simpa using hx
    have h2 : target.1.1 s = h.face.1 s := by
      have hx := ConcretePolarABKPRData.concreteData_across_face_sign
        hred ha hb hd hncol h.face hop.2 s
      change target.1.1 s = if s =
        ConcretePolarFlankBounds.edgeLine (DD.boundaryEdge h.face hop.2)
        then !(h.face.1 s) else h.face.1 s at hx
      rw [hOppOwner] at hx
      simpa [hso] using hx
    cases hs : bad.1.1 s <;> simp [hs, h1, h2]
  have hogn : bad.1.1 o ≠ target.1.1 o := by
    have h1 : h.face.1 o = bad.1.1 o := by
      rw [← hfaceLocal]
      have hx := ConcretePolarABKPRData.concreteData_across_face_sign
        hred ha hb hd hncol bad.1 j o
      change (DD.across ⟨bad.1, j⟩).1.1 o =
        if o = s then !(bad.1.1 o) else bad.1.1 o at hx
      simpa [hso.symm] using hx
    have h2 : target.1.1 o = !(h.face.1 o) := by
      have hx := ConcretePolarABKPRData.concreteData_across_face_sign
        hred ha hb hd hncol h.face hop.2 o
      change target.1.1 o = if o =
        ConcretePolarFlankBounds.edgeLine (DD.boundaryEdge h.face hop.2)
        then !(h.face.1 o) else h.face.1 o at hx
      rw [hOppOwner] at hx
      simpa using hx
    cases ho : bad.1.1 o <;> simp [ho, h1, h2]
  have htargetRest : RestrictedRealizable (normals (B (P := P)))
      (normalVec red) target.1.1 :=
    ConcreteRedOppositeSector.restrictedRealizable_opposite_sector
      v hmult s o hso hvs hvo bad.1 target.1 hwbad hwtarget
      hsgn hogn red hredOrd hbadRest hredIncV
  let rr : PolarRedChordExtraction.ChordLine (P := P) target.1 :=
    ⟨⟨red, hredOrd⟩, htargetRest⟩
  have hpChord : PolarRedChordExtraction.chordPair
      hred (hspan ha hb hd hncol) target.1 rr ∈
      PolarRedChordExtraction.redChords
        hred (hspan ha hb hd hncol) target.1 :=
    (PolarRedChordExtraction.mem_redChords_iff
      hred (hspan ha hb hd hncol) target.1 _).mpr ⟨rr, rfl⟩
  have hpolarPos : 0 < (PolarRedChordExtraction.redChords
      hred (hspan ha hb hd hncol) target.1).card :=
    Finset.card_pos.mpr ⟨_, hpChord⟩
  have hcard := ConcretePolarABKPRData.redChords_card_eq_polar
    hred
    (vertex_degree := ConcretePolarVertexDegree.concreteVertexEdges_card_eq
      (B (P := P)) ha hb hd hncol)
    ha hb hd hncol target.1
  change (DD.redChords target.1).card =
    (PolarRedChordExtraction.redChords
      hred (hspan ha hb hd hncol) target.1).card at hcard
  change 0 < (DD.redChords target.1).card
  rw [hcard]
  exact hpolarPos

/-- Therefore the face across a helping opposite edge is never triangular. -/
theorem helpingOpposite_across_not_triangle
    (L : (D hred ha hb hd hncol).FlankSystem (Line (P := P)))
    (hedge : L.edgeLine = ConcretePolarFlankBounds.edgeLine)
    {e : (D hred ha hb hd hncol).EvilFace}
    {h : (D hred ha hb hd hncol).HelpingPair}
    (heh : L.Adj e h) :
    (C ha hb hd hncol).faceDegree
      ((D hred ha hb hd hncol).across
        ((D hred ha hb hd hncol).helpingOppositeDart h)).1 ≠ 3 := by
  intro htri
  have hzero := (D hred ha hb hd hncol).triangle_no_redChord _ htri
  have hpos := helpingOpposite_across_has_redChord
    hred ha hb hd hncol L hedge heh
  omega

end Erdos735.ConcreteStage4HelperOpposite
