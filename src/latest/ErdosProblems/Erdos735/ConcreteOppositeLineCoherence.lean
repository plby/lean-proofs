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

import ErdosProblems.Erdos735.Stage4OppositeLine
import ErdosProblems.Erdos735.ConcretePolarFlankBounds
import ErdosProblems.Erdos735.BadNeighborLocal

/-!
# Opposite-line coherence for literal polar flanks

At the far endpoint of the edge separating a bad quadrangle from a helping
quadrangle, the two opposite boundary edges meet.  That endpoint is a double
blue vertex, so the two opposite edges have the same projective owner.  This
is the local strip lemma needed by the corrected Stage-4 Levi path.
-/

open Classical
noncomputable section

namespace Erdos735.ConcreteOppositeLineCoherence

open ProjectiveArrangement ProjectiveBoundaryExtraction SignVector ChartOrder
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
private abbrev hspan : Submodule.span ℝ
    (Set.range (normals (B (P := P)))) = ⊤ :=
  ConcretePolarABKPRData.hspan ha hb hd hncol
private abbrev Line := ProjectiveBoundaryExtraction.Line (B (P := P))

private theorem line_eq_of_multiplicity_two
    (v : ProjectiveBoundaryExtraction.Vertex (B (P := P)))
    (l₀ l₁ l : Line (P := P))
    (hmult : lineMultiplicity (OnLine (B (P := P))) v = 2)
    (hl₀ : OnLine (B (P := P)) v l₀)
    (hl₁ : OnLine (B (P := P)) v l₁)
    (hl : OnLine (B (P := P)) v l)
    (h₀₁ : l₀ ≠ l₁) (hl₀ne : l ≠ l₀) : l = l₁ := by
  let S := Finset.univ.filter fun q : Line (P := P) ↦
    OnLine (B (P := P)) v q
  have hpair : ({l₀, l₁} : Finset (Line (P := P))) ⊆ S := by
    intro q hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl <;> simp [S, hl₀, hl₁]
  have hcard : S.card = 2 := hmult
  have hpCard : ({l₀, l₁} : Finset (Line (P := P))).card = 2 :=
    Finset.card_pair h₀₁
  have heq : S = {l₀, l₁} := by
    exact Finset.Subset.antisymm
      (Finset.eq_of_subset_of_card_le hpair (by omega) |>.symm.subset) hpair
  have hlmem : l ∈ S := by simp [S, hl]
  rw [heq] at hlmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hlmem
  exact hlmem.resolve_left hl₀ne

theorem lineMultiplicity_eq_two_of_mem_bad_boundaryEdge
    {f : StrictFace (normals (B (P := P)))}
    (hbad : (D hred ha hb hd hncol).IsBadTwoQuadrangle f)
    (i : Fin ((C ha hb hd hncol).faceDegree f))
    (v : OrientedVertex (B (P := P)))
    (hv : v ∈ (C ha hb hd hncol).edgeVertices
      ((D hred ha hb hd hncol).boundaryEdge f i)) :
    lineMultiplicity (OnLine (B (P := P))) v.1 = 2 := by
  rw [(D hred ha hb hd hncol).boundaryEdge_vertices] at hv
  simp only [Finset.mem_insert, Finset.mem_singleton] at hv
  have hm : (C ha hb hd hncol).blueMultiplicity v = 2 := by
    rcases hv with rfl | rfl
    · exact (D hred ha hb hd hncol).badTwo_boundaryVertex_multiplicity_two hbad i
    · exact (D hred ha hb hd hncol).badTwo_boundaryVertex_multiplicity_two hbad
        (ABKPR.faceSucc (C ha hb hd hncol) f i)
  simpa [C, ConcretePolarCellulation.blueCellulation,
    ConcretePolarCellulation.blueCellulationOfVertexDegree,
    ConcretePolarCellulation.boundaryExtractionOfVertexDegree,
    BoundaryExtraction.toBlueCellulation] using hm

/-- Opposite edges belonging to adjacent evil and helping vertices of the
flank graph meet at the literal far corner of their separating edge.  The
statement retains the oriented projective vertex, so it can be transported
directly to the cyclic line skeleton. -/
theorem oppositeDarts_share_orientedVertex_with_separator_of_adj
    (L : (D hred ha hb hd hncol).FlankSystem (Line (P := P)))
    (hedge : L.edgeLine = ConcretePolarFlankBounds.edgeLine)
    {e : (D hred ha hb hd hncol).EvilFace}
    {h : (D hred ha hb hd hncol).HelpingPair}
    (heh : L.Adj e h) :
    ∃ j : Fin ((C ha hb hd hncol).faceDegree
        ((D hred ha hb hd hncol).across
          ((D hred ha hb hd hncol).evilDart e)).1),
      ABKPR.Data.CyclicAdjacentIndex
        ((D hred ha hb hd hncol).across
          ((D hred ha hb hd hncol).evilDart e)).2 j ∧
      ((D hred ha hb hd hncol).across ⟨
        ((D hred ha hb hd hncol).across
          ((D hred ha hb hd hncol).evilDart e)).1, j⟩).1 = h.face ∧
      ∃ v : OrientedVertex (B (P := P)),
      v ∈ (C ha hb hd hncol).edgeVertices
        ((D hred ha hb hd hncol).boundaryEdge
          ((D hred ha hb hd hncol).across
            ((D hred ha hb hd hncol).evilDart e)).1 j) ∧
      v ∈ (C ha hb hd hncol).edgeVertices
        ((D hred ha hb hd hncol).boundaryEdge
          ((D hred ha hb hd hncol).evilBadOppositeDart e).1
          ((D hred ha hb hd hncol).evilBadOppositeDart e).2) ∧
      v ∈ (C ha hb hd hncol).edgeVertices
        ((D hred ha hb hd hncol).boundaryEdge
          ((D hred ha hb hd hncol).helpingOppositeDart h).1
          ((D hred ha hb hd hncol).helpingOppositeDart h).2) := by
  let DD := D hred ha hb hd hncol
  let CC := C ha hb hd hncol
  obtain ⟨side, hside⟩ := heh
  have hgeomL := L.evilFlank_geometric e side h hside
  have hgeom : DD.IsGeometricFlank
      ConcretePolarFlankBounds.edgeLine e h := by
    simpa only [hedge] using hgeomL
  let ee : {e : DD.EvilFace //
      DD.IsGeometricFlank ConcretePolarFlankBounds.edgeLine e h} :=
    ⟨e, hgeom⟩
  let bad := DD.across (DD.evilDart e)
  let i := bad.2
  let j := DD.endpointAdjacentIndex ConcretePolarFlankBounds.edgeLine h ee
  let r := DD.endpointHelperIndex ConcretePolarFlankBounds.edgeLine h ee
  have hspec := DD.endpointAdjacentIndex_spec
    ConcretePolarFlankBounds.edgeLine h ee
  have hbad : DD.IsBadTwoQuadrangle bad.1 := DD.evilDart_across_bad e
  have hhelp : DD.IsZeroDiagonalQuadrangle h.face := h.isZeroDiagonal
  obtain ⟨v, hvj, hvopp, _hvnot⟩ :=
    DD.exists_farVertex_mem_adjacent_opposite_not_path
      hbad.1.1 i j hspec.1
  have hsepEq : DD.boundaryEdge bad.1 j = DD.boundaryEdge h.face r := by
    have hacross := DD.across_sameEdge ⟨bad.1, j⟩
    have hdart := DD.endpointAcrossDart_eq
      ConcretePolarFlankBounds.edgeLine h ee
    change DD.across ⟨bad.1, j⟩ = ⟨h.face, r⟩ at hdart
    rw [hdart] at hacross
    exact hacross
  have hvsepH : v ∈ CC.edgeVertices (DD.boundaryEdge h.face r) := by
    rw [← hsepEq]
    exact hvj
  have hmult : lineMultiplicity (OnLine (B (P := P))) v.1 = 2 :=
    lineMultiplicity_eq_two_of_mem_bad_boundaryEdge
      hred ha hb hd hncol hbad j v hvj
  let lSep : Line (P := P) := ConcretePolarFlankBounds.edgeLine
    (DD.boundaryEdge bad.1 j)
  let lBadOpp : Line (P := P) := ConcretePolarFlankBounds.edgeLine
    (DD.boundaryEdge bad.1
      (ABKPR.faceSucc CC bad.1 (ABKPR.faceSucc CC bad.1 i)))
  let lPath : Line (P := P) := ConcretePolarFlankBounds.edgeLine
    (DD.boundaryEdge bad.1 i)
  have hSepBadOpp : lSep ≠ lBadOpp := by
    exact Function.Injective.ne
      (ConcretePolarFlankBounds.data_boundary_edgeLine_injective
        hred ha hb hd hncol bad.1)
      (ABKPR.cyclicAdjacent_ne_secondSucc_of_faceDegree_eq_four
        CC hbad.1.1 i j hspec.1)
  have hSepPath : lSep ≠ lPath := by
    have hji : j ≠ i :=
      (ABKPR.ne_of_cyclicAdjacent_of_faceDegree_eq_four
        CC hbad.1.1 i j hspec.1).symm
    exact Function.Injective.ne
      (ConcretePolarFlankBounds.data_boundary_edgeLine_injective
        hred ha hb hd hncol bad.1) hji
  have hBadOppPath : lBadOpp ≠ lPath := by
    exact Function.Injective.ne
      (ConcretePolarFlankBounds.data_boundary_edgeLine_injective
        hred ha hb hd hncol bad.1)
      (ABKPR.secondSucc_ne_of_faceDegree_eq_four CC hbad.1.1 i)
  have hvnotPathH : v ∉ CC.edgeVertices
      (DD.boundaryEdge h.face h.index) := by
    intro hvpathH
    have hlSep : OnLine (B (P := P)) v.1 lSep :=
      concreteEdgeVertex_on_support (hspan ha hb hd hncol)
        (DD.boundaryEdge bad.1 j) v hvj
    have hlBadOpp : OnLine (B (P := P)) v.1 lBadOpp :=
      concreteEdgeVertex_on_support (hspan ha hb hd hncol)
        (DD.boundaryEdge bad.1
          (ABKPR.faceSucc CC bad.1 (ABKPR.faceSucc CC bad.1 i))) v hvopp
    have hlHelperPath : OnLine (B (P := P)) v.1
        (ConcretePolarFlankBounds.edgeLine
          (DD.boundaryEdge h.face h.index)) :=
      concreteEdgeVertex_on_support (hspan ha hb hd hncol)
        (DD.boundaryEdge h.face h.index) v hvpathH
    have hHelperPath : ConcretePolarFlankBounds.edgeLine
        (DD.boundaryEdge h.face h.index) = lPath := by
      calc
        ConcretePolarFlankBounds.edgeLine (DD.boundaryEdge h.face h.index) =
            ConcretePolarFlankBounds.edgeLine
              (DD.boundaryEdge e.1 (DD.evilIndex e)) := hgeom.2
        _ = lPath := by
          exact congrArg ConcretePolarFlankBounds.edgeLine
            (DD.across_sameEdge (DD.evilDart e))
    have hlPath : OnLine (B (P := P)) v.1 lPath := by
      rw [← hHelperPath]
      exact hlHelperPath
    have hline := line_eq_of_multiplicity_two v.1
      lSep lBadOpp lPath hmult hlSep hlBadOpp hlPath
        hSepBadOpp hSepPath.symm
    exact hBadOppPath hline.symm
  have hadjH : ABKPR.Data.CyclicAdjacentIndex h.index r :=
    ConcretePolarFlankBounds.endpointHelperIndex_adjacent
      hred ha hb hd hncol h ee
  have hvHelpOpp : v ∈ CC.edgeVertices
      (DD.boundaryEdge h.face
        (ABKPR.faceSucc CC h.face (ABKPR.faceSucc CC h.face h.index))) := by
    exact DD.mem_opposite_of_mem_adjacent_not_mem_path
      hhelp.1 h.index r hadjH hvsepH hvnotPathH
  exact ⟨j, hspec.1, hspec.2, v, hvj, hvopp, hvHelpOpp⟩

/-- Incidence-only projection of the strengthened far-corner statement. -/
theorem oppositeDarts_share_orientedVertex_of_adj
    (L : (D hred ha hb hd hncol).FlankSystem (Line (P := P)))
    (hedge : L.edgeLine = ConcretePolarFlankBounds.edgeLine)
    {e : (D hred ha hb hd hncol).EvilFace}
    {h : (D hred ha hb hd hncol).HelpingPair}
    (heh : L.Adj e h) :
    ∃ v : OrientedVertex (B (P := P)),
      v ∈ (C ha hb hd hncol).edgeVertices
        ((D hred ha hb hd hncol).boundaryEdge
          ((D hred ha hb hd hncol).evilBadOppositeDart e).1
          ((D hred ha hb hd hncol).evilBadOppositeDart e).2) ∧
      v ∈ (C ha hb hd hncol).edgeVertices
        ((D hred ha hb hd hncol).boundaryEdge
          ((D hred ha hb hd hncol).helpingOppositeDart h).1
          ((D hred ha hb hd hncol).helpingOppositeDart h).2) := by
  obtain ⟨_j, _hadj, _hface, v, _hvsep, hvbad, hvhelp⟩ :=
    oppositeDarts_share_orientedVertex_with_separator_of_adj
      hred ha hb hd hncol L hedge heh
  exact ⟨v, hvbad, hvhelp⟩

/-- Literal owner labels force the opposite edges of every geometric flank
to have the same owner. -/
theorem oppositeLineCoherence
    (L : (D hred ha hb hd hncol).FlankSystem (Line (P := P)))
    (hedge : L.edgeLine = ConcretePolarFlankBounds.edgeLine) :
    ABKPR.Data.OppositeLineCoherence (D hred ha hb hd hncol) L := by
  let DD := D hred ha hb hd hncol
  let CC := C ha hb hd hncol
  refine ⟨?_⟩
  intro e h heh
  obtain ⟨side, hside⟩ := heh
  have hgeomL := L.evilFlank_geometric e side h hside
  have hgeom : DD.IsGeometricFlank ConcretePolarFlankBounds.edgeLine e h := by
    simpa only [hedge] using hgeomL
  let ee : {e : DD.EvilFace //
      DD.IsGeometricFlank ConcretePolarFlankBounds.edgeLine e h} := ⟨e, hgeom⟩
  let bad := DD.across (DD.evilDart e)
  let i := bad.2
  let j := DD.endpointAdjacentIndex ConcretePolarFlankBounds.edgeLine h ee
  let r := DD.endpointHelperIndex ConcretePolarFlankBounds.edgeLine h ee
  have hspec := DD.endpointAdjacentIndex_spec
    ConcretePolarFlankBounds.edgeLine h ee
  have hbad : DD.IsBadTwoQuadrangle bad.1 := DD.evilDart_across_bad e
  have hhelp : DD.IsZeroDiagonalQuadrangle h.face := h.isZeroDiagonal
  obtain ⟨v, hvj, hvopp, hvnot⟩ :=
    DD.exists_farVertex_mem_adjacent_opposite_not_path hbad.1.1 i j hspec.1
  have hsepEq : DD.boundaryEdge bad.1 j = DD.boundaryEdge h.face r := by
    have hacross := DD.across_sameEdge ⟨bad.1, j⟩
    have hdart := DD.endpointAcrossDart_eq
      ConcretePolarFlankBounds.edgeLine h ee
    change DD.across ⟨bad.1, j⟩ = ⟨h.face, r⟩ at hdart
    rw [hdart] at hacross
    exact hacross
  have hvsepH : v ∈ CC.edgeVertices (DD.boundaryEdge h.face r) := by
    rw [← hsepEq]
    exact hvj
  have hmult : lineMultiplicity (OnLine (B (P := P))) v.1 = 2 :=
    lineMultiplicity_eq_two_of_mem_bad_boundaryEdge hred ha hb hd hncol
      hbad j v hvj
  let lSep : Line (P := P) := ConcretePolarFlankBounds.edgeLine
    (DD.boundaryEdge bad.1 j)
  let lBadOpp : Line (P := P) := ConcretePolarFlankBounds.edgeLine
    (DD.boundaryEdge bad.1
      (ABKPR.faceSucc CC bad.1 (ABKPR.faceSucc CC bad.1 i)))
  let lHelpOpp : Line (P := P) := ConcretePolarFlankBounds.edgeLine
    (DD.boundaryEdge h.face
      (ABKPR.faceSucc CC h.face (ABKPR.faceSucc CC h.face h.index)))
  let lPath : Line (P := P) := ConcretePolarFlankBounds.edgeLine
    (DD.boundaryEdge bad.1 i)
  have hSepBadOpp : lSep ≠ lBadOpp := by
    exact Function.Injective.ne
      (ConcretePolarFlankBounds.data_boundary_edgeLine_injective
        hred ha hb hd hncol bad.1)
      (ABKPR.cyclicAdjacent_ne_secondSucc_of_faceDegree_eq_four
        CC hbad.1.1 i j hspec.1)
  have hSepPath : lSep ≠ lPath := by
    have hji : j ≠ i :=
      (ABKPR.ne_of_cyclicAdjacent_of_faceDegree_eq_four
        CC hbad.1.1 i j hspec.1).symm
    exact Function.Injective.ne
      (ConcretePolarFlankBounds.data_boundary_edgeLine_injective
        hred ha hb hd hncol bad.1) hji
  have hBadOppPath : lBadOpp ≠ lPath := by
    exact Function.Injective.ne
      (ConcretePolarFlankBounds.data_boundary_edgeLine_injective
        hred ha hb hd hncol bad.1)
      (ABKPR.secondSucc_ne_of_faceDegree_eq_four CC hbad.1.1 i)
  have hvnotPathH : v ∉ CC.edgeVertices (DD.boundaryEdge h.face h.index) := by
    intro hvpathH
    have hlSep : OnLine (B (P := P)) v.1 lSep :=
      concreteEdgeVertex_on_support (hspan ha hb hd hncol)
        (DD.boundaryEdge bad.1 j) v hvj
    have hlBadOpp : OnLine (B (P := P)) v.1 lBadOpp :=
      concreteEdgeVertex_on_support (hspan ha hb hd hncol)
        (DD.boundaryEdge bad.1
          (ABKPR.faceSucc CC bad.1 (ABKPR.faceSucc CC bad.1 i))) v hvopp
    have hlHelperPath : OnLine (B (P := P)) v.1
        (ConcretePolarFlankBounds.edgeLine
          (DD.boundaryEdge h.face h.index)) :=
      concreteEdgeVertex_on_support (hspan ha hb hd hncol)
        (DD.boundaryEdge h.face h.index) v hvpathH
    have hHelperPath : ConcretePolarFlankBounds.edgeLine
        (DD.boundaryEdge h.face h.index) = lPath := by
      calc
        ConcretePolarFlankBounds.edgeLine (DD.boundaryEdge h.face h.index) =
            ConcretePolarFlankBounds.edgeLine
              (DD.boundaryEdge e.1 (DD.evilIndex e)) := hgeom.2
        _ = lPath := by
          exact congrArg ConcretePolarFlankBounds.edgeLine
            (DD.across_sameEdge (DD.evilDart e))
    have hlPath : OnLine (B (P := P)) v.1 lPath := by
      rw [← hHelperPath]
      exact hlHelperPath
    have hline := line_eq_of_multiplicity_two v.1
      lSep lBadOpp lPath hmult hlSep hlBadOpp hlPath hSepBadOpp hSepPath.symm
    exact hBadOppPath hline.symm
  have hadjH : ABKPR.Data.CyclicAdjacentIndex h.index r := by
    exact ConcretePolarFlankBounds.endpointHelperIndex_adjacent
      hred ha hb hd hncol h ee
  have hvHelpOpp : v ∈ CC.edgeVertices
      (DD.boundaryEdge h.face
        (ABKPR.faceSucc CC h.face (ABKPR.faceSucc CC h.face h.index))) := by
    exact DD.mem_opposite_of_mem_adjacent_not_mem_path
      hhelp.1 h.index r hadjH hvsepH hvnotPathH
  have hlSep : OnLine (B (P := P)) v.1 lSep :=
    concreteEdgeVertex_on_support (hspan ha hb hd hncol)
      (DD.boundaryEdge bad.1 j) v hvj
  have hlBadOpp : OnLine (B (P := P)) v.1 lBadOpp :=
    concreteEdgeVertex_on_support (hspan ha hb hd hncol)
      (DD.boundaryEdge bad.1
        (ABKPR.faceSucc CC bad.1 (ABKPR.faceSucc CC bad.1 i))) v hvopp
  have hlHelpOpp : OnLine (B (P := P)) v.1 lHelpOpp :=
    concreteEdgeVertex_on_support (hspan ha hb hd hncol)
      (DD.boundaryEdge h.face
        (ABKPR.faceSucc CC h.face (ABKPR.faceSucc CC h.face h.index))) v hvHelpOpp
  have hHelpOppSep : lHelpOpp ≠ lSep := by
    have hrs : r ≠
        ABKPR.faceSucc CC h.face (ABKPR.faceSucc CC h.face h.index) :=
      ABKPR.cyclicAdjacent_ne_secondSucc_of_faceDegree_eq_four
        CC hhelp.1 h.index r hadjH
    intro heq
    have hsame : ConcretePolarFlankBounds.edgeLine
        (DD.boundaryEdge h.face
          (ABKPR.faceSucc CC h.face (ABKPR.faceSucc CC h.face h.index))) =
        ConcretePolarFlankBounds.edgeLine (DD.boundaryEdge h.face r) := by
      change lHelpOpp = _
      rw [← hsepEq]
      exact heq
    exact hrs ((ConcretePolarFlankBounds.data_boundary_edgeLine_injective
      hred ha hb hd hncol h.face) hsame).symm
  have hline : lHelpOpp = lBadOpp :=
    line_eq_of_multiplicity_two v.1
      lSep lBadOpp lHelpOpp hmult hlSep hlBadOpp hlHelpOpp
      hSepBadOpp hHelpOppSep
  unfold ABKPR.Data.evilOppositeLine ABKPR.Data.helperOppositeLine
  rw [hedge]
  exact hline.symm

/-- The opposite owner of an evil bad quadrangle is distinct from the
evil's path-line owner. -/
theorem evilOppositeLine_ne_badEdgeLine
    (L : (D hred ha hb hd hncol).FlankSystem (Line (P := P)))
    (hedge : L.edgeLine = ConcretePolarFlankBounds.edgeLine)
    (e : (D hred ha hb hd hncol).EvilFace) :
    ABKPR.Data.evilOppositeLine (D hred ha hb hd hncol) L e ≠
      L.edgeLine ((D hred ha hb hd hncol).boundaryEdge
        e.1 ((D hred ha hb hd hncol).evilIndex e)) := by
  let DD := D hred ha hb hd hncol
  let CC := C ha hb hd hncol
  let bad := DD.across (DD.evilDart e)
  let i := bad.2
  intro heq
  unfold ABKPR.Data.evilOppositeLine ABKPR.Data.evilBadOppositeDart at heq
  rw [hedge] at heq
  have hpath := congrArg ConcretePolarFlankBounds.edgeLine
    (DD.across_sameEdge (DD.evilDart e))
  have hopath : ConcretePolarFlankBounds.edgeLine
      (DD.boundaryEdge bad.1
        (ABKPR.faceSucc CC bad.1 (ABKPR.faceSucc CC bad.1 i))) =
      ConcretePolarFlankBounds.edgeLine (DD.boundaryEdge bad.1 i) :=
    heq.trans hpath
  have hindex := (ConcretePolarFlankBounds.data_boundary_edgeLine_injective
    hred ha hb hd hncol bad.1) hopath
  exact (ABKPR.secondSucc_ne_of_faceDegree_eq_four CC
    (DD.evilDart_across_bad e).1.1 i) hindex

/-- A triangular face across either cyclic flank contains an edge on the
evil opposite line, and that edge meets the bad quadrangle's opposite edge
at the literal far corner.  This retains the endpoint data needed to place
the triangle in the cyclic line belt. -/
theorem triangleFlank_oppositeEdge_bridge
    (L : (D hred ha hb hd hncol).FlankSystem (Line (P := P)))
    (hedge : L.edgeLine = ConcretePolarFlankBounds.edgeLine)
    (e : (D hred ha hb hd hncol).EvilFace)
    (j : Fin ((C ha hb hd hncol).faceDegree
      ((D hred ha hb hd hncol).across
        ((D hred ha hb hd hncol).evilDart e)).1))
    (hadj : ABKPR.Data.CyclicAdjacentIndex
      ((D hred ha hb hd hncol).across
        ((D hred ha hb hd hncol).evilDart e)).2 j)
    (htri : (C ha hb hd hncol).faceDegree
      ((D hred ha hb hd hncol).across
        ⟨((D hred ha hb hd hncol).across
          ((D hred ha hb hd hncol).evilDart e)).1, j⟩).1 = 3) :
    ∃ u : Fin ((C ha hb hd hncol).faceDegree
        ((D hred ha hb hd hncol).across
          ⟨((D hred ha hb hd hncol).across
            ((D hred ha hb hd hncol).evilDart e)).1, j⟩).1),
      ConcretePolarFlankBounds.edgeLine
          ((D hred ha hb hd hncol).boundaryEdge
            ((D hred ha hb hd hncol).across
              ⟨((D hred ha hb hd hncol).across
                ((D hred ha hb hd hncol).evilDart e)).1, j⟩).1 u) =
        ABKPR.Data.evilOppositeLine (D hred ha hb hd hncol) L e ∧
      ∃ v : OrientedVertex (B (P := P)),
        v ∈ (C ha hb hd hncol).edgeVertices
          ((D hred ha hb hd hncol).boundaryEdge
            ((D hred ha hb hd hncol).across
              ((D hred ha hb hd hncol).evilDart e)).1 j) ∧
        v ∈ (C ha hb hd hncol).edgeVertices
          ((D hred ha hb hd hncol).boundaryEdge
            ((D hred ha hb hd hncol).evilBadOppositeDart e).1
            ((D hred ha hb hd hncol).evilBadOppositeDart e).2) ∧
        v ∈ (C ha hb hd hncol).edgeVertices
          ((D hred ha hb hd hncol).boundaryEdge
            ((D hred ha hb hd hncol).across
              ⟨((D hred ha hb hd hncol).across
                ((D hred ha hb hd hncol).evilDart e)).1, j⟩).1 u) ∧
        ¬ OnLine (B (P := P)) v.1
          (L.edgeLine ((D hred ha hb hd hncol).boundaryEdge
            e.1 ((D hred ha hb hd hncol).evilIndex e))) := by
  let DD := D hred ha hb hd hncol
  let CC := C ha hb hd hncol
  let bad := DD.across (DD.evilDart e)
  let i := bad.2
  let flank := DD.across ⟨bad.1, j⟩
  have hbad : DD.IsBadTwoQuadrangle bad.1 := DD.evilDart_across_bad e
  obtain ⟨v, hvj, hvopp, _hvnot⟩ :=
    DD.exists_farVertex_mem_adjacent_opposite_not_path
      hbad.1.1 i j hadj
  have hsepEq : DD.boundaryEdge bad.1 j =
      DD.boundaryEdge flank.1 flank.2 := by
    exact DD.across_sameEdge ⟨bad.1, j⟩
  have hvflank : v ∈ CC.edgeVertices
      (DD.boundaryEdge flank.1 flank.2) := by
    rw [← hsepEq]
    exact hvj
  obtain ⟨u, hune, hvu⟩ :=
    DD.exists_other_boundaryEdge_at_vertex_of_faceDegree_eq_three
      htri flank.2 hvflank
  let lSep : Line (P := P) := ConcretePolarFlankBounds.edgeLine
    (DD.boundaryEdge bad.1 j)
  let lBadOpp : Line (P := P) := ConcretePolarFlankBounds.edgeLine
    (DD.boundaryEdge bad.1
      (ABKPR.faceSucc CC bad.1 (ABKPR.faceSucc CC bad.1 i)))
  let lPath : Line (P := P) := ConcretePolarFlankBounds.edgeLine
    (DD.boundaryEdge bad.1 i)
  let lOther : Line (P := P) := ConcretePolarFlankBounds.edgeLine
    (DD.boundaryEdge flank.1 u)
  have hmult : lineMultiplicity (OnLine (B (P := P))) v.1 = 2 :=
    lineMultiplicity_eq_two_of_mem_bad_boundaryEdge
      hred ha hb hd hncol hbad j v hvj
  have hSepBadOpp : lSep ≠ lBadOpp := by
    exact Function.Injective.ne
      (ConcretePolarFlankBounds.data_boundary_edgeLine_injective
        hred ha hb hd hncol bad.1)
      (ABKPR.cyclicAdjacent_ne_secondSucc_of_faceDegree_eq_four
        CC hbad.1.1 i j hadj)
  have hSepPath : lSep ≠ lPath := by
    have hji : j ≠ i :=
      (ABKPR.ne_of_cyclicAdjacent_of_faceDegree_eq_four
        CC hbad.1.1 i j hadj).symm
    exact Function.Injective.ne
      (ConcretePolarFlankBounds.data_boundary_edgeLine_injective
        hred ha hb hd hncol bad.1) hji
  have hBadOppPath : lBadOpp ≠ lPath := by
    exact Function.Injective.ne
      (ConcretePolarFlankBounds.data_boundary_edgeLine_injective
        hred ha hb hd hncol bad.1)
      (ABKPR.secondSucc_ne_of_faceDegree_eq_four CC hbad.1.1 i)
  have hOtherSep : lOther ≠ lSep := by
    intro heq
    apply hune
    apply ConcretePolarFlankBounds.data_boundary_edgeLine_injective
      hred ha hb hd hncol flank.1
    calc
      ConcretePolarFlankBounds.edgeLine
          (DD.boundaryEdge flank.1 u) = lSep := heq
      _ = ConcretePolarFlankBounds.edgeLine
          (DD.boundaryEdge flank.1 flank.2) :=
        congrArg ConcretePolarFlankBounds.edgeLine hsepEq
  have hlSep : OnLine (B (P := P)) v.1 lSep :=
    concreteEdgeVertex_on_support (hspan ha hb hd hncol)
      (DD.boundaryEdge bad.1 j) v hvj
  have hlBadOpp : OnLine (B (P := P)) v.1 lBadOpp :=
    concreteEdgeVertex_on_support (hspan ha hb hd hncol)
      (DD.boundaryEdge bad.1
        (ABKPR.faceSucc CC bad.1 (ABKPR.faceSucc CC bad.1 i))) v hvopp
  have hlOther : OnLine (B (P := P)) v.1 lOther :=
    concreteEdgeVertex_on_support (hspan ha hb hd hncol)
      (DD.boundaryEdge flank.1 u) v hvu
  have hline : lOther = lBadOpp :=
    line_eq_of_multiplicity_two v.1 lSep lBadOpp lOther
      hmult hlSep hlBadOpp hlOther hSepBadOpp hOtherSep
  have hvnotPathLine : ¬ OnLine (B (P := P)) v.1 lPath := by
    intro hvPath
    have hpathEq := line_eq_of_multiplicity_two v.1
      lSep lBadOpp lPath hmult hlSep hlBadOpp hvPath
      hSepBadOpp hSepPath.symm
    exact hBadOppPath hpathEq.symm
  refine ⟨u, ?_, v, hvj, hvopp, hvu, ?_⟩
  change ConcretePolarFlankBounds.edgeLine
        (DD.boundaryEdge flank.1 u) =
      ABKPR.Data.evilOppositeLine DD L e
  unfold ABKPR.Data.evilOppositeLine ABKPR.Data.evilBadOppositeDart
  rw [hedge]
  exact hline
  rw [hedge]
  have hpath := congrArg ConcretePolarFlankBounds.edgeLine
    (DD.across_sameEdge (DD.evilDart e))
  intro hv
  apply hvnotPathLine
  change OnLine (B (P := P)) v.1
    (ConcretePolarFlankBounds.edgeLine
      (DD.boundaryEdge bad.1 i))
  exact hpath ▸ hv

/-- In the same triangular flank, the boundary edge complementary to the
opposite-line edge lies on the evil path line.  The two edges meet at the
literal projective crossing of the path and opposite owners. -/
theorem triangleFlank_pathEdge_bridge
    (L : (D hred ha hb hd hncol).FlankSystem (Line (P := P)))
    (hedge : L.edgeLine = ConcretePolarFlankBounds.edgeLine)
    (e : (D hred ha hb hd hncol).EvilFace)
    (j : Fin ((C ha hb hd hncol).faceDegree
      ((D hred ha hb hd hncol).across
        ((D hred ha hb hd hncol).evilDart e)).1))
    (hadj : ABKPR.Data.CyclicAdjacentIndex
      ((D hred ha hb hd hncol).across
        ((D hred ha hb hd hncol).evilDart e)).2 j)
    (htri : (C ha hb hd hncol).faceDegree
      ((D hred ha hb hd hncol).across
        ⟨((D hred ha hb hd hncol).across
          ((D hred ha hb hd hncol).evilDart e)).1, j⟩).1 = 3)
    (uOpp : Fin ((C ha hb hd hncol).faceDegree
      ((D hred ha hb hd hncol).across
        ⟨((D hred ha hb hd hncol).across
          ((D hred ha hb hd hncol).evilDart e)).1, j⟩).1))
    (huOpp : ConcretePolarFlankBounds.edgeLine
        ((D hred ha hb hd hncol).boundaryEdge
          ((D hred ha hb hd hncol).across
            ⟨((D hred ha hb hd hncol).across
              ((D hred ha hb hd hncol).evilDart e)).1, j⟩).1 uOpp) =
      ABKPR.Data.evilOppositeLine (D hred ha hb hd hncol) L e) :
    ∃ uPath : Fin ((C ha hb hd hncol).faceDegree
        ((D hred ha hb hd hncol).across
          ⟨((D hred ha hb hd hncol).across
            ((D hred ha hb hd hncol).evilDart e)).1, j⟩).1),
      L.edgeLine
          ((D hred ha hb hd hncol).boundaryEdge
            ((D hred ha hb hd hncol).across
              ⟨((D hred ha hb hd hncol).across
                ((D hred ha hb hd hncol).evilDart e)).1, j⟩).1 uPath) =
        L.edgeLine ((D hred ha hb hd hncol).boundaryEdge
          e.1 ((D hred ha hb hd hncol).evilIndex e)) ∧
      uPath ≠ uOpp ∧
      ∃ v : OrientedVertex (B (P := P)),
        v ∈ (C ha hb hd hncol).edgeVertices
          ((D hred ha hb hd hncol).boundaryEdge
            ((D hred ha hb hd hncol).across
              ⟨((D hred ha hb hd hncol).across
                ((D hred ha hb hd hncol).evilDart e)).1, j⟩).1 uOpp) ∧
        v ∈ (C ha hb hd hncol).edgeVertices
          ((D hred ha hb hd hncol).boundaryEdge
            ((D hred ha hb hd hncol).across
              ⟨((D hred ha hb hd hncol).across
                ((D hred ha hb hd hncol).evilDart e)).1, j⟩).1 uPath) := by
  let DD := D hred ha hb hd hncol
  let CC := C ha hb hd hncol
  let bad := DD.across (DD.evilDart e)
  let i := bad.2
  let opp := ABKPR.faceSucc CC bad.1 (ABKPR.faceSucc CC bad.1 i)
  let flank := DD.across ⟨bad.1, j⟩
  have hbad : DD.IsBadTwoQuadrangle bad.1 := DD.evilDart_across_bad e
  obtain ⟨vNear, hvj, hvi, _hvnotOpp⟩ :=
    DD.exists_nearVertex_mem_adjacent_path_not_opposite
      hbad.1.1 i j hadj
  have hsepEq : DD.boundaryEdge bad.1 j =
      DD.boundaryEdge flank.1 flank.2 :=
    DD.across_sameEdge ⟨bad.1, j⟩
  have hvFlankSep : vNear ∈ CC.edgeVertices
      (DD.boundaryEdge flank.1 flank.2) := by
    rw [← hsepEq]
    exact hvj
  obtain ⟨uPath, huPathNeSep, hvPath⟩ :=
    DD.exists_other_boundaryEdge_at_vertex_of_faceDegree_eq_three
      htri flank.2 hvFlankSep
  let lSep : Line (P := P) := ConcretePolarFlankBounds.edgeLine
    (DD.boundaryEdge bad.1 j)
  let lPath : Line (P := P) := ConcretePolarFlankBounds.edgeLine
    (DD.boundaryEdge bad.1 i)
  let lBadOpp : Line (P := P) := ConcretePolarFlankBounds.edgeLine
    (DD.boundaryEdge bad.1 opp)
  let lOther : Line (P := P) := ConcretePolarFlankBounds.edgeLine
    (DD.boundaryEdge flank.1 uPath)
  have hmult : lineMultiplicity (OnLine (B (P := P))) vNear.1 = 2 :=
    lineMultiplicity_eq_two_of_mem_bad_boundaryEdge
      hred ha hb hd hncol hbad j vNear hvj
  have hSepPath : lSep ≠ lPath := by
    have hji : j ≠ i :=
      (ABKPR.ne_of_cyclicAdjacent_of_faceDegree_eq_four
        CC hbad.1.1 i j hadj).symm
    exact Function.Injective.ne
      (ConcretePolarFlankBounds.data_boundary_edgeLine_injective
        hred ha hb hd hncol bad.1) hji
  have hOtherSep : lOther ≠ lSep := by
    intro heq
    apply huPathNeSep
    apply ConcretePolarFlankBounds.data_boundary_edgeLine_injective
      hred ha hb hd hncol flank.1
    calc
      ConcretePolarFlankBounds.edgeLine
          (DD.boundaryEdge flank.1 uPath) = lSep := heq
      _ = ConcretePolarFlankBounds.edgeLine
          (DD.boundaryEdge flank.1 flank.2) :=
        congrArg ConcretePolarFlankBounds.edgeLine hsepEq
  have hvSep : OnLine (B (P := P)) vNear.1 lSep :=
    concreteEdgeVertex_on_support (hspan ha hb hd hncol)
      (DD.boundaryEdge bad.1 j) vNear hvj
  have hvBadPath : OnLine (B (P := P)) vNear.1 lPath :=
    concreteEdgeVertex_on_support (hspan ha hb hd hncol)
      (DD.boundaryEdge bad.1 i) vNear hvi
  have hvOther : OnLine (B (P := P)) vNear.1 lOther :=
    concreteEdgeVertex_on_support (hspan ha hb hd hncol)
      (DD.boundaryEdge flank.1 uPath) vNear hvPath
  have hOtherPath : lOther = lPath :=
    line_eq_of_multiplicity_two vNear.1 lSep lPath lOther
      hmult hvSep hvBadPath hvOther hSepPath hOtherSep
  have hPathOwner : L.edgeLine (DD.boundaryEdge flank.1 uPath) =
      L.edgeLine (DD.boundaryEdge e.1 (DD.evilIndex e)) := by
    rw [hedge]
    calc
      ConcretePolarFlankBounds.edgeLine
          (DD.boundaryEdge flank.1 uPath) = lPath := hOtherPath
      _ = ConcretePolarFlankBounds.edgeLine
          (DD.boundaryEdge e.1 (DD.evilIndex e)) := by
        exact congrArg ConcretePolarFlankBounds.edgeLine
          (DD.across_sameEdge (DD.evilDart e)).symm
  have hBadOppPath : lBadOpp ≠ lPath := by
    exact Function.Injective.ne
      (ConcretePolarFlankBounds.data_boundary_edgeLine_injective
        hred ha hb hd hncol bad.1)
      (ABKPR.secondSucc_ne_of_faceDegree_eq_four CC hbad.1.1 i)
  have huPathNeOpp : uPath ≠ uOpp := by
    intro heq
    subst uOpp
    have huOpp' := huOpp
    change lOther = ABKPR.Data.evilOppositeLine DD L e at huOpp'
    unfold ABKPR.Data.evilOppositeLine ABKPR.Data.evilBadOppositeDart at huOpp'
    rw [hedge] at huOpp'
    change lOther = lBadOpp at huOpp'
    exact hBadOppPath (huOpp'.symm.trans hOtherPath)
  obtain ⟨vCross, hvOpp, hvPath'⟩ :=
    DD.exists_common_vertex_of_distinct_edges_of_faceDegree_eq_three
      htri uOpp uPath huPathNeOpp.symm
  exact ⟨uPath, hPathOwner, huPathNeOpp, vCross, hvOpp, hvPath'⟩

/-- Incidence-only projection of `triangleFlank_oppositeEdge_bridge`. -/
theorem triangleFlank_incident_evilOppositeLine
    (L : (D hred ha hb hd hncol).FlankSystem (Line (P := P)))
    (hedge : L.edgeLine = ConcretePolarFlankBounds.edgeLine)
    (e : (D hred ha hb hd hncol).EvilFace)
    (j : Fin ((C ha hb hd hncol).faceDegree
      ((D hred ha hb hd hncol).across
        ((D hred ha hb hd hncol).evilDart e)).1))
    (hadj : ABKPR.Data.CyclicAdjacentIndex
      ((D hred ha hb hd hncol).across
        ((D hred ha hb hd hncol).evilDart e)).2 j)
    (htri : (C ha hb hd hncol).faceDegree
      ((D hred ha hb hd hncol).across
        ⟨((D hred ha hb hd hncol).across
          ((D hred ha hb hd hncol).evilDart e)).1, j⟩).1 = 3) :
    SignVectorArrangement.LineFaceIncident (normals (B (P := P)))
      (ABKPR.Data.evilOppositeLine (D hred ha hb hd hncol) L e)
      ((D hred ha hb hd hncol).across
        ⟨((D hred ha hb hd hncol).across
          ((D hred ha hb hd hncol).evilDart e)).1, j⟩).1 := by
  let DD := D hred ha hb hd hncol
  let flank := DD.across
    ⟨(DD.across (DD.evilDart e)).1, j⟩
  obtain ⟨u, hu, _v, _hvsep, _hvbad, _hvu, _hvnotPath⟩ :=
    triangleFlank_oppositeEdge_bridge
      hred ha hb hd hncol L hedge e j hadj htri
  refine ⟨DD.boundaryEdge flank.1 u, ?_, ?_⟩
  · rw [← SignVector.PolarBoundaryAcross.faceBoundary_toFinset
      (normals (B (P := P))) normal_cross (hspan ha hb hd hncol) flank.1]
    exact List.mem_toFinset.mpr (DD.boundaryEdge_mem flank.1 u)
  · exact hu

end Erdos735.ConcreteOppositeLineCoherence
