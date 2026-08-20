/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos735.ConcreteStage4BeltCollision

/-!
# The fixed-helper collision witness

Two distinct evil cells adjacent to one helping quadrangle meet the
helper's opposite edge at its two different far corners.  This is the
fixed-helper companion to `two_helpers_distinct_shared_vertices`.
-/

open Classical
noncomputable section

namespace Erdos735.ConcreteStage4BeltCollisionHelper

open ProjectiveArrangement ProjectiveBoundaryExtraction
open ChartOrder SignVector SignVectorArrangement
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

/-- Two distinct evil cells adjacent to one helper meet the helper's
opposite edge at distinct oriented endpoints. -/
theorem two_evils_distinct_shared_vertices
    (L : (D hred ha hb hd hncol).FlankSystem (Line (P := P)))
    (hedge : L.edgeLine = ConcretePolarFlankBounds.edgeLine)
    {h : (D hred ha hb hd hncol).HelpingPair}
    {e k : (D hred ha hb hd hncol).EvilFace}
    (heh : L.Adj e h) (hkh : L.Adj k h) (hek : e ≠ k) :
    ∃ v u : OrientedVertex (B (P := P)), v ≠ u ∧
      v ∈ (C ha hb hd hncol).edgeVertices
        ((D hred ha hb hd hncol).boundaryEdge
          ((D hred ha hb hd hncol).evilBadOppositeDart e).1
          ((D hred ha hb hd hncol).evilBadOppositeDart e).2) ∧
      u ∈ (C ha hb hd hncol).edgeVertices
        ((D hred ha hb hd hncol).boundaryEdge
          ((D hred ha hb hd hncol).evilBadOppositeDart k).1
          ((D hred ha hb hd hncol).evilBadOppositeDart k).2) ∧
      v ∈ (C ha hb hd hncol).edgeVertices
        ((D hred ha hb hd hncol).boundaryEdge
          ((D hred ha hb hd hncol).helpingOppositeDart h).1
          ((D hred ha hb hd hncol).helpingOppositeDart h).2) ∧
      u ∈ (C ha hb hd hncol).edgeVertices
        ((D hred ha hb hd hncol).boundaryEdge
          ((D hred ha hb hd hncol).helpingOppositeDart h).1
          ((D hred ha hb hd hncol).helpingOppositeDart h).2) := by
  let DD := D hred ha hb hd hncol
  let CC := C ha hb hd hncol
  obtain ⟨je, hjeAdj, hjeFace, v, hvSepBad, hvEvilOpp, hvHelpOpp, _⟩ :=
    ConcreteStage4BeltCollision.flank_shared_vertex_data
      hred ha hb hd hncol L hedge heh
  obtain ⟨jk, hjkAdj, hjkFace, u, huSepBad, huEvilOpp, huHelpOpp, _⟩ :=
    ConcreteStage4BeltCollision.flank_shared_vertex_data
      hred ha hb hd hncol L hedge hkh
  obtain ⟨se, hse⟩ := heh
  obtain ⟨sk, hsk⟩ := hkh
  have hgeomE₀ := L.evilFlank_geometric e se h hse
  have hgeomK₀ := L.evilFlank_geometric k sk h hsk
  have hgeomE : DD.IsGeometricFlank ConcretePolarFlankBounds.edgeLine e h := by
    simpa only [hedge] using hgeomE₀
  have hgeomK : DD.IsGeometricFlank ConcretePolarFlankBounds.edgeLine k h := by
    simpa only [hedge] using hgeomK₀
  let ee : {q : DD.EvilFace //
      DD.IsGeometricFlank ConcretePolarFlankBounds.edgeLine q h} := ⟨e, hgeomE⟩
  let ek : {q : DD.EvilFace //
      DD.IsGeometricFlank ConcretePolarFlankBounds.edgeLine q h} := ⟨k, hgeomK⟩
  let re := DD.endpointHelperIndex ConcretePolarFlankBounds.edgeLine h ee
  let rk := DD.endpointHelperIndex ConcretePolarFlankBounds.edgeLine h ek
  have hreAdj : ABKPR.Data.CyclicAdjacentIndex h.index re :=
    ConcretePolarFlankBounds.endpointHelperIndex_adjacent
      hred ha hb hd hncol h ee
  have hrkAdj : ABKPR.Data.CyclicAdjacentIndex h.index rk :=
    ConcretePolarFlankBounds.endpointHelperIndex_adjacent
      hred ha hb hd hncol h ek
  have hrne : re ≠ rk := by
    apply Function.Injective.ne
      (DD.endpointHelperIndex_injective ConcretePolarFlankBounds.edgeLine
        (ConcretePolarFlankBounds.data_boundary_edgeLine_injective
          hred ha hb hd hncol) h)
    intro heq
    exact hek (congrArg Subtype.val heq)
  have hjeCanon : je = DD.endpointAdjacentIndex
      ConcretePolarFlankBounds.edgeLine h ee := by
    by_contra hne
    have hfacesNe := ConcretePolarABKPRData.concreteData_across_faces_ne
      hred ha hb hd hncol (DD.across (DD.evilDart e)).1 je
      (DD.endpointAdjacentIndex ConcretePolarFlankBounds.edgeLine h ee) hne
    apply hfacesNe
    exact hjeFace.trans
      (DD.endpointAdjacentIndex_spec ConcretePolarFlankBounds.edgeLine h ee).2.symm
  have hjkCanon : jk = DD.endpointAdjacentIndex
      ConcretePolarFlankBounds.edgeLine h ek := by
    by_contra hne
    have hfacesNe := ConcretePolarABKPRData.concreteData_across_faces_ne
      hred ha hb hd hncol (DD.across (DD.evilDart k)).1 jk
      (DD.endpointAdjacentIndex ConcretePolarFlankBounds.edgeLine h ek) hne
    apply hfacesNe
    exact hjkFace.trans
      (DD.endpointAdjacentIndex_spec ConcretePolarFlankBounds.edgeLine h ek).2.symm
  have hvSepHelp : v ∈ CC.edgeVertices (DD.boundaryEdge h.face re) := by
    have hdart : DD.across
        ⟨(DD.across (DD.evilDart e)).1, je⟩ = ⟨h.face, re⟩ := by
      rw [hjeCanon]
      exact DD.endpointAcrossDart_eq ConcretePolarFlankBounds.edgeLine h ee
    have hs := DD.across_sameEdge
      ⟨(DD.across (DD.evilDart e)).1, je⟩
    rw [hdart] at hs
    rw [← hs]
    exact hvSepBad
  have huSepHelp : u ∈ CC.edgeVertices (DD.boundaryEdge h.face rk) := by
    have hdart : DD.across
        ⟨(DD.across (DD.evilDart k)).1, jk⟩ = ⟨h.face, rk⟩ := by
      rw [hjkCanon]
      exact DD.endpointAcrossDart_eq ConcretePolarFlankBounds.edgeLine h ek
    have hs := DD.across_sameEdge
      ⟨(DD.across (DD.evilDart k)).1, jk⟩
    rw [hdart] at hs
    rw [← hs]
    exact huSepBad
  have hvNotPath : v ∉ CC.edgeVertices (DD.boundaryEdge h.face h.index) :=
    DD.not_mem_path_of_mem_adjacent_and_opposite h.isZeroDiagonal.1
      h.index re hreAdj hvSepHelp hvHelpOpp
  have huNotPath : u ∉ CC.edgeVertices (DD.boundaryEdge h.face h.index) :=
    DD.not_mem_path_of_mem_adjacent_and_opposite h.isZeroDiagonal.1
      h.index rk hrkAdj huSepHelp huHelpOpp
  have hvu : v ≠ u := DD.far_vertices_ne_of_distinct_adjacent
    h.isZeroDiagonal.1 h.index re rk hreAdj hrkAdj hrne
    hvSepHelp huSepHelp hvNotPath huNotPath
  exact ⟨v, u, hvu, hvEvilOpp, huEvilOpp, hvHelpOpp, huHelpOpp⟩

/-- Projective cyclic-edge form of the fixed-helper two-evil endpoint
statement. -/
theorem two_evils_distinct_projective_vertices
    (pick : OtherLineChoice (Line (P := P)))
    (L : (D hred ha hb hd hncol).FlankSystem (Line (P := P)))
    (hedge : L.edgeLine = ConcretePolarFlankBounds.edgeLine)
    {h : (D hred ha hb hd hncol).HelpingPair}
    {e k : (D hred ha hb hd hncol).EvilFace}
    (heh : L.Adj e h) (hkh : L.Adj k h) (hek : e ≠ k) :
    ∃ v u : ProjectiveBoundaryExtraction.Vertex (B (P := P)), v ≠ u ∧
      v ∈ cyclicEdgeVertices
        (Finset.univ : Finset (ProjectiveBoundaryExtraction.Vertex (B (P := P))))
        (OnLine (B (P := P))) (vertexCoord (B (P := P)))
        (ConcreteStage4BeltStep.helperOppositeBeltEdgeOfAdj
          hred ha hb hd hncol pick L hedge heh).1.1 ∧
      u ∈ cyclicEdgeVertices
        (Finset.univ : Finset (ProjectiveBoundaryExtraction.Vertex (B (P := P))))
        (OnLine (B (P := P))) (vertexCoord (B (P := P)))
        (ConcreteStage4BeltStep.helperOppositeBeltEdgeOfAdj
          hred ha hb hd hncol pick L hedge heh).1.1 ∧
      v ∈ cyclicEdgeVertices
        (Finset.univ : Finset (ProjectiveBoundaryExtraction.Vertex (B (P := P))))
        (OnLine (B (P := P))) (vertexCoord (B (P := P)))
        (ConcreteStage4BeltStep.evilOppositeBeltEdge
          hred ha hb hd hncol pick L hedge e).1.1 ∧
      u ∈ cyclicEdgeVertices
        (Finset.univ : Finset (ProjectiveBoundaryExtraction.Vertex (B (P := P))))
        (OnLine (B (P := P))) (vertexCoord (B (P := P)))
        (ConcreteStage4BeltStep.evilOppositeBeltEdge
          hred ha hb hd hncol pick L hedge k).1.1 := by
  let DD := D hred ha hb hd hncol
  let edgeH := DD.boundaryEdge (DD.helpingOppositeDart h).1
    (DD.helpingOppositeDart h).2
  let edgeE := DD.boundaryEdge (DD.evilBadOppositeDart e).1
    (DD.evilBadOppositeDart e).2
  let edgeK := DD.boundaryEdge (DD.evilBadOppositeDart k).1
    (DD.evilBadOppositeDart k).2
  obtain ⟨v, u, hvu, hvE, huK, hvH, huH⟩ :=
    two_evils_distinct_shared_vertices
      hred ha hb hd hncol L hedge heh hkh hek
  have hvu' : v.1 ≠ u.1 := by
    intro h
    exact hvu (ConcreteStage4BeltCollision.fst_injective_on_concreteEdgeVertices
      ha hb hd hncol edgeH hvH huH h)
  refine ⟨v.1, u.1, hvu', ?_, ?_, ?_, ?_⟩
  · exact ConcreteStage4BeltCollision.fst_mem_cyclicEdgeVertices_of_mem_concrete
      ha hb hd hncol pick edgeH hvH
  · exact ConcreteStage4BeltCollision.fst_mem_cyclicEdgeVertices_of_mem_concrete
      ha hb hd hncol pick edgeH huH
  · exact ConcreteStage4BeltCollision.fst_mem_cyclicEdgeVertices_of_mem_concrete
      ha hb hd hncol pick edgeE hvE
  · exact ConcreteStage4BeltCollision.fst_mem_cyclicEdgeVertices_of_mem_concrete
      ha hb hd hncol pick edgeK huK

end Erdos735.ConcreteStage4BeltCollisionHelper
