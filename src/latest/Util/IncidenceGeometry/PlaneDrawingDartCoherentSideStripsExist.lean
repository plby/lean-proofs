import Util.IncidenceGeometry.OrdinaryDrawingImage
import Util.IncidenceGeometry.PlaneDrawingDartArcData
import Util.IncidenceGeometry.PlaneDrawingDartArcEndpointAwaySeparation
import Util.IncidenceGeometry.PlaneDrawingDartCoherentSideStripsForPair
import Util.IncidenceGeometry.PlaneDrawingDartVertexSectorGeometry
import Util.IncidenceGeometry.PlaneDrawingDartVertexStarData
import Util.IncidenceGeometry.PolygonalArc
import Util.IncidenceGeometry.PolygonalArcCollar
import Util.IncidenceGeometry.PolygonalArcEndpointIsolationExists
import Util.IncidenceGeometry.PolygonalArcInitialEndpointLeftCone
import Util.IncidenceGeometry.PolygonalArcSideStripAssembly
import Util.IncidenceGeometry.PolygonalArcTerminalEndpointLeftCone
import Util.IncidenceGeometry.PolygonalSideStrips
import Util.IncidenceGeometry.PolygonalSideStripsReverseOfSameCarrier
import Util.IncidenceGeometry.PositiveSeparation
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

open Classical
noncomputable section

lemma PlaneDrawingDartCoherentSideStripsExist {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] [DecidableRel G.Adj]
    (D : OrdinaryPolygonalDrawing G) (hD : D.crossingSet.card = 0)
    (A : PlaneDrawingDartArcData G D)
    (C : PlaneDrawingDartVertexSectorGeometry G D A) :
    ∃ sideStrips : ∀ d : G.Dart, PolygonalSideStrips (A.dartArc d),
      (∀ d : G.Dart, ((sideStrips d).leftStrip).Nonempty) ∧
        (∀ d : G.Dart, (sideStrips d).leftStrip ⊆
          (OrdinaryDrawingImage G D)ᶜ) ∧
          (∀ (d : G.Dart) (x : EuclideanSpace ℝ (Fin 2)),
            x ∈ (A.dartArc d).relativeInterior →
              ∃ U : Set (EuclideanSpace ℝ (Fin 2)),
                IsOpen U ∧ x ∈ U ∧
                  U ∩ (OrdinaryDrawingImage G D)ᶜ ⊆
                    (sideStrips d).leftStrip ∪
                      (sideStrips d.symm).leftStrip) ∧
            (∀ d : G.Dart,
              (sideStrips d).rightStrip = (sideStrips d.symm).leftStrip) ∧
              (∀ d : G.Dart,
                (C.successorSector d ∩ (sideStrips d).leftStrip ∩
                  Metric.ball (D.vertexPlacement d.toProd.2)
                    (C.star.localDiskRadius d.toProd.2)).Nonempty) ∧
                (∀ d : G.Dart,
                  (C.successorSector d ∩
                    (sideStrips (C.star.successor d)).leftStrip ∩
                      Metric.ball (D.vertexPlacement d.toProd.2)
                        (C.star.localDiskRadius d.toProd.2)).Nonempty) := by
  let dartEdge : G.Dart → G.edgeSet := fun d => ⟨d.edge, SimpleGraph.Dart.edge_mem d⟩
  have dartEdge_symm : ∀ d : G.Dart, dartEdge d.symm = dartEdge d := by
    intro d
    apply Subtype.ext
    exact SimpleGraph.Dart.edge_symm d
  have edge_has_dart : ∀ e : G.edgeSet, ∃ d : G.Dart, d.edge = e.1 := by
    intro e
    rcases e with ⟨e, he⟩
    revert he
    refine Sym2.inductionOn e ?_
    intro u v he
    have huv : G.Adj u v := (SimpleGraph.mem_edgeSet (G := G)).mp he
    exact ⟨⟨(u, v), huv⟩, rfl⟩
  let edgeRep : G.edgeSet → G.Dart := fun e => Classical.choose (edge_has_dart e)
  have edgeRep_edge : ∀ e : G.edgeSet, (edgeRep e).edge = e.1 := fun e =>
    Classical.choose_spec (edge_has_dart e)
  let pairExists := fun e : G.edgeSet =>
    PlaneDrawingDartCoherentSideStripsForPair G D hD A C (edgeRep e)
  let pairS : ∀ e : G.edgeSet, PolygonalSideStrips (A.dartArc (edgeRep e)) :=
    fun e => Classical.choose (pairExists e)
  let pairT : ∀ e : G.edgeSet, PolygonalSideStrips (A.dartArc (edgeRep e).symm) :=
    fun e => Classical.choose (Classical.choose_spec (pairExists e))
  have pairSpec : ∀ e : G.edgeSet,
      (pairS e).rightStrip = (pairT e).leftStrip ∧
        (pairT e).rightStrip = (pairS e).leftStrip ∧
          (pairS e).leftStrip.Nonempty ∧
            (pairT e).leftStrip.Nonempty ∧
              (pairS e).leftStrip ⊆ (OrdinaryDrawingImage G D)ᶜ ∧
                (pairT e).leftStrip ⊆ (OrdinaryDrawingImage G D)ᶜ ∧
                  (∀ x : EuclideanSpace ℝ (Fin 2),
                    x ∈ (A.dartArc (edgeRep e)).relativeInterior →
                      ∃ U : Set (EuclideanSpace ℝ (Fin 2)),
                        IsOpen U ∧ x ∈ U ∧
                          U ∩ (OrdinaryDrawingImage G D)ᶜ ⊆
                            (pairS e).leftStrip ∪ (pairT e).leftStrip) ∧
                    (∀ x : EuclideanSpace ℝ (Fin 2),
                      x ∈ (A.dartArc (edgeRep e).symm).relativeInterior →
                        ∃ U : Set (EuclideanSpace ℝ (Fin 2)),
                          IsOpen U ∧ x ∈ U ∧
                            U ∩ (OrdinaryDrawingImage G D)ᶜ ⊆
                              (pairT e).leftStrip ∪ (pairS e).leftStrip) ∧
                      (C.successorSector (edgeRep e) ∩ (pairS e).leftStrip ∩
                        Metric.ball (D.vertexPlacement (edgeRep e).toProd.2)
                          (C.star.localDiskRadius (edgeRep e).toProd.2)).Nonempty ∧
                        (C.successorSector (edgeRep e).symm ∩ (pairT e).leftStrip ∩
                          Metric.ball (D.vertexPlacement (edgeRep e).symm.toProd.2)
                            (C.star.localDiskRadius (edgeRep e).symm.toProd.2)).Nonempty ∧
                          (∀ p : G.Dart, C.star.successor p = edgeRep e →
                            (C.successorSector p ∩ (pairS e).leftStrip ∩
                              Metric.ball (D.vertexPlacement p.toProd.2)
                                (C.star.localDiskRadius p.toProd.2)).Nonempty) ∧
                            (∀ p : G.Dart, C.star.successor p = (edgeRep e).symm →
                              (C.successorSector p ∩ (pairT e).leftStrip ∩
                                Metric.ball (D.vertexPlacement p.toProd.2)
                                  (C.star.localDiskRadius p.toProd.2)).Nonempty) := by
    intro e
    dsimp [pairS, pairT, pairExists]
    exact Classical.choose_spec (Classical.choose_spec
      (PlaneDrawingDartCoherentSideStripsForPair G D hD A C (edgeRep e)))
  let stripOfEq {γ δ : PolygonalArc} (hγ : γ = δ) (S : PolygonalSideStrips γ) :
      PolygonalSideStrips δ :=
    { collar := S.collar
      leftStrip := S.leftStrip
      rightStrip := S.rightStrip
      collar_open := S.collar_open
      left_open := S.left_open
      right_open := S.right_open
      relativeInterior_subset_collar := by
        simpa [← hγ] using S.relativeInterior_subset_collar
      left_subset_collar := S.left_subset_collar
      right_subset_collar := S.right_subset_collar
      left_connected := S.left_connected
      right_connected := S.right_connected
      left_disjoint_arc := by
        simpa [← hγ] using S.left_disjoint_arc
      right_disjoint_arc := by
        simpa [← hγ] using S.right_disjoint_arc
      side_strips_disjoint := S.side_strips_disjoint
      relativeInterior_subset_closure_left := by
        simpa [← hγ] using S.relativeInterior_subset_closure_left
      relativeInterior_subset_closure_right := by
        simpa [← hγ] using S.relativeInterior_subset_closure_right
      collar_without_arc := by
        simpa [← hγ] using S.collar_without_arc }
  let sideStrips : ∀ d : G.Dart, PolygonalSideStrips (A.dartArc d) := fun d =>
    let e := dartEdge d
    let a := edgeRep e
    if h : a = d then
      stripOfEq (by simpa [a] using congrArg A.dartArc h) (pairS e)
    else
      have ha_edge : a.edge = d.edge := by
        dsimp [a, e, dartEdge]
        exact edgeRep_edge (dartEdge d)
      have ha_symm : a.symm = d := by
        rcases (SimpleGraph.dart_edge_eq_iff a d).mp ha_edge with had | had
        · exact False.elim (h had)
        · simpa using congrArg SimpleGraph.Dart.symm had
      stripOfEq (by simpa [a] using congrArg A.dartArc ha_symm) (pairT e)
  have rep_symm_of_not : ∀ d : G.Dart,
      ¬ edgeRep (dartEdge d) = d → (edgeRep (dartEdge d)).symm = d := by
    intro d h
    have ha_edge : (edgeRep (dartEdge d)).edge = d.edge := by
      simpa [dartEdge] using edgeRep_edge (dartEdge d)
    rcases (SimpleGraph.dart_edge_eq_iff (edgeRep (dartEdge d)) d).mp ha_edge with had | had
    · exact False.elim (h had)
    · simpa using congrArg SimpleGraph.Dart.symm had
  have rep_eq_symm_of_symm : ∀ d : G.Dart,
      (edgeRep (dartEdge d)).symm = d → edgeRep (dartEdge d) = d.symm := by
    intro d h
    simpa using congrArg SimpleGraph.Dart.symm h
  have rep_not_symm_of_rep : ∀ d : G.Dart,
      edgeRep (dartEdge d) = d → ¬ edgeRep (dartEdge d.symm) = d.symm := by
    intro d h hsymm
    have hsymm' : edgeRep (dartEdge d) = d.symm := by
      simpa [dartEdge_symm d] using hsymm
    have hd : d = d.symm := h.symm.trans hsymm'
    exact (SimpleGraph.Dart.symm_ne d) hd.symm
  refine ⟨sideStrips, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro d
    by_cases h : edgeRep (dartEdge d) = d
    · rcases pairSpec (dartEdge d) with
        ⟨hST, hTS, hSnon, hTnon, hScomp, hTcomp, hSlocal, hTlocal,
          hSterm, hTterm, hSprev, hTprev⟩
      simpa [sideStrips, h, stripOfEq] using hSnon
    · rcases pairSpec (dartEdge d) with
        ⟨hST, hTS, hSnon, hTnon, hScomp, hTcomp, hSlocal, hTlocal,
          hSterm, hTterm, hSprev, hTprev⟩
      have ha_symm := rep_symm_of_not d h
      simpa [sideStrips, h, ha_symm, stripOfEq] using hTnon
  · intro d
    by_cases h : edgeRep (dartEdge d) = d
    · rcases pairSpec (dartEdge d) with
        ⟨hST, hTS, hSnon, hTnon, hScomp, hTcomp, hSlocal, hTlocal,
          hSterm, hTterm, hSprev, hTprev⟩
      simpa [sideStrips, h, stripOfEq] using hScomp
    · rcases pairSpec (dartEdge d) with
        ⟨hST, hTS, hSnon, hTnon, hScomp, hTcomp, hSlocal, hTlocal,
          hSterm, hTterm, hSprev, hTprev⟩
      have ha_symm := rep_symm_of_not d h
      simpa [sideStrips, h, ha_symm, stripOfEq] using hTcomp
  · intro d x hx
    by_cases h : edgeRep (dartEdge d) = d
    · rcases pairSpec (dartEdge d) with
        ⟨hST, hTS, hSnon, hTnon, hScomp, hTcomp, hSlocal, hTlocal,
          hSterm, hTterm, hSprev, hTprev⟩
      have hx' : x ∈ (A.dartArc (edgeRep (dartEdge d))).relativeInterior := by
        simpa [h] using hx
      rcases hSlocal x hx' with ⟨U, hUopen, hxU, hUsub⟩
      refine ⟨U, hUopen, hxU, ?_⟩
      have hsymm_not := rep_not_symm_of_rep d h
      have hd_ne_symm : ¬ d = d.symm := fun hd => (SimpleGraph.Dart.symm_ne d) hd.symm
      have hUsub' :
          U ∩ (OrdinaryDrawingImage G D)ᶜ ⊆
            (pairS (dartEdge d)).leftStrip ∪ (pairT (dartEdge d.symm)).leftStrip := by
        rw [dartEdge_symm d]
        exact hUsub
      simpa [sideStrips, h, hsymm_not, hd_ne_symm, dartEdge_symm d, stripOfEq] using hUsub'
    · rcases pairSpec (dartEdge d) with
        ⟨hST, hTS, hSnon, hTnon, hScomp, hTcomp, hSlocal, hTlocal,
          hSterm, hTterm, hSprev, hTprev⟩
      have ha_symm := rep_symm_of_not d h
      have ha_eq_dsymm := rep_eq_symm_of_symm d ha_symm
      have hx' : x ∈ (A.dartArc (edgeRep (dartEdge d)).symm).relativeInterior := by
        simpa [ha_symm] using hx
      rcases hTlocal x hx' with ⟨U, hUopen, hxU, hUsub⟩
      refine ⟨U, hUopen, hxU, ?_⟩
      have hsymm_ne : ¬ d.symm = d := SimpleGraph.Dart.symm_ne d
      have hUsub' :
          U ∩ (OrdinaryDrawingImage G D)ᶜ ⊆
            (pairT (dartEdge d)).leftStrip ∪ (pairS (dartEdge d.symm)).leftStrip := by
        rw [dartEdge_symm d]
        exact hUsub
      simpa [sideStrips, h, ha_symm, ha_eq_dsymm, hsymm_ne, dartEdge_symm d, stripOfEq] using hUsub'
  · intro d
    by_cases h : edgeRep (dartEdge d) = d
    · rcases pairSpec (dartEdge d) with
        ⟨hST, hTS, hSnon, hTnon, hScomp, hTcomp, hSlocal, hTlocal,
          hSterm, hTterm, hSprev, hTprev⟩
      have hsymm_not := rep_not_symm_of_rep d h
      have hd_ne_symm : ¬ d = d.symm := fun hd => (SimpleGraph.Dart.symm_ne d) hd.symm
      have hST' :
          (pairS (dartEdge d)).rightStrip = (pairT (dartEdge d.symm)).leftStrip := by
        rw [dartEdge_symm d]
        exact hST
      simpa [sideStrips, h, hsymm_not, hd_ne_symm, dartEdge_symm d, stripOfEq] using hST'
    · rcases pairSpec (dartEdge d) with
        ⟨hST, hTS, hSnon, hTnon, hScomp, hTcomp, hSlocal, hTlocal,
          hSterm, hTterm, hSprev, hTprev⟩
      have ha_symm := rep_symm_of_not d h
      have ha_eq_dsymm := rep_eq_symm_of_symm d ha_symm
      have hsymm_ne : ¬ d.symm = d := SimpleGraph.Dart.symm_ne d
      have hTS' :
          (pairT (dartEdge d)).rightStrip = (pairS (dartEdge d.symm)).leftStrip := by
        rw [dartEdge_symm d]
        exact hTS
      simpa [sideStrips, h, ha_symm, ha_eq_dsymm, hsymm_ne, dartEdge_symm d, stripOfEq] using hTS'
  · intro d
    by_cases h : edgeRep (dartEdge d) = d
    · rcases pairSpec (dartEdge d) with
        ⟨hST, hTS, hSnon, hTnon, hScomp, hTcomp, hSlocal, hTlocal,
          hSterm, hTterm, hSprev, hTprev⟩
      simpa [sideStrips, h, stripOfEq] using hSterm
    · rcases pairSpec (dartEdge d) with
        ⟨hST, hTS, hSnon, hTnon, hScomp, hTcomp, hSlocal, hTlocal,
          hSterm, hTterm, hSprev, hTprev⟩
      have ha_symm := rep_symm_of_not d h
      simpa [sideStrips, h, ha_symm, stripOfEq] using hTterm
  · intro d
    let s : G.Dart := C.star.successor d
    by_cases h : edgeRep (dartEdge s) = s
    · rcases pairSpec (dartEdge s) with
        ⟨hST, hTS, hSnon, hTnon, hScomp, hTcomp, hSlocal, hTlocal,
          hSterm, hTterm, hSprev, hTprev⟩
      have hs : C.star.successor d = edgeRep (dartEdge s) := by
        simpa [s] using h.symm
      simpa [s, sideStrips, h, stripOfEq] using hSprev d hs
    · rcases pairSpec (dartEdge s) with
        ⟨hST, hTS, hSnon, hTnon, hScomp, hTcomp, hSlocal, hTlocal,
          hSterm, hTterm, hSprev, hTprev⟩
      have ha_symm := rep_symm_of_not s h
      have hs : C.star.successor d = (edgeRep (dartEdge s)).symm := by
        simpa [s] using ha_symm.symm
      simpa [s, sideStrips, h, ha_symm, stripOfEq] using hTprev d hs
