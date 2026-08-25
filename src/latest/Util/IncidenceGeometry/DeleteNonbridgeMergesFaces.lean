import Util.IncidenceGeometry.DeleteEdgeInheritedFaceData
import Util.IncidenceGeometry.DeleteEdgeOldFaceMap
import Util.IncidenceGeometry.DeleteEdgeOldFaceMapTwoFaceQuotient
import Util.IncidenceGeometry.DeleteNonbridgeSideFacesDistinct
import Util.IncidenceGeometry.PlaneFaceData
import Util.IncidenceGeometry.DrawingFaceComponent
import Util.IncidenceGeometry.PolygonalArcCollar
import Util.IncidenceGeometry.PolygonalJordanSeparation
import Util.IncidenceGeometry.FinitePolygonalPerturbation
import Util.IncidenceGeometry.OpenConnectedComponentPolygonallyConnected
import Util.IncidenceGeometry.OrdinaryDrawingImageCompact
import Mathlib.Combinatorics.SimpleGraph.Acyclic

open Classical
noncomputable section

lemma DeleteNonbridgeMergesFaces {V : Type*} [Fintype V] (G : SimpleGraph V)
    [Fintype G.edgeSet] [DecidableRel G.Adj] (D : OrdinaryPolygonalDrawing G)
    (hD : D.crossingSet.card = 0) (A : PlaneFaceData G D) (e : G.edgeFinset)
    (hconn : G.Connected) (he : ¬ G.IsBridge e.1) :
    let Gdel : SimpleGraph V := G.deleteEdges {e.1}
    ∃ Ddel : OrdinaryPolygonalDrawing Gdel,
      Ddel.crossingSet.card = 0 ∧
        Ddel.vertexPlacement = D.vertexPlacement ∧
          (∀ ed : Gdel.edgeFinset,
            ∃ eG : G.edgeFinset, eG.1 = ed.1 ∧ eG.1 ≠ e.1 ∧
              Ddel.edgeArc ed = D.edgeArc eG) ∧
            ∃ Adel : PlaneFaceData Gdel Ddel,
              ∃ d : G.Dart,
                d.edge = e.1 ∧
                  A.leftFace d ≠ A.leftFace d.symm ∧
                    ∃ oldToNew : A.Face → Adel.Face,
                      (∀ F : A.Face, A.faceSet F ⊆ Adel.faceSet (oldToNew F)) ∧
                        oldToNew (A.leftFace d) = oldToNew (A.leftFace d.symm) ∧
                          (D.edgeArc e).relativeInterior ⊆
                            Adel.faceSet (oldToNew (A.leftFace d)) ∧
                            (∀ F F' : A.Face,
                              oldToNew F = oldToNew F' ↔
                                F = F' ∨
                                  (F = A.leftFace d ∧ F' = A.leftFace d.symm) ∨
                                    (F = A.leftFace d.symm ∧ F' = A.leftFace d)) ∧
                              (∀ F : A.Face,
                                F ≠ A.leftFace d → F ≠ A.leftFace d.symm →
                                  Adel.faceSet (oldToNew F) = A.faceSet F) ∧
                                (∀ Fdel : Adel.Face, ∃ F : A.Face,
                                  oldToNew F = Fdel) ∧
                                  @Fintype.card Adel.Face Adel.faceFintype + 1 =
                                    @Fintype.card A.Face A.faceFintype := by
  classical
  dsimp
  rcases DeleteEdgeInheritedFaceData G D hD A e with
    ⟨Ddel, Adel, hDdel, hvertex, hedges⟩
  refine ⟨Ddel, hDdel, hvertex, hedges, ?_⟩
  refine ⟨Adel, ?_⟩
  rcases DeleteNonbridgeSideFacesDistinct G D hD A e hconn he with
    ⟨d, hd, hdistinct⟩
  refine ⟨d, hd, hdistinct, ?_⟩
  rcases
    DeleteEdgeOldFaceMapTwoFaceQuotient G D hD A e Ddel Adel hvertex hedges d hd
      hdistinct with
    ⟨oldToNew, hcontain, hmerge, hrel, hiff, hunchanged, hsurj, hcard⟩
  exact ⟨oldToNew, hcontain, hmerge, hrel, hiff, hunchanged, hsurj, hcard⟩
