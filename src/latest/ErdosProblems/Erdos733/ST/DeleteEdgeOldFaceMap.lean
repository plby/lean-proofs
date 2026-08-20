import ErdosProblems.Erdos733.ST.PlaneFaceData
import ErdosProblems.Erdos733.ST.DrawingFaceComponent
import ErdosProblems.Erdos733.ST.ComplementComponent
import ErdosProblems.Erdos733.ST.OrdinaryDrawingImage
import Mathlib.Combinatorics.SimpleGraph.Acyclic

open Classical
noncomputable section

-- [TABLET NODE: DeleteEdgeOldFaceMap]
lemma DeleteEdgeOldFaceMap {V : Type*} [Fintype V] (G : SimpleGraph V)
    [Fintype G.edgeSet] [DecidableRel G.Adj] (D : OrdinaryPolygonalDrawing G)
    (A : PlaneFaceData G D) (e : G.edgeFinset) :
    let Gdel : SimpleGraph V := G.deleteEdges {e.1}
    ∀ (Ddel : OrdinaryPolygonalDrawing Gdel) (Adel : PlaneFaceData Gdel Ddel),
      Ddel.vertexPlacement = D.vertexPlacement →
        (∀ ed : Gdel.edgeFinset,
          ∃ eG : G.edgeFinset, eG.1 = ed.1 ∧ eG.1 ≠ e.1 ∧
            Ddel.edgeArc ed = D.edgeArc eG) →
          ∃ oldToNew : A.Face → Adel.Face,
            ∀ F : A.Face, A.faceSet F ⊆ Adel.faceSet (oldToNew F) := by
-- BODY
  dsimp
  intro Ddel Adel hvertex hedge
  have hImageSubset :
      OrdinaryDrawingImage (G.deleteEdges {e.1}) Ddel ⊆ OrdinaryDrawingImage G D := by
    intro x hx
    rw [OrdinaryDrawingImage] at hx ⊢
    rcases hx with hxv | hxe
    · left
      rcases hxv with ⟨v, rfl⟩
      exact ⟨v, by rw [hvertex]⟩
    · right
      rcases Set.mem_iUnion.mp hxe with ⟨ed, hxed⟩
      rcases hedge ed with ⟨eG, _heq, _hne, hArc⟩
      exact Set.mem_iUnion.mpr ⟨eG, by simpa [hArc] using hxed⟩
  have hOldComponent :
      ∀ F : A.Face, ComplementComponent (OrdinaryDrawingImage G D) (A.faceSet F) := by
    intro F
    simpa [DrawingFaceComponent] using A.face_component F
  have hOldNonempty : ∀ F : A.Face, (A.faceSet F).Nonempty := fun F =>
    (hOldComponent F).1
  have hOldSubset :
      ∀ F : A.Face, A.faceSet F ⊆ (OrdinaryDrawingImage G D)ᶜ := fun F =>
    (hOldComponent F).2.1
  have hOldConnected : ∀ F : A.Face, IsConnected (A.faceSet F) := fun F =>
    (hOldComponent F).2.2.1
  let p : A.Face → EuclideanSpace ℝ (Fin 2) := fun F =>
    Classical.choose (hOldNonempty F)
  have hpOld : ∀ F : A.Face, p F ∈ A.faceSet F := fun F =>
    Classical.choose_spec (hOldNonempty F)
  have hpNewComplement :
      ∀ F : A.Face, p F ∈ (OrdinaryDrawingImage (G.deleteEdges {e.1}) Ddel)ᶜ := by
    intro F hpNew
    exact (hOldSubset F (hpOld F)) (hImageSubset hpNew)
  have hFaceExists :
      ∀ F : A.Face, ∃ Q : Adel.Face, p F ∈ Adel.faceSet Q := by
    intro F
    rcases Adel.complement_point_face (p F) (hpNewComplement F) with
      ⟨Q, hQ, _hQuniq⟩
    exact ⟨Q, hQ⟩
  choose oldToNew hOldToNew using hFaceExists
  refine ⟨oldToNew, ?_⟩
  intro F x hxF
  have hNewComponent :
      ComplementComponent (OrdinaryDrawingImage (G.deleteEdges {e.1}) Ddel)
        (Adel.faceSet (oldToNew F)) := by
    simpa [DrawingFaceComponent] using Adel.face_component (oldToNew F)
  rcases hNewComponent with ⟨_hNewNonempty, hNewSubset, hNewConnected, hNewMaximal⟩
  have hOldSubsetNew :
      A.faceSet F ⊆ (OrdinaryDrawingImage (G.deleteEdges {e.1}) Ddel)ᶜ := by
    intro y hy hyImage
    exact (hOldSubset F hy) (hImageSubset hyImage)
  have hMeet : (Adel.faceSet (oldToNew F) ∩ A.faceSet F).Nonempty :=
    ⟨p F, hOldToNew F, hpOld F⟩
  have hUnionConnected : IsConnected (Adel.faceSet (oldToNew F) ∪ A.faceSet F) :=
    IsConnected.union hMeet hNewConnected (hOldConnected F)
  have hUnionSubsetComplement :
      Adel.faceSet (oldToNew F) ∪ A.faceSet F ⊆
        (OrdinaryDrawingImage (G.deleteEdges {e.1}) Ddel)ᶜ := by
    intro y hy
    rcases hy with hyNew | hyOld
    · exact hNewSubset hyNew
    · exact hOldSubsetNew hyOld
  have hUnionNonempty : (Adel.faceSet (oldToNew F) ∪ A.faceSet F).Nonempty :=
    ⟨p F, Or.inl (hOldToNew F)⟩
  have hNewSubsetUnion :
      Adel.faceSet (oldToNew F) ⊆ Adel.faceSet (oldToNew F) ∪ A.faceSet F := by
    intro y hy
    exact Or.inl hy
  have hUnionSubsetNew :
      Adel.faceSet (oldToNew F) ∪ A.faceSet F ⊆ Adel.faceSet (oldToNew F) :=
    hNewMaximal (Adel.faceSet (oldToNew F) ∪ A.faceSet F)
      hUnionNonempty hUnionSubsetComplement hUnionConnected hNewSubsetUnion
  exact hUnionSubsetNew (Or.inr hxF)
