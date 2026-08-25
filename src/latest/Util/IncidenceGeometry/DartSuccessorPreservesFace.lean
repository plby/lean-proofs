import Util.IncidenceGeometry.PlaneFaceData

open Classical
noncomputable section

lemma DartSuccessorPreservesFace {V : Type*} [Fintype V] (G : SimpleGraph V)
    [Fintype G.edgeSet] [DecidableRel G.Adj] (D : OrdinaryPolygonalDrawing G)
    (hD : D.crossingSet.card = 0) (A : PlaneFaceData G D) :
    (∀ d : G.Dart, A.leftFace (A.successor d) = A.leftFace d) ∧
      ∀ F : A.Face, ∀ d : G.Dart, A.leftFace d = F →
        (∀ n : ℕ, A.leftFace ((A.successor^[n]) d) = F) ∧
          ∀ n : ℕ, A.leftFace (((A.successor.symm)^[n]) d) = F := by
  have _hD : D.crossingSet.card = 0 := hD
  have successorFace : ∀ d : G.Dart, A.leftFace (A.successor d) = A.leftFace d := by
    intro d
    rcases A.successor_clockwise_sector d with
      ⟨sector, _hsectorOpen, hsectorConn, _hsectorBall, hsectorSubCompl,
        hsectorLeft, hsectorSuccLeft, _hsectorDisjoint⟩
    rcases hsectorLeft with ⟨z, ⟨⟨hzSector, hzLeft⟩, _hzBall⟩⟩
    rcases hsectorSuccLeft with ⟨w, ⟨⟨hwSector, hwLeft⟩, _hwBall⟩⟩
    have hFaceComp :
        ComplementComponent (OrdinaryDrawingImage G D)
          (A.faceSet (A.leftFace d)) := by
      simpa [DrawingFaceComponent] using A.face_component (A.leftFace d)
    rcases hFaceComp with
      ⟨hFaceNonempty, hFaceSubCompl, hFaceConn, hFaceMax⟩
    have hzFace : z ∈ A.faceSet (A.leftFace d) :=
      A.leftFace_contains d hzLeft
    have hUnionInter :
        (A.faceSet (A.leftFace d) ∩ sector).Nonempty :=
      ⟨z, hzFace, hzSector⟩
    have hUnionConn :
        IsConnected (A.faceSet (A.leftFace d) ∪ sector) :=
      hFaceConn.union hUnionInter hsectorConn
    have hFaceSubUnion :
        A.faceSet (A.leftFace d) ⊆ A.faceSet (A.leftFace d) ∪ sector := by
      intro x hx
      exact Or.inl hx
    have hUnionSubCompl :
        A.faceSet (A.leftFace d) ∪ sector ⊆ (OrdinaryDrawingImage G D)ᶜ := by
      intro x hx
      rcases hx with hxFace | hxSector
      · exact hFaceSubCompl hxFace
      · exact hsectorSubCompl hxSector
    have hUnionSubFace :
        A.faceSet (A.leftFace d) ∪ sector ⊆ A.faceSet (A.leftFace d) :=
      hFaceMax (A.faceSet (A.leftFace d) ∪ sector)
        (hFaceNonempty.mono hFaceSubUnion) hUnionSubCompl hUnionConn hFaceSubUnion
    have hwFaceD : w ∈ A.faceSet (A.leftFace d) :=
      hUnionSubFace (Or.inr hwSector)
    have hwFaceSucc : w ∈ A.faceSet (A.leftFace (A.successor d)) :=
      A.leftFace_contains (A.successor d) hwLeft
    have hwCompl : w ∈ (OrdinaryDrawingImage G D)ᶜ :=
      hsectorSubCompl hwSector
    rcases A.complement_point_face w hwCompl with ⟨F, _hFmem, hFuniq⟩
    exact (hFuniq (A.leftFace (A.successor d)) hwFaceSucc).trans
      (hFuniq (A.leftFace d) hwFaceD).symm
  refine ⟨successorFace, ?_⟩
  intro F d hleft
  have predecessorFace : ∀ e : G.Dart,
      A.leftFace (A.successor.symm e) = A.leftFace e := by
    intro e
    have h := successorFace (A.successor.symm e)
    simpa using h.symm
  constructor
  · intro n
    induction n with
    | zero =>
        simpa using hleft
    | succ n ih =>
        rw [Function.iterate_succ_apply']
        exact (successorFace ((A.successor^[n]) d)).trans ih
  · intro n
    induction n with
    | zero =>
        simpa using hleft
    | succ n ih =>
        rw [Function.iterate_succ_apply']
        exact (predecessorFace (((A.successor.symm)^[n]) d)).trans ih
