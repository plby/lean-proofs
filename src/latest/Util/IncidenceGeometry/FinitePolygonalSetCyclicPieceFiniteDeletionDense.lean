import Util.IncidenceGeometry.FinitePolygonalSetCyclicTraversalCuts
import Util.IncidenceGeometry.SegmentFiniteSetComplementDense

open Classical
noncomputable section

lemma FinitePolygonalSetCyclicPieceFiniteDeletionDense
    (J : SimpleClosedPolygonalCurve) (K : FinitePolygonalSet)
    (D : FinitePolygonalSetCyclicTraversalCuts J K)
    (i : D.pieceIndex) :
    D.pieceCarrier i ⊆
      closure (D.pieceCarrier i \ (K.points : Set (EuclideanSpace ℝ (Fin 2)))) := by
  let γ : PolygonalArc := (D.pieceArc i).1
  let n : ℕ := (D.pieceSegmentIndex i).1
  have hn : n + 1 < γ.vertices.length := (D.pieceSegmentIndex i).2
  have hverts :
      γ.vertices[n]'(Nat.lt_of_succ_lt hn) ≠ γ.vertices[n + 1]'hn := by
    intro hv
    have hidx : n = n + 1 :=
      (γ.simple_vertices.getElem_inj_iff).mp hv
    omega
  have hne : D.pieceSource i ≠ D.pieceTarget i := by
    intro hst
    have hparam :
        (D.pieceSourceParam i).1 = (D.pieceTargetParam i).1 := by
      apply AffineMap.lineMap_injective ℝ hverts
      simpa [γ, n, D.pieceSource_eq i, D.pieceTarget_eq i] using hst
    have hlt := D.pieceSourceParam_lt_targetParam i
    have hsubeq : D.pieceSourceParam i = D.pieceTargetParam i := Subtype.ext hparam
    rw [← hsubeq] at hlt
    exact (lt_irrefl (D.pieceSourceParam i)) hlt
  rw [D.pieceCarrier_eq i]
  exact SegmentFiniteSetComplementDense (D.pieceSource i) (D.pieceTarget i)
    K.points hne
