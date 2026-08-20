import ErdosProblems.Erdos733.ST.ComplementComponent
import ErdosProblems.Erdos733.ST.SimpleClosedCurveAsFinitePolygonalSet
import ErdosProblems.Erdos733.ST.FiniteStraightLineComplexCarrierCompact
import ErdosProblems.Erdos733.ST.EuclideanPlaneClosedBallExteriorConnected

open Classical
noncomputable section

-- [TABLET NODE: JordanUnboundedComplementComponentUnique]
lemma JordanUnboundedComplementComponentUnique
    (J : SimpleClosedPolygonalCurve)
    (F G : Set (EuclideanSpace ℝ (Fin 2))) :
    ComplementComponent J.carrier F →
      ComplementComponent J.carrier G →
        ¬ Bornology.IsBounded F →
          ¬ Bornology.IsBounded G →
            F = G := by
-- BODY
  rintro ⟨hFne, hFsub, hFconn, hFmax⟩
    ⟨hGne, hGsub, hGconn, hGmax⟩ hFunbounded hGunbounded
  obtain ⟨K, hK⟩ := SimpleClosedCurveAsFinitePolygonalSet J
  have hJbounded : Bornology.IsBounded J.carrier := by
    rw [← hK]
    exact
      (FiniteStraightLineComplexCarrierCompact
        K.carrier K.points K.segments K.carrier_eq).isBounded
  obtain ⟨R, hRpos, hJR⟩ := hJbounded.subset_closedBall_lt 0 0
  let E : Set (EuclideanSpace ℝ (Fin 2)) :=
    (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) R)ᶜ
  have hEne : E.Nonempty := by
    exact (EuclideanPlaneClosedBallExteriorConnected R hRpos.le).nonempty
  have hEconn : IsConnected E :=
    EuclideanPlaneClosedBallExteriorConnected R hRpos.le
  have hEsub : E ⊆ J.carrierᶜ := by
    dsimp [E]
    exact Set.compl_subset_compl.mpr hJR
  have hFE : (F ∩ E).Nonempty := by
    by_contra hFE
    apply hFunbounded
    apply Metric.isBounded_closedBall.subset
    intro x hxF
    by_contra hxR
    apply hFE
    refine ⟨x, hxF, ?_⟩
    exact hxR
  have hGE : (G ∩ E).Nonempty := by
    by_contra hGE
    apply hGunbounded
    apply Metric.isBounded_closedBall.subset
    intro x hxG
    by_contra hxR
    apply hGE
    refine ⟨x, hxG, ?_⟩
    exact hxR
  have hEsubF : E ⊆ F := by
    have hUnionSub : F ∪ E ⊆ F :=
      hFmax (F ∪ E)
        (hFne.mono Set.subset_union_left)
        (Set.union_subset hFsub hEsub)
        (IsConnected.union hFE hFconn hEconn)
        Set.subset_union_left
    exact Set.subset_union_right.trans hUnionSub
  have hEsubG : E ⊆ G := by
    have hUnionSub : G ∪ E ⊆ G :=
      hGmax (G ∪ E)
        (hGne.mono Set.subset_union_left)
        (Set.union_subset hGsub hEsub)
        (IsConnected.union hGE hGconn hEconn)
        Set.subset_union_left
    exact Set.subset_union_right.trans hUnionSub
  have hFG : (F ∩ G).Nonempty := by
    rcases hEne with ⟨z, hz⟩
    exact ⟨z, hEsubF hz, hEsubG hz⟩
  have hUnionConn : IsConnected (F ∪ G) :=
    IsConnected.union hFG hFconn hGconn
  apply Set.Subset.antisymm
  · exact Set.subset_union_left.trans
      (hGmax (F ∪ G)
        (hFne.mono Set.subset_union_left)
        (Set.union_subset hFsub hGsub)
        hUnionConn Set.subset_union_right)
  · exact Set.subset_union_right.trans
      (hFmax (F ∪ G)
        (hFne.mono Set.subset_union_left)
        (Set.union_subset hFsub hGsub)
        hUnionConn Set.subset_union_left)
