import ErdosProblems.Erdos733.ST.FinitePolygonalSetCyclicSuccessorPiecesContained
import ErdosProblems.Erdos733.ST.SegmentFiniteSetComplementDense

open Classical
noncomputable section

-- [TABLET NODE: FinitePolygonalSetListedSegmentsCoveredByCyclicPieces]
lemma FinitePolygonalSetListedSegmentsCoveredByCyclicPieces
    (J : SimpleClosedPolygonalCurve) (K : FinitePolygonalSet)
    (hKJ : K.carrier = J.carrier)
    (D : FinitePolygonalSetCyclicTraversalCuts J K) :
    ∀ s : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
      s ∈ K.segments →
        segment ℝ s.1 s.2 =
          ⋃ q : {q : {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points} //
              segment ℝ q.1 (D.successor q).1 ⊆ segment ℝ s.1 s.2},
            segment ℝ q.1.1 (D.successor q.1).1 := by
-- BODY
  intro s hs
  rcases FinitePolygonalSetCyclicSuccessorPiecesContained J K hKJ D with
    ⟨hcarrier, hrefine, _harcCarrier, _hopen_subset, _hno_listed_open,
      _hopen_disjoint⟩
  let U : Set (EuclideanSpace ℝ (Fin 2)) :=
    ⋃ q : {q : {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points} //
        segment ℝ q.1 (D.successor q).1 ⊆ segment ℝ s.1 s.2},
      segment ℝ q.1.1 (D.successor q.1).1
  have hU_def :
      U =
        ⋃ q : {q : {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points} //
            segment ℝ q.1 (D.successor q).1 ⊆ segment ℝ s.1 s.2},
          segment ℝ q.1.1 (D.successor q.1).1 := rfl
  have hclosed_segment :
      ∀ a b : EuclideanSpace ℝ (Fin 2), IsClosed (segment ℝ a b) := by
    intro a b
    rw [segment_eq_image_lineMap]
    exact (isCompact_Icc.image AffineMap.lineMap_continuous).isClosed
  have hU_closed : IsClosed U := by
    rw [hU_def]
    exact isClosed_iUnion_of_finite fun q => hclosed_segment q.1.1 (D.successor q.1).1
  apply le_antisymm
  · intro z hzseg
    have hnonlisted_subset :
        segment ℝ s.1 s.2 \ (K.points : Set (EuclideanSpace ℝ (Fin 2))) ⊆ U := by
      intro w hw
      rcases hw with ⟨hwseg, hwnot⟩
      have hwK : w ∈ K.carrier := by
        rw [K.carrier_eq]
        exact Or.inr (Set.mem_iUnion.2 ⟨⟨s, hs⟩, hwseg⟩)
      have hwJ : w ∈ J.carrier := by
        simpa [hKJ] using hwK
      have hwUnion :
          w ∈
            ⋃ p : {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points},
              segment ℝ p.1 (D.successor p).1 := by
        simpa [hcarrier] using hwJ
      rcases Set.mem_iUnion.mp hwUnion with ⟨p, hwp⟩
      rcases hrefine p with ⟨t, ht, hpt⟩
      have ht_eq : t = s := by
        by_contra hts
        have hst : s ≠ t := by
          intro hst
          exact hts hst.symm
        exact hwnot (K.segment_intersections_listed s t hs ht hst w hwseg (hpt hwp))
      have hp_subset : segment ℝ p.1 (D.successor p).1 ⊆ segment ℝ s.1 s.2 := by
        simpa [ht_eq] using hpt
      rw [hU_def]
      exact Set.mem_iUnion.2 ⟨⟨p, hp_subset⟩, hwp⟩
    have hz_closure :
        z ∈ closure U :=
      closure_mono hnonlisted_subset
        (SegmentFiniteSetComplementDense s.1 s.2 K.points
          (K.segment_nondegenerate s hs) hzseg)
    have hzU : z ∈ U := by
      simpa [hU_closed.closure_eq] using hz_closure
    simpa [hU_def] using hzU
  · intro z hzU
    rcases Set.mem_iUnion.mp hzU with ⟨q, hzq⟩
    exact q.2 hzq
