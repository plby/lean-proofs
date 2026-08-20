import Mathlib.Data.Set.Card.Arithmetic
import ErdosProblems.Erdos733.ST.FinitePolygonalSetListedSegmentsCoveredByCyclicPieces

open Classical
noncomputable section

-- [TABLET NODE: FinitePolygonalSetOpenIntersectionPartition]
lemma FinitePolygonalSetOpenIntersectionPartition
    (J : SimpleClosedPolygonalCurve) (K : FinitePolygonalSet)
    (hKJ : K.carrier = J.carrier)
    (D : FinitePolygonalSetCyclicTraversalCuts J K) :
    ∀ a b : EuclideanSpace ℝ (Fin 2),
      (∀ v : EuclideanSpace ℝ (Fin 2), v ∈ K.points →
          v ∉ openSegment ℝ a b) →
        (∀ s : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
          s ∈ K.segments →
            ¬ ∃ p q : EuclideanSpace ℝ (Fin 2),
              p ≠ q ∧ segment ℝ p q ⊆ segment ℝ a b ∩ segment ℝ s.1 s.2) →
        K.segments.sum (fun s =>
          Set.ncard (openSegment ℝ a b ∩ openSegment ℝ s.1 s.2)) =
          K.points.attach.sum fun p =>
            Set.ncard (openSegment ℝ a b ∩ openSegment ℝ p.1 (D.successor p).1) := by
-- BODY
  intro a b havoid hoverlap
  rcases FinitePolygonalSetCyclicSuccessorPiecesContained J K hKJ D with
    ⟨_hcarrier, hrefine, _harcCarrier, _hopen_subset, _hno_listed_open,
      hopen_disjoint⟩
  let Aseg :
      EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) →
        Set (EuclideanSpace ℝ (Fin 2)) :=
    fun s => openSegment ℝ a b ∩ openSegment ℝ s.1 s.2
  let Apiece :
      {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points} →
        Set (EuclideanSpace ℝ (Fin 2)) :=
    fun p => openSegment ℝ a b ∩ openSegment ℝ p.1 (D.successor p).1
  have hsegCover := FinitePolygonalSetListedSegmentsCoveredByCyclicPieces J K hKJ D
  have hAseg_finite :
      ∀ s ∈ (K.segments :
          Set (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2))),
        (Aseg s).Finite := by
    intro s hs
    by_cases hnonempty : (Aseg s).Nonempty
    · rcases hnonempty with ⟨x, hx⟩
      refine (Set.finite_singleton x).subset ?_
      intro y hy
      have hyx : y = x := by
        by_contra hyx_ne
        have hsub :
            segment ℝ y x ⊆ segment ℝ a b ∩ segment ℝ s.1 s.2 := by
          intro z hz
          exact
            ⟨(convex_segment (𝕜 := ℝ) a b).segment_subset
                (openSegment_subset_segment ℝ a b hy.1)
                (openSegment_subset_segment ℝ a b hx.1) hz,
              (convex_segment (𝕜 := ℝ) s.1 s.2).segment_subset
                (openSegment_subset_segment ℝ s.1 s.2 hy.2)
                (openSegment_subset_segment ℝ s.1 s.2 hx.2) hz⟩
        exact hoverlap s hs ⟨y, x, hyx_ne, hsub⟩
      · simp [hyx]
    · rw [Set.not_nonempty_iff_eq_empty] at hnonempty
      rw [hnonempty]
      exact Set.finite_empty
  have hApiece_finite :
      ∀ p ∈ (K.points.attach :
          Set {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points}),
        (Apiece p).Finite := by
    intro p _hp
    rcases hrefine p with ⟨s, hs, hpsub⟩
    exact (hAseg_finite s hs).subset (by
      intro z hz
      have hzseg : z ∈ segment ℝ s.1 s.2 :=
        hpsub (openSegment_subset_segment ℝ p.1 (D.successor p).1 hz.2)
      have hendpoints := K.segment_endpoints_listed s hs
      have hleft : s.1 ≠ z := by
        intro h
        exact havoid s.1 hendpoints.1 (by simpa [h] using hz.1)
      have hright : s.2 ≠ z := by
        intro h
        exact havoid s.2 hendpoints.2 (by simpa [h] using hz.1)
      exact ⟨hz.1, mem_openSegment_of_ne_left_right hleft hright hzseg⟩)
  have hAseg_pairwise :
      (K.segments :
          Set (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2))).PairwiseDisjoint
        Aseg := by
    intro s hs t ht hst
    change Disjoint (Aseg s) (Aseg t)
    rw [Set.disjoint_left]
    intro z hzS hzT
    exact havoid z
      (K.segment_intersections_listed s t hs ht hst z
        (openSegment_subset_segment ℝ s.1 s.2 hzS.2)
        (openSegment_subset_segment ℝ t.1 t.2 hzT.2))
      hzS.1
  have hApiece_pairwise :
      (K.points.attach :
          Set {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points}).PairwiseDisjoint
        Apiece := by
    intro p _hp q _hq hpq
    exact (hopen_disjoint p q hpq).mono Set.inter_subset_right Set.inter_subset_right
  have hunion :
      (⋃ s ∈ (K.segments :
          Set (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2))), Aseg s) =
        ⋃ p ∈ (K.points.attach :
          Set {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points}), Apiece p := by
    ext z
    constructor
    · intro hz
      rcases Set.mem_iUnion.mp hz with ⟨s, hz⟩
      rcases Set.mem_iUnion.mp hz with ⟨hs, hzA⟩
      have hzseg : z ∈ segment ℝ s.1 s.2 :=
        openSegment_subset_segment ℝ s.1 s.2 hzA.2
      have hzUnion :
          z ∈
            ⋃ q : {q : {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points} //
                segment ℝ q.1 (D.successor q).1 ⊆ segment ℝ s.1 s.2},
              segment ℝ q.1.1 (D.successor q.1).1 := by
        simpa [hsegCover s hs] using hzseg
      rcases Set.mem_iUnion.mp hzUnion with ⟨q, hzq⟩
      have hleft : q.1.1 ≠ z := by
        intro h
        exact havoid q.1.1 q.1.2 (by simpa [h] using hzA.1)
      have hright : (D.successor q.1).1 ≠ z := by
        intro h
        exact havoid (D.successor q.1).1 (D.successor q.1).2
          (by simpa [h] using hzA.1)
      have hzopen :
          z ∈ openSegment ℝ q.1.1 (D.successor q.1).1 :=
        mem_openSegment_of_ne_left_right hleft hright hzq
      refine Set.mem_iUnion.2 ⟨q.1, ?_⟩
      refine Set.mem_iUnion.2 ⟨by simp, ?_⟩
      exact ⟨hzA.1, hzopen⟩
    · intro hz
      rcases Set.mem_iUnion.mp hz with ⟨p, hz⟩
      rcases Set.mem_iUnion.mp hz with ⟨_hp, hzA⟩
      rcases hrefine p with ⟨s, hs, hpsub⟩
      have hzseg : z ∈ segment ℝ s.1 s.2 :=
        hpsub (openSegment_subset_segment ℝ p.1 (D.successor p).1 hzA.2)
      have hendpoints := K.segment_endpoints_listed s hs
      have hleft : s.1 ≠ z := by
        intro h
        exact havoid s.1 hendpoints.1 (by simpa [h] using hzA.1)
      have hright : s.2 ≠ z := by
        intro h
        exact havoid s.2 hendpoints.2 (by simpa [h] using hzA.1)
      have hzopen : z ∈ openSegment ℝ s.1 s.2 :=
        mem_openSegment_of_ne_left_right hleft hright hzseg
      refine Set.mem_iUnion.2 ⟨s, ?_⟩
      refine Set.mem_iUnion.2 ⟨hs, ?_⟩
      exact ⟨hzA.1, hzopen⟩
  have hleft_sum :
      K.segments.sum (fun s => (Aseg s).ncard) =
        (⋃ s ∈ (K.segments :
          Set (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2))), Aseg s).ncard := by
    have hcard :=
      (K.segments.finite_toSet).ncard_biUnion hAseg_finite hAseg_pairwise
    rw [hcard]
    rw [finsum_mem_eq_finite_toFinset_sum _ K.segments.finite_toSet]
    rw [Finset.finite_toSet_toFinset]
  have hright_sum :
      K.points.attach.sum (fun p => (Apiece p).ncard) =
        (⋃ p ∈ (K.points.attach :
          Set {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points}), Apiece p).ncard := by
    have hcard :=
      (K.points.attach.finite_toSet).ncard_biUnion hApiece_finite hApiece_pairwise
    rw [hcard]
    rw [finsum_mem_eq_finite_toFinset_sum _ K.points.attach.finite_toSet]
    rw [Finset.finite_toSet_toFinset]
  calc
    K.segments.sum (fun s =>
        Set.ncard (openSegment ℝ a b ∩ openSegment ℝ s.1 s.2))
        = K.segments.sum (fun s => (Aseg s).ncard) := by
          simp [Aseg]
    _ = (⋃ s ∈ (K.segments :
          Set (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2))), Aseg s).ncard :=
          hleft_sum
    _ = (⋃ p ∈ (K.points.attach :
          Set {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points}), Apiece p).ncard := by
          rw [hunion]
    _ = K.points.attach.sum (fun p => (Apiece p).ncard) := hright_sum.symm
    _ = K.points.attach.sum fun p =>
          Set.ncard (openSegment ℝ a b ∩ openSegment ℝ p.1 (D.successor p).1) := by
          simp [Apiece]
