import Util.IncidenceGeometry.FinitePolygonalSetCyclicOrderedPieceCoveredByListedSegments
import Mathlib.Topology.Connected.Clopen

open Classical
noncomputable section

lemma FinitePolygonalSetCyclicOrderedPieceContainedInListedSegment
    (J : SimpleClosedPolygonalCurve) (K : FinitePolygonalSet)
    (hKJ : K.carrier = J.carrier)
    (D : FinitePolygonalSetCyclicTraversalCuts J K)
    (p : {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points})
    (i : D.pieceIndex) (hi : i ∈ D.arcPieceOrder p) :
    ∃ s : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
      s ∈ K.segments ∧ D.pieceCarrier i ⊆ segment ℝ s.1 s.2 := by
  let a : EuclideanSpace ℝ (Fin 2) := D.pieceSource i
  let b : EuclideanSpace ℝ (Fin 2) := D.pieceTarget i
  have hPieceCovered :
      D.pieceCarrier i ⊆
        ⋃ s : {s // s ∈ K.segments}, segment ℝ s.1.1 s.1.2 :=
    FinitePolygonalSetCyclicOrderedPieceCoveredByListedSegments J K hKJ D p i hi
  have hpiece_eq : D.pieceCarrier i = segment ℝ a b := by
    simpa [a, b] using D.pieceCarrier_eq i
  have hclosed_segment :
      ∀ x y : EuclideanSpace ℝ (Fin 2), IsClosed (segment ℝ x y) := by
    intro x y
    rw [segment_eq_image_lineMap]
    exact (isCompact_Icc.image AffineMap.lineMap_continuous).isClosed
  let m : EuclideanSpace ℝ (Fin 2) := midpoint ℝ a b
  have hm_open : m ∈ openSegment ℝ a b := by
    simpa [m] using midpoint_mem_openSegment (𝕜 := ℝ) a b
  have hm_piece : m ∈ D.pieceCarrier i := by
    rw [hpiece_eq]
    exact openSegment_subset_segment ℝ a b hm_open
  have hm_union := hPieceCovered hm_piece
  rcases Set.mem_iUnion.mp hm_union with ⟨s, hms⟩
  let V : Set (EuclideanSpace ℝ (Fin 2)) :=
    ⋃ t : {t : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) //
        t ∈ K.segments},
      if t.1 = s.1 then (∅ : Set (EuclideanSpace ℝ (Fin 2)))
      else segment ℝ t.1.1 t.1.2
  have hclosed_s : IsClosed (segment ℝ s.1.1 s.1.2) :=
    hclosed_segment s.1.1 s.1.2
  have hclosed_V : IsClosed V := by
    dsimp [V]
    exact isClosed_iUnion_of_finite fun t => by
      by_cases hts : t.1 = s.1
      · simp [hts]
      · simpa [hts] using hclosed_segment t.1.1 t.1.2
  have hm_arcInterior : m ∈ D.arcInterior p :=
    D.ordered_piece_open_subset_arcInterior p i hi hm_open
  have hm_not_listed : m ∉ K.points := by
    intro hmK
    exact D.no_listed_point_in_arcInterior p m hmK hm_arcInterior
  have hm_not_V : m ∉ V := by
    intro hmV
    rcases Set.mem_iUnion.mp hmV with ⟨t, hmt⟩
    by_cases hts : t.1 = s.1
    · simpa [V, hts] using hmt
    have hne : s.1 ≠ t.1 := by
      intro hst
      exact hts hst.symm
    have hmt' : m ∈ segment ℝ t.1.1 t.1.2 := by
      simpa [V, hts] using hmt
    exact hm_not_listed
      (K.segment_intersections_listed s.1 t.1 s.2 t.2 hne m hms hmt')
  have hopen_cover :
      openSegment ℝ a b ⊆ segment ℝ s.1.1 s.1.2 ∪ V := by
    intro x hx
    have hx_piece : x ∈ D.pieceCarrier i := by
      rw [hpiece_eq]
      exact openSegment_subset_segment ℝ a b hx
    rcases Set.mem_iUnion.mp (hPieceCovered hx_piece) with ⟨t, hxt⟩
    by_cases hts : t.1 = s.1
    · exact Or.inl (by simpa [hts] using hxt)
    · exact Or.inr (Set.mem_iUnion.2 ⟨t, by simpa [V, hts] using hxt⟩)
  have hinter_empty :
      openSegment ℝ a b ∩ (segment ℝ s.1.1 s.1.2 ∩ V) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.2
    intro x hx
    rcases hx with ⟨hxopen, hxs, hxV⟩
    rcases Set.mem_iUnion.mp hxV with ⟨t, hxt⟩
    by_cases hts : t.1 = s.1
    · simpa [V, hts] using hxt
    have hne : s.1 ≠ t.1 := by
      intro hst
      exact hts hst.symm
    have hxt' : x ∈ segment ℝ t.1.1 t.1.2 := by
      simpa [V, hts] using hxt
    have hx_listed : x ∈ K.points :=
      K.segment_intersections_listed s.1 t.1 s.2 t.2 hne x hxs hxt'
    exact D.no_listed_point_in_arcInterior p x hx_listed
      (D.ordered_piece_open_subset_arcInterior p i hi hxopen)
  have hopen_subset_s : openSegment ℝ a b ⊆ segment ℝ s.1.1 s.1.2 := by
    have hpre : IsPreconnected (openSegment ℝ a b) :=
      (convex_openSegment (𝕜 := ℝ) a b).isPreconnected
    rcases
        (isPreconnected_iff_subset_of_disjoint_closed.mp hpre
          (segment ℝ s.1.1 s.1.2) V hclosed_s hclosed_V
          hopen_cover hinter_empty) with hleft | hright
    · exact hleft
    · exact False.elim (hm_not_V (hright hm_open))
  have hclosed_piece :
      segment ℝ a b ⊆ segment ℝ s.1.1 s.1.2 := by
    intro x hx
    have hx_closure : x ∈ closure (openSegment ℝ a b) :=
      segment_subset_closure_openSegment hx
    have hx_closure_s : x ∈ closure (segment ℝ s.1.1 s.1.2) :=
      closure_mono hopen_subset_s hx_closure
    simpa [hclosed_s.closure_eq] using hx_closure_s
  refine ⟨s.1, s.2, ?_⟩
  intro x hx
  exact hclosed_piece (by simpa [hpiece_eq] using hx)
