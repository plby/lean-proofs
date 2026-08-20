import ErdosProblems.Erdos733.ST.ComplementComponent
import ErdosProblems.Erdos733.ST.ComplementComponentAbsorbsConnectedSubset
import ErdosProblems.Erdos733.ST.ComplementComponentDisjointUnionRight
import ErdosProblems.Erdos733.ST.ComplementComponentsFiniteHitFamily
import ErdosProblems.Erdos733.ST.ConnectedSubsetContainedInUniqueComplementComponent
import ErdosProblems.Erdos733.ST.FiniteConnectedIntersectionGrouping
import ErdosProblems.Erdos733.ST.FiniteStraightLineComplexCarrierCompact
import ErdosProblems.Erdos733.ST.OneEdgeEndpointNonincidentFeatureSeparation
import ErdosProblems.Erdos733.ST.OneEdgeEndpointRadiusRefinement
import ErdosProblems.Erdos733.ST.OneEdgeEndpointSectorComplementPackage
import ErdosProblems.Erdos733.ST.OneEdgeMiddleParametersFromEndpointRadii
import ErdosProblems.Erdos733.ST.OneEdgeMiddleOpenSegmentNeighborhood
import ErdosProblems.Erdos733.ST.OneEdgeGroupedLocalPieceHit
import ErdosProblems.Erdos733.ST.OneEdgeRawLocalFiniteCover
import ErdosProblems.Erdos733.ST.OneEdgeMiddleRectangleEndpointBallOverlaps
import ErdosProblems.Erdos733.ST.OneEdgeMiddleRectangleSidePieces
import ErdosProblems.Erdos733.ST.OneEdgeOldComponentBookkeeping
import ErdosProblems.Erdos733.ST.OpenConnectedComponentPolygonallyConnected
import ErdosProblems.Erdos733.ST.PolygonalPathOrderedFirstHitPrefix
import ErdosProblems.Erdos733.ST.PositiveSeparation

open Classical
noncomputable section

-- [TABLET NODE: FiniteStraightLineComplexOneEdgeComplementComponents]
lemma FiniteStraightLineComplexOneEdgeComplementComponents
    (A : Set (EuclideanSpace ℝ (Fin 2)))
    (V : Finset (EuclideanSpace ℝ (Fin 2)))
    (E : Finset (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)))
    (a b : EuclideanSpace ℝ (Fin 2))
    (hA :
      A =
        (V : Set (EuclideanSpace ℝ (Fin 2))) ∪
          ⋃ e : {e // e ∈ E}, segment ℝ e.1.1 e.1.2)
    (hEdgeSource :
      ∀ e : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
        e ∈ E → e.1 ∈ V)
    (hEdgeTarget :
      ∀ e : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
        e ∈ E → e.2 ∈ V)
    (hEdgeNondegenerate :
      ∀ e : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
        e ∈ E → e.1 ≠ e.2)
    (hNoVertexInEdgeInterior :
      ∀ e : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
        e ∈ E →
          ∀ v : EuclideanSpace ℝ (Fin 2),
            v ∈ V → v ∉ openSegment ℝ e.1 e.2)
    (hEdgeOpenInteriorsDisjoint :
      ∀ e f : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
        e ∈ E → f ∈ E → e ≠ f →
          Disjoint (openSegment ℝ e.1 e.2) (openSegment ℝ f.1 f.2))
    (haV : a ∈ V)
    (hbV : b ∈ V)
    (hab : a ≠ b)
    (hNewInteriorDisjoint : Disjoint (openSegment ℝ a b) A)
    (hFiniteA :
      ∃ comps : Finset (Set (EuclideanSpace ℝ (Fin 2))),
        (∀ C ∈ comps, ComplementComponent A C) ∧
          ∀ C : Set (EuclideanSpace ℝ (Fin 2)),
            ComplementComponent A C → C ∈ comps) :
    ∃ comps : Finset (Set (EuclideanSpace ℝ (Fin 2))),
      (∀ C ∈ comps, ComplementComponent (A ∪ segment ℝ a b) C) ∧
        ∀ C : Set (EuclideanSpace ℝ (Fin 2)),
          ComplementComponent (A ∪ segment ℝ a b) C → C ∈ comps := by
-- BODY
  have haA : a ∈ A := by
    rw [hA]
    exact Or.inl haV
  have hbA : b ∈ A := by
    rw [hA]
    exact Or.inl hbV
  rcases OneEdgeOldComponentBookkeeping A a b hab haA hbA hNewInteriorDisjoint with
    ⟨Csigma, hCsigma, hOpenSegment_Csigma, hUnique_Csigma, hOldComponentPersists⟩
  rcases OneEdgeEndpointNonincidentFeatureSeparation V E a
      hNoVertexInEdgeInterior haV with
    ⟨ρa, hρa_pos, hρa_vertices, hρa_nonincident_edges⟩
  have hNewInteriorDisjoint_symm : Disjoint (openSegment ℝ b a) A := by
    simpa [openSegment_symm] using hNewInteriorDisjoint
  rcases OneEdgeEndpointNonincidentFeatureSeparation V E b
      hNoVertexInEdgeInterior hbV with
    ⟨ρb, hρb_pos, hρb_vertices, hρb_nonincident_edges⟩
  rcases OneEdgeEndpointRadiusRefinement V E a b ρa ρb hab hρa_pos hρb_pos
      hρa_vertices hρa_nonincident_edges hρb_vertices hρb_nonincident_edges with
    ⟨ra, rb, hra_pos, hrb_pos, hra_le_ρa, hrb_le_ρb,
      hra_lt_third, hrb_lt_third, hradii_sum_lt,
      hra_vertices, hra_nonincident_edges, hrb_vertices, hrb_nonincident_edges⟩
  have hEndpointA_sectors :=
    OneEdgeEndpointSectorComplementPackage A V E a b hA hEdgeSource hEdgeTarget
      hEdgeNondegenerate hEdgeOpenInteriorsDisjoint haV hbV hab
      hNewInteriorDisjoint ra hra_pos hra_vertices hra_nonincident_edges
  have hEndpointB_sectors :=
    OneEdgeEndpointSectorComplementPackage A V E b a hA hEdgeSource hEdgeTarget
      hEdgeNondegenerate hEdgeOpenInteriorsDisjoint hbV haV hab.symm
      hNewInteriorDisjoint_symm rb hrb_pos hrb_vertices hrb_nonincident_edges
  rcases hEndpointA_sectors with
    ⟨clockwiseNextA, fullClockwiseTurnA, clockwiseTurnA, sectorA,
      hfullA_eq, hfullA_pos, hturnA_pos, hturnA_le, hturnA_full,
      hfirstA_after, hfixedA, hsectorA_data, hcarrierA_rays,
      hnewA_ray, hsectorA_cover⟩
  rcases hEndpointB_sectors with
    ⟨clockwiseNextB, fullClockwiseTurnB, clockwiseTurnB, sectorB,
      hfullB_eq, hfullB_pos, hturnB_pos, hturnB_le, hturnB_full,
      hfirstB_after, hfixedB, hsectorB_data, hcarrierB_rays,
      hnewB_ray, hsectorB_cover⟩
  have hAcompact : IsCompact A :=
    FiniteStraightLineComplexCarrierCompact A V E hA
  rcases OneEdgeMiddleParametersFromEndpointRadii a b ra rb hab hra_pos hrb_pos
      hradii_sum_lt with
    ⟨t0, t1, ht0_pos, ht01, ht1_lt, ht0_reaches_a, ht1_reaches_b,
      hline_t0_ball_a, hline_t1_ball_b, ht_mem_open⟩
  have hMiddleSubsegment_nonempty :
      (AffineMap.lineMap a b ''
        Set.Icc t0 t1).Nonempty := by
    refine ⟨AffineMap.lineMap a b ((t0 + t1) / 2), ?_⟩
    refine ⟨(t0 + t1) / 2, ?_, rfl⟩
    constructor <;> linarith
  have hMiddleSubsegment_compact :
      IsCompact
        (AffineMap.lineMap a b ''
          Set.Icc t0 t1) :=
    (isCompact_Icc.image AffineMap.lineMap_continuous)
  have hMiddleSubsegment_disjoint_A :
      Disjoint
        (AffineMap.lineMap a b ''
          Set.Icc t0 t1) A := by
    rw [Set.disjoint_left]
    intro x hx hxA
    rcases hx with ⟨t, ht, rfl⟩
    have ht_open : t ∈ Set.Ioo (0 : ℝ) 1 :=
      ht_mem_open t ht
    have hxopen : AffineMap.lineMap a b t ∈ openSegment ℝ a b := by
      rw [openSegment_eq_image_lineMap]
      exact ⟨t, ht_open, rfl⟩
    exact (Set.disjoint_left.mp hNewInteriorDisjoint) hxopen hxA
  rcases PositiveSeparation hMiddleSubsegment_nonempty ⟨a, haA⟩
      hMiddleSubsegment_compact hAcompact hMiddleSubsegment_disjoint_A with
    ⟨δmid, hδmid_pos, hδmid_sep⟩
  rcases OneEdgeMiddleRectangleEndpointBallOverlaps A a b t0 t1 δmid
      (Metric.ball a ra) (Metric.ball b rb) hab
      ht0_pos ht01 ht1_lt hδmid_pos hδmid_sep
      Metric.isOpen_ball Metric.isOpen_ball
      hline_t0_ball_a hline_t1_ball_b with
    ⟨εmid, hεmid_pos, middleRect, middleLeft, middleRight,
      hmiddleRect_nonempty, hmiddleRect_open,
      hmiddleLeft_nonempty, hmiddleLeft_open, hmiddleLeft_connected,
      hmiddleRight_nonempty, hmiddleRight_open, hmiddleRight_connected,
      hmiddleLeft_subset_rect, hmiddleRight_subset_rect,
      hmiddleLeft_subset_compl, hmiddleRight_subset_compl, hmiddle_cover,
      hmiddle_axis_subset,
      hmiddleLeft_ball_a, hmiddleRight_ball_a,
      hmiddleLeft_ball_b, hmiddleRight_ball_b⟩
  have hLocalSegmentNeighborhood :=
    OneEdgeMiddleOpenSegmentNeighborhood a b ra rb t0 t1 middleRect hab
      ht0_pos ht01 ht1_lt ht0_reaches_a ht1_reaches_b
      hline_t0_ball_a hline_t1_ball_b hmiddleRect_open hmiddle_axis_subset
  have hLocalUnion_open :
      IsOpen ((Metric.ball a ra ∪ middleRect) ∪ Metric.ball b rb) :=
    hLocalSegmentNeighborhood.1
  have hOpenSegment_subset_localUnion :
      openSegment ℝ a b ⊆
        ((Metric.ball a ra ∪ middleRect) ∪ Metric.ball b rb) :=
    hLocalSegmentNeighborhood.2
  have hSegment_subset_localUnion :
      segment ℝ a b ⊆
        ((Metric.ball a ra ∪ middleRect) ∪ Metric.ball b rb) := by
    intro x hx
    rw [← insert_endpoints_openSegment (𝕜 := ℝ) a b] at hx
    rcases hx with rfl | hx
    · left
      left
      exact Metric.mem_ball_self hra_pos
    · rcases hx with rfl | hxopen
      · right
        exact Metric.mem_ball_self hrb_pos
      · exact hOpenSegment_subset_localUnion hxopen
  have hCsigma_path : PolygonallyPathConnected Csigma := by
    have hAopen_compl : IsOpen Aᶜ := hAcompact.isClosed.isOpen_compl
    exact
      OpenConnectedComponentPolygonallyConnected Aᶜ Csigma hAopen_compl
        (by simpa using hCsigma)
  have hmiddleLeft_sectorA :
      ∃ i, (middleLeft ∩ sectorA i).Nonempty := by
    rcases hmiddleLeft_ball_a with ⟨x, ⟨hxleft, hxball⟩⟩
    have hxcompl : x ∈ (A ∪ segment ℝ a b)ᶜ :=
      hmiddleLeft_subset_compl hxleft
    rcases hsectorA_cover x hxball hxcompl with ⟨i, hxi⟩
    exact ⟨i, ⟨x, ⟨hxleft, hxi⟩⟩⟩
  have hmiddleRight_sectorA :
      ∃ i, (middleRight ∩ sectorA i).Nonempty := by
    rcases hmiddleRight_ball_a with ⟨x, ⟨hxright, hxball⟩⟩
    have hxcompl : x ∈ (A ∪ segment ℝ a b)ᶜ :=
      hmiddleRight_subset_compl hxright
    rcases hsectorA_cover x hxball hxcompl with ⟨i, hxi⟩
    exact ⟨i, ⟨x, ⟨hxright, hxi⟩⟩⟩
  have hmiddleLeft_sectorB :
      ∃ i, (middleLeft ∩ sectorB i).Nonempty := by
    rcases hmiddleLeft_ball_b with ⟨x, ⟨hxleft, hxball⟩⟩
    have hxcompl_ab : x ∈ (A ∪ segment ℝ a b)ᶜ :=
      hmiddleLeft_subset_compl hxleft
    have hxcompl_ba : x ∈ (A ∪ segment ℝ b a)ᶜ := by
      simpa [segment_symm] using hxcompl_ab
    rcases hsectorB_cover x hxball hxcompl_ba with ⟨i, hxi⟩
    exact ⟨i, ⟨x, ⟨hxleft, hxi⟩⟩⟩
  have hmiddleRight_sectorB :
      ∃ i, (middleRight ∩ sectorB i).Nonempty := by
    rcases hmiddleRight_ball_b with ⟨x, ⟨hxright, hxball⟩⟩
    have hxcompl_ab : x ∈ (A ∪ segment ℝ a b)ᶜ :=
      hmiddleRight_subset_compl hxright
    have hxcompl_ba : x ∈ (A ∪ segment ℝ b a)ᶜ := by
      simpa [segment_symm] using hxcompl_ab
    rcases hsectorB_cover x hxball hxcompl_ba with ⟨i, hxi⟩
    exact ⟨i, ⟨x, ⟨hxright, hxi⟩⟩⟩
  have hRawLocalCover :=
    OneEdgeRawLocalFiniteCover A Csigma a b ra rb sectorA sectorB middleRect
      middleLeft middleRight hCsigma hsectorA_data hsectorB_data
      hmiddleLeft_connected hmiddleRight_connected hmiddleLeft_subset_compl
      hmiddleRight_subset_compl hmiddle_cover hsectorA_cover hsectorB_cover
      hmiddleLeft_sectorA hmiddleRight_sectorA hmiddleLeft_sectorB
      hmiddleRight_sectorB
  rcases hRawLocalCover with
    ⟨rawPieces, piece, hpiece_sectorA, hpiece_sectorB, hpiece_middleLeft,
      hpiece_middleRight, hraw_mem, hraw_piece_data, hraw_cover,
      hraw_middle_overlaps⟩
  have hGroupedLocalPieces :=
    FiniteConnectedIntersectionGrouping rawPieces piece
      ((A ∪ segment ℝ a b)ᶜ ∩ Csigma)
      (fun k hk => (hraw_piece_data k hk).1)
      (fun k hk => (hraw_piece_data k hk).2.1)
      (fun k hk x hx =>
        ⟨(hraw_piece_data k hk).2.2.1 hx,
          (hraw_piece_data k hk).2.2.2 hx⟩)
  rcases hGroupedLocalPieces with
    ⟨groupedLocalPieces, groupedLocalPieceOf, hgroupedLocalPiece_eq,
      hgroupedLocalPiece_mem, hgroupedLocalPiece_rep,
      hgroupedLocalPiece_data, hrawPiece_subset_groupedLocalPiece⟩
  have hOrderedFirstHitPrefix :
      ∀ (γ : PolygonalPath) (U : Set (EuclideanSpace ℝ (Fin 2))),
        IsOpen U →
          segment ℝ a b ⊆ U →
            γ.source ∉ segment ℝ a b →
              γ.target ∈ segment ℝ a b →
                ∃ (y : EuclideanSpace ℝ (Fin 2))
                  (P : Set (EuclideanSpace ℝ (Fin 2))),
                  y ∈ γ.carrier ∧ y ∈ U ∧ y ∉ segment ℝ a b ∧
                    IsConnected P ∧ γ.source ∈ P ∧ y ∈ P ∧
                      P ⊆ γ.carrier ∩ (segment ℝ a b)ᶜ := by
    intro γ U hU hsegU hsrc htgt
    exact PolygonalPathOrderedFirstHitPrefix γ a b U hU hsegU hsrc htgt
  have hLocalGroupedPieceHit :
      ∀ C : Set (EuclideanSpace ℝ (Fin 2)),
        ComplementComponent (A ∪ segment ℝ a b) C →
          C ⊆ Csigma →
            ∃ G ∈ groupedLocalPieces, (C ∩ G).Nonempty := by
    intro C hC hC_subset_Csigma
    exact
      OneEdgeGroupedLocalPieceHit A Csigma C
        ((Metric.ball a ra ∪ middleRect) ∪ Metric.ball b rb) a b
        rawPieces piece groupedLocalPieces groupedLocalPieceOf
        hC hC_subset_Csigma hCsigma.2.1 hCsigma_path
        hOpenSegment_Csigma hLocalUnion_open hSegment_subset_localUnion
        hraw_cover hgroupedLocalPiece_mem hrawPiece_subset_groupedLocalPiece
  -- The remaining proof is the local finite hitting family inside
  -- `Csigma \ openSegment ℝ a b`; old components outside `Csigma`, refined
  -- endpoint sector decompositions, and the middle rectangular side pieces
  -- are now handled.
  classical
  rcases hFiniteA with ⟨oldComps, hOldComps_component, hOldComps_cover⟩
  let hitFamily : Finset (Set (EuclideanSpace ℝ (Fin 2))) :=
    oldComps.filter (fun C => C ≠ Csigma) ∪ groupedLocalPieces
  let P : hitFamily → Set (EuclideanSpace ℝ (Fin 2)) := fun i => i.1
  have hPne : ∀ i : hitFamily, (P i).Nonempty := by
    intro i
    dsimp [P]
    have hi := Finset.mem_union.mp i.2
    rcases hi with hi_old | hi_grouped
    · exact (hOldComponentPersists i.1
        (hOldComps_component i.1 (Finset.mem_filter.mp hi_old).1)
        (Finset.mem_filter.mp hi_old).2).2.1
    · exact (hgroupedLocalPiece_data i.1 hi_grouped).1
  have hPsub :
      ∀ i : hitFamily, P i ⊆ (A ∪ segment ℝ a b)ᶜ := by
    intro i
    dsimp [P]
    have hi := Finset.mem_union.mp i.2
    rcases hi with hi_old | hi_grouped
    · exact (hOldComponentPersists i.1
        (hOldComps_component i.1 (Finset.mem_filter.mp hi_old).1)
        (Finset.mem_filter.mp hi_old).2).2.2.1
    · intro x hx
      exact (hgroupedLocalPiece_data i.1 hi_grouped).2.2 hx |>.1
  have hPconn : ∀ i : hitFamily, IsConnected (P i) := by
    intro i
    dsimp [P]
    have hi := Finset.mem_union.mp i.2
    rcases hi with hi_old | hi_grouped
    · exact (hOldComponentPersists i.1
        (hOldComps_component i.1 (Finset.mem_filter.mp hi_old).1)
        (Finset.mem_filter.mp hi_old).2).2.2.2.1
    · exact (hgroupedLocalPiece_data i.1 hi_grouped).2.1
  have hhit :
      ∀ C : Set (EuclideanSpace ℝ (Fin 2)),
        ComplementComponent (A ∪ segment ℝ a b) C →
          ∃ i : hitFamily, (C ∩ P i).Nonempty := by
    intro C hC
    have hC_subset_old_compl : C ⊆ Aᶜ := by
      intro x hxC hxA
      exact hC.2.1 hxC (Or.inl hxA)
    rcases ConnectedSubsetContainedInUniqueComplementComponent A C hC.1
        hC_subset_old_compl hC.2.2.1 with
      ⟨D, hD_data, _hD_unique⟩
    rcases hD_data with ⟨hD_component, hC_subset_D⟩
    have hD_mem_old : D ∈ oldComps :=
      hOldComps_cover D hD_component
    by_cases hD_eq : D = Csigma
    · have hC_subset_Csigma : C ⊆ Csigma := by
        simpa [hD_eq] using hC_subset_D
      rcases hLocalGroupedPieceHit C hC hC_subset_Csigma with
        ⟨G, hG_mem, hCG⟩
      refine ⟨⟨G, ?_⟩, ?_⟩
      · exact Finset.mem_union.mpr (Or.inr hG_mem)
      · simpa [P]
        using hCG
    · have hD_mem_hit : D ∈ hitFamily := by
        exact Finset.mem_union.mpr
          (Or.inl (Finset.mem_filter.mpr ⟨hD_mem_old, hD_eq⟩))
      have hCD_nonempty : (C ∩ D).Nonempty := by
        rcases hC.1 with ⟨x, hxC⟩
        exact ⟨x, hxC, hC_subset_D hxC⟩
      refine ⟨⟨D, hD_mem_hit⟩, ?_⟩
      simpa [P] using hCD_nonempty
  exact
    ComplementComponentsFiniteHitFamily (A ∪ segment ℝ a b) P
      hPne hPsub hPconn hhit
