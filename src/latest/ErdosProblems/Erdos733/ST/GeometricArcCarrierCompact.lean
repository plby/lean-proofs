import ErdosProblems.Erdos733.ST.GeometricArcDrawing

open Classical
noncomputable section

-- [TABLET NODE: GeometricArcCarrierCompact]
lemma GeometricArcCarrierCompact {V : Type*} [Fintype V]
    {G : SimpleGraph V} [Fintype G.edgeSet] (D : GeometricArcDrawing G)
    (e : G.edgeFinset) :
    IsCompact (D.edgeCarrier e) ∧ (D.edgeCarrier e).Nonempty := by
-- BODY
  constructor
  · rcases D.edge_is_simple_lineSegment_or_circularArc e with hline | harc
    · rcases hline with ⟨_hne, hcarrier, _hrel⟩
      rw [hcarrier, segment_eq_image_lineMap]
      exact isCompact_Icc.image AffineMap.lineMap_continuous
    · rcases harc with
        ⟨_c, _r, γ, _hr, hγcont, _hγinj, _hcircle, _hsource, _htarget,
          hcarrier, _hrel⟩
      rw [hcarrier]
      exact isCompact_range hγcont
  · rcases D.edge_is_simple_lineSegment_or_circularArc e with hline | harc
    · rcases hline with ⟨_hne, hcarrier, _hrel⟩
      rw [hcarrier]
      exact ⟨D.edgeSource e, left_mem_segment ℝ (D.edgeSource e) (D.edgeTarget e)⟩
    · rcases harc with
        ⟨_c, _r, γ, _hr, _hγcont, _hγinj, _hcircle, _hsource, _htarget,
          hcarrier, _hrel⟩
      rw [hcarrier]
      exact Set.range_nonempty γ
