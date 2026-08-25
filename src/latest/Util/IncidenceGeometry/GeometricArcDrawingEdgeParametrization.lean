import Util.IncidenceGeometry.GeometricArcDrawing

open Classical
noncomputable section

lemma GeometricArcDrawingEdgeParametrization {V : Type*} [Fintype V]
    {G : SimpleGraph V} [Fintype G.edgeSet] (D : GeometricArcDrawing G)
    (e : G.edgeFinset) :
    ∃ γ : Set.Icc (0 : ℝ) 1 → EuclideanSpace ℝ (Fin 2),
      Continuous γ ∧ Function.Injective γ ∧
        γ ⟨0, by simp⟩ = D.edgeSource e ∧
          γ ⟨1, by simp⟩ = D.edgeTarget e ∧
            D.edgeCarrier e = Set.range γ ∧
              D.edgeRelativeInterior e =
                Set.range (fun t : {t : ℝ // 0 < t ∧ t < 1} =>
                  γ ⟨t.1, ⟨le_of_lt t.2.1, le_of_lt t.2.2⟩⟩) := by
  rcases D.edge_is_simple_lineSegment_or_circularArc e with hline | harc
  · rcases hline with ⟨hne, hcarrier, hrel⟩
    let γ : Set.Icc (0 : ℝ) 1 → EuclideanSpace ℝ (Fin 2) := fun t =>
      AffineMap.lineMap (D.edgeSource e) (D.edgeTarget e) t.1
    have hγcont : Continuous γ := by
      exact AffineMap.lineMap_continuous.comp continuous_subtype_val
    have hγinj : Function.Injective γ := by
      intro s t hst
      apply Subtype.ext
      exact (AffineMap.lineMap_injective (k := ℝ) hne) hst
    have hγrange :
        Set.range γ =
          (AffineMap.lineMap (D.edgeSource e) (D.edgeTarget e)) ''
            Set.Icc (0 : ℝ) 1 := by
      ext p
      constructor
      · rintro ⟨t, rfl⟩
        exact ⟨t.1, t.2, rfl⟩
      · rintro ⟨t, ht, rfl⟩
        exact ⟨⟨t, ht⟩, rfl⟩
    have hγopen_range :
        Set.range (fun t : {t : ℝ // 0 < t ∧ t < 1} =>
          γ ⟨t.1, ⟨le_of_lt t.2.1, le_of_lt t.2.2⟩⟩) =
            (AffineMap.lineMap (D.edgeSource e) (D.edgeTarget e)) ''
              Set.Ioo (0 : ℝ) 1 := by
      ext p
      constructor
      · rintro ⟨t, rfl⟩
        exact ⟨t.1, t.2, rfl⟩
      · rintro ⟨t, ht, rfl⟩
        exact ⟨⟨t, ht⟩, rfl⟩
    refine ⟨γ, hγcont, hγinj, ?_, ?_, ?_, ?_⟩
    · simp [γ]
    · simp [γ]
    · rw [hcarrier, segment_eq_image_lineMap, hγrange]
    · rw [hrel, openSegment_eq_image_lineMap, hγopen_range]
  · rcases harc with
      ⟨_c, _r, γ, _hr, hγcont, hγinj, _hcircle, hsource, htarget,
        hcarrier, hrel⟩
    exact ⟨γ, hγcont, hγinj, hsource, htarget, hcarrier, hrel⟩
