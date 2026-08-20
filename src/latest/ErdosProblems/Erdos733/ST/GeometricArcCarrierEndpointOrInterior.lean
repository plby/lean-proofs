import ErdosProblems.Erdos733.ST.GeometricArcDrawing

open Classical
noncomputable section

-- [TABLET NODE: GeometricArcCarrierEndpointOrInterior]
lemma GeometricArcCarrierEndpointOrInterior {V : Type*} [Fintype V]
    {G : SimpleGraph V} [Fintype G.edgeSet] (D : GeometricArcDrawing G)
    (e : G.edgeFinset) {p : EuclideanSpace ℝ (Fin 2)}
    (hp : p ∈ D.edgeCarrier e) :
    p = D.edgeSource e ∨ p = D.edgeTarget e ∨ p ∈ D.edgeRelativeInterior e := by
-- BODY
  rcases D.edge_is_simple_lineSegment_or_circularArc e with hline | harc
  · rcases hline with ⟨_hne, hcarrier, hrel⟩
    by_cases hs : p = D.edgeSource e
    · exact Or.inl hs
    · by_cases ht : p = D.edgeTarget e
      · exact Or.inr (Or.inl ht)
      · exact Or.inr (Or.inr (by
          rw [hrel]
          exact mem_openSegment_of_ne_left_right (𝕜 := ℝ)
            (by simpa [eq_comm] using hs) (by simpa [eq_comm] using ht)
            (by simpa [hcarrier] using hp)))
  · rcases harc with
      ⟨_c, _r, γ, _hr, _hγcont, _hγinj, _hcircle, hsource, htarget,
        hcarrier, hrel⟩
    rw [hcarrier] at hp
    rcases hp with ⟨t, rfl⟩
    by_cases ht0 : t.1 = 0
    · left
      have ht_eq : t = ⟨0, by simp⟩ := Subtype.ext ht0
      simpa [ht_eq, hsource]
    · by_cases ht1 : t.1 = 1
      · right
        left
        have ht_eq : t = ⟨1, by simp⟩ := Subtype.ext ht1
        simpa [ht_eq, htarget]
      · right
        right
        rw [hrel]
        have ht_pos : 0 < t.1 := lt_of_le_of_ne t.2.1 (Ne.symm ht0)
        have ht_lt : t.1 < 1 := lt_of_le_of_ne t.2.2 ht1
        refine ⟨⟨t.1, ht_pos, ht_lt⟩, ?_⟩
        congr
