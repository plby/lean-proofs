import Util.IncidenceGeometry.Basic

open Classical
noncomputable section

lemma EndpointUnitDiskOrderedGapDiskIntersections
    {A B z1 z2 u1 v1 u2 v2 : EuclideanSpace ℝ (Fin 2)}
    {rho1 rho2 e1 x1 e2 x2 : ℝ}
    (hAB : A ≠ B)
    (hcut1 : Metric.closedBall z1 rho1 ∩ segment ℝ A B = segment ℝ u1 v1)
    (hcut2 : Metric.closedBall z2 rho2 ∩ segment ℝ A B = segment ℝ u2 v2)
    (hu1 : u1 = AffineMap.lineMap A B e1)
    (hv1 : v1 = AffineMap.lineMap A B x1)
    (hu2 : u2 = AffineMap.lineMap A B e2)
    (hv2 : v2 = AffineMap.lineMap A B x2)
    (hx1_nonneg : 0 ≤ x1) (he2_le_one : e2 ≤ 1)
    (he1x1 : e1 < x1) (hx1e2 : x1 < e2) (he2x2 : e2 < x2) :
    (∀ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
      p ∈ segment ℝ v1 u2 →
        p ∈ Metric.closedBall z1 rho1 →
          p = v1) ∧
      (∀ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
        p ∈ segment ℝ v1 u2 →
          p ∈ Metric.closedBall z2 rho2 →
            p = u2) := by
  have adjacent_lineMap_segments_inter_singleton :
      ∀ {α β γ : ℝ}, α < β → β < γ →
        segment ℝ (AffineMap.lineMap A B α) (AffineMap.lineMap A B β) ∩
            segment ℝ (AffineMap.lineMap A B β) (AffineMap.lineMap A B γ) =
          {AffineMap.lineMap A B β} := by
    intro α β γ hαβ hβγ
    let f : ℝ →ᵃ[ℝ] EuclideanSpace ℝ (Fin 2) := AffineMap.lineMap A B
    have hf : Function.Injective f := AffineMap.lineMap_injective (k := ℝ) hAB
    have hseg1 :
        segment ℝ (f α) (f β) = f '' segment ℝ α β := by
      simp
    have hseg2 :
        segment ℝ (f β) (f γ) = f '' segment ℝ β γ := by
      simp
    rw [hseg1, hseg2, ← Set.image_inter hf]
    have hinter : segment ℝ α β ∩ segment ℝ β γ = ({β} : Set ℝ) := by
      rw [segment_eq_Icc hαβ.le, segment_eq_Icc hβγ.le]
      ext x
      constructor
      · intro hx
        exact le_antisymm hx.1.2 hx.2.1
      · intro hx
        subst x
        exact ⟨⟨hαβ.le, le_rfl⟩, ⟨le_rfl, hβγ.le⟩⟩
    rw [hinter]
    simp [f]
  have hv1_chord : v1 ∈ segment ℝ A B := by
    rw [hv1, segment_eq_image_lineMap]
    exact Set.mem_image_of_mem (AffineMap.lineMap A B)
      ⟨hx1_nonneg, (le_of_lt hx1e2).trans he2_le_one⟩
  have hu2_chord : u2 ∈ segment ℝ A B := by
    rw [hu2, segment_eq_image_lineMap]
    exact Set.mem_image_of_mem (AffineMap.lineMap A B)
      ⟨le_trans hx1_nonneg (le_of_lt hx1e2), he2_le_one⟩
  have hbridge_chord :
      segment ℝ v1 u2 ⊆ segment ℝ A B :=
    (convex_segment A B).segment_subset hv1_chord hu2_chord
  have hleft_inter :
      segment ℝ u1 v1 ∩ segment ℝ v1 u2 = {v1} := by
    simpa [hu1, hv1, hu2] using
      adjacent_lineMap_segments_inter_singleton he1x1 hx1e2
  have hright_inter :
      segment ℝ v1 u2 ∩ segment ℝ u2 v2 = {u2} := by
    simpa [hv1, hu2, hv2] using
      adjacent_lineMap_segments_inter_singleton hx1e2 he2x2
  constructor
  · intro p hpbridge hpball
    have hp_cut : p ∈ segment ℝ u1 v1 := by
      have hp_inter : p ∈ Metric.closedBall z1 rho1 ∩ segment ℝ A B :=
        ⟨hpball, hbridge_chord hpbridge⟩
      simpa [hcut1] using hp_inter
    have hp_singleton : p ∈ ({v1} : Set (EuclideanSpace ℝ (Fin 2))) := by
      simpa [hleft_inter] using (show p ∈ segment ℝ u1 v1 ∩ segment ℝ v1 u2 from
        ⟨hp_cut, hpbridge⟩)
    exact Set.mem_singleton_iff.mp hp_singleton
  · intro p hpbridge hpball
    have hp_cut : p ∈ segment ℝ u2 v2 := by
      have hp_inter : p ∈ Metric.closedBall z2 rho2 ∩ segment ℝ A B :=
        ⟨hpball, hbridge_chord hpbridge⟩
      simpa [hcut2] using hp_inter
    have hp_singleton : p ∈ ({u2} : Set (EuclideanSpace ℝ (Fin 2))) := by
      simpa [hright_inter] using (show p ∈ segment ℝ v1 u2 ∩ segment ℝ u2 v2 from
        ⟨hpbridge, hp_cut⟩)
    exact Set.mem_singleton_iff.mp hp_singleton
