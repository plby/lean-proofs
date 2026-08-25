import Util.IncidenceGeometry.JordanLocalSideData

open Classical
noncomputable section

lemma JordanExteriorLocalSideUnbounded
    (J : SimpleClosedPolygonalCurve) (S : JordanLocalSideData J) :
    ∃ T : Set (EuclideanSpace ℝ (Fin 2)),
      T.Nonempty ∧ T ⊆ J.carrierᶜ ∧ IsConnected T ∧
        ¬ Bornology.IsBounded T ∧
          ((T ∩ S.leftRegion).Nonempty ∨ (T ∩ S.rightRegion).Nonempty) := by
  rcases S.exterior_ray_access with ⟨w, u, hu, hw_side, hray⟩
  let f : ℝ → EuclideanSpace ℝ (Fin 2) := fun t => w + t • u
  let T : Set (EuclideanSpace ℝ (Fin 2)) := f '' Set.Ici 0
  have hwT : w ∈ T := by
    refine ⟨0, by simp, ?_⟩
    simp [f]
  refine ⟨T, ⟨w, hwT⟩, ?_, ?_, ?_, ?_⟩
  · rintro z ⟨t, ht, rfl⟩
    exact hray t ht
  · exact isConnected_Ici.image f
      ((continuous_const.add (continuous_id.smul continuous_const)).continuousOn)
  · intro hT
    rcases Metric.isBounded_iff.mp hT with ⟨C, hC⟩
    have hu_norm : 0 < ‖u‖ := norm_pos_iff.mpr hu
    let t : ℝ := (|C| + 1) / ‖u‖
    have ht : 0 ≤ t := by
      exact div_nonneg (by positivity) hu_norm.le
    have hftT : f t ∈ T := ⟨t, ht, rfl⟩
    have hdist_le : dist w (f t) ≤ C := hC hwT hftT
    have hdist_eq : dist w (f t) = t * ‖u‖ := by
      rw [dist_eq_norm]
      have hsub : w - f t = -(t • u) := by
        simp [f]
      rw [hsub, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht]
    have ht_mul : t * ‖u‖ = |C| + 1 := by
      dsimp [t]
      field_simp
    rw [hdist_eq, ht_mul] at hdist_le
    linarith [le_abs_self C]
  · rcases hw_side with hw_left | hw_right
    · exact Or.inl ⟨w, hwT, hw_left⟩
    · exact Or.inr ⟨w, hwT, hw_right⟩
