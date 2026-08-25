import Util.IncidenceGeometry.Basic

open Classical
noncomputable section

lemma EndpointUnitDiskChordGapCutDiskIntersections
    {A B z u v : EuclideanSpace ℝ (Fin 2)}
    {rho α β e x : ℝ}
    (hAB : A ≠ B)
    (hcut : Metric.closedBall z rho ∩ segment ℝ A B = segment ℝ u v)
    (hu : u = AffineMap.lineMap A B e)
    (hv : v = AffineMap.lineMap A B x)
    (hα0 : 0 ≤ α) (hαβ : α ≤ β) (hβ1 : β ≤ 1)
    (hex : e < x) :
    (∀ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
      p ∈ segment ℝ (AffineMap.lineMap A B α) (AffineMap.lineMap A B β) →
        p ∈ Metric.closedBall z rho →
          β < e → False) ∧
      (∀ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
        p ∈ segment ℝ (AffineMap.lineMap A B α) (AffineMap.lineMap A B β) →
          p ∈ Metric.closedBall z rho →
            β = e → p = u) ∧
        (∀ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
          p ∈ segment ℝ (AffineMap.lineMap A B α) (AffineMap.lineMap A B β) →
            p ∈ Metric.closedBall z rho →
              x < α → False) ∧
          (∀ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
            p ∈ segment ℝ (AffineMap.lineMap A B α) (AffineMap.lineMap A B β) →
              p ∈ Metric.closedBall z rho →
                x = α → p = v) := by
  let f : ℝ →ᵃ[ℝ] EuclideanSpace ℝ (Fin 2) := AffineMap.lineMap A B
  have hf : Function.Injective f := AffineMap.lineMap_injective (k := ℝ) hAB
  have gap_param :
      ∀ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
        p ∈ segment ℝ (f α) (f β) →
          ∃ s : ℝ, α ≤ s ∧ s ≤ β ∧ p = f s := by
    intro p hp
    have hseg : segment ℝ (f α) (f β) = f '' segment ℝ α β := by
      simp [f]
    rw [hseg] at hp
    rcases hp with ⟨s, hs, rfl⟩
    have hsIcc : s ∈ Set.Icc α β := by
      simpa [segment_eq_Icc hαβ] using hs
    exact ⟨s, hsIcc.1, hsIcc.2, rfl⟩
  have cut_param :
      ∀ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
        p ∈ Metric.closedBall z rho →
          p ∈ segment ℝ (f α) (f β) →
            ∃ t : ℝ, e ≤ t ∧ t ≤ x ∧ p = f t := by
    intro p hpball hpgap
    rcases gap_param hpgap with ⟨s, hsα, hsβ, hp_eq⟩
    have hp_chord : p ∈ segment ℝ A B := by
      rw [hp_eq]
      rw [segment_eq_image_lineMap]
      exact ⟨s, ⟨le_trans hα0 hsα, le_trans hsβ hβ1⟩, rfl⟩
    have hp_cut : p ∈ segment ℝ u v := by
      have : p ∈ Metric.closedBall z rho ∩ segment ℝ A B := ⟨hpball, hp_chord⟩
      simpa [hcut] using this
    have hseg_uv : segment ℝ u v = f '' segment ℝ e x := by
      simp [f, hu, hv]
    rw [hseg_uv] at hp_cut
    rcases hp_cut with ⟨t, ht, hpt⟩
    have htIcc : t ∈ Set.Icc e x := by
      simpa [segment_eq_Icc hex.le] using ht
    exact ⟨t, htIcc.1, htIcc.2, hpt.symm⟩
  constructor
  · intro p hpgap hpball hβe
    rcases gap_param hpgap with ⟨s, _hsα, hsβ, hp_eq_s⟩
    rcases cut_param hpball hpgap with ⟨t, hte, _htx, hp_eq_t⟩
    have hst : s = t := hf (by rw [← hp_eq_s, ← hp_eq_t])
    linarith
  constructor
  · intro p hpgap hpball hβe
    rcases gap_param hpgap with ⟨s, _hsα, hsβ, hp_eq_s⟩
    rcases cut_param hpball hpgap with ⟨t, hte, _htx, hp_eq_t⟩
    have hst : s = t := hf (by rw [← hp_eq_s, ← hp_eq_t])
    have ht_eq : t = e := by linarith
    rw [hp_eq_t, ht_eq, hu]
  constructor
  · intro p hpgap hpball hxα
    rcases gap_param hpgap with ⟨s, hsα, _hsβ, hp_eq_s⟩
    rcases cut_param hpball hpgap with ⟨t, _hte, htx, hp_eq_t⟩
    have hst : s = t := hf (by rw [← hp_eq_s, ← hp_eq_t])
    linarith
  · intro p hpgap hpball hxα
    rcases gap_param hpgap with ⟨s, hsα, _hsβ, hp_eq_s⟩
    rcases cut_param hpball hpgap with ⟨t, _hte, htx, hp_eq_t⟩
    have hst : s = t := hf (by rw [← hp_eq_s, ← hp_eq_t])
    have ht_eq : t = x := by linarith
    rw [hp_eq_t, ht_eq, hv]
