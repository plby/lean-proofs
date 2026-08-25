import Util.IncidenceGeometry.Basic

open Classical
noncomputable section

lemma EndpointSidePrefixEventInjectiveCharge
    (X : Set (EuclideanSpace ℝ (Fin 2)))
    (XA : Finset (EuclideanSpace ℝ (Fin 2)))
    (radius : EuclideanSpace ℝ (Fin 2) → ℝ) :
    (∀ z, z ∈ X →
      ∃ p, p ∈ XA ∧ z ∈ Metric.ball p (radius p)) →
      (∀ p, p ∈ XA →
        (X ∩ Metric.ball p (radius p)).Subsingleton) →
      ∃ charge :
          EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2),
        X.Finite ∧
          (∀ z, z ∈ X →
            charge z ∈ XA ∧
              z ∈ Metric.ball (charge z) (radius (charge z))) ∧
          ∀ z w, z ∈ X → w ∈ X →
            charge z = charge w → z = w := by
  intro hcover hone
  let charge :
      EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) :=
    fun z => if hz : z ∈ X then Classical.choose (hcover z hz) else 0
  have hcharge : ∀ z, z ∈ X →
      charge z ∈ XA ∧
        z ∈ Metric.ball (charge z) (radius (charge z)) := by
    intro z hz
    dsimp [charge]
    rw [dif_pos hz]
    exact Classical.choose_spec (hcover z hz)
  have hinjective : Set.InjOn charge X := by
    intro z hz w hw heq
    have hzdata := hcharge z hz
    have hwdata := hcharge w hw
    apply hone (charge z) hzdata.1
    · exact ⟨hz, hzdata.2⟩
    · exact ⟨hw, by simpa [heq] using hwdata.2⟩
  have hfinite : X.Finite := by
    apply Set.Finite.of_finite_image
    · apply XA.finite_toSet.subset
      rintro y ⟨z, hz, rfl⟩
      exact (hcharge z hz).1
    · exact hinjective
  refine ⟨charge, hfinite, hcharge, ?_⟩
  intro z w hz hw heq
  exact hinjective hz hw heq
