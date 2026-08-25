import Util.IncidenceGeometry.PolygonalPathSegment

open Classical
noncomputable section

lemma PolygonalPathOriginalSegmentGap
    (K F : Set (EuclideanSpace ℝ (Fin 2))) (α : PolygonalPath)
    (i : ℕ) (hi : i + 1 < α.vertices.length)
    (p q : EuclideanSpace ℝ (Fin 2)) :
    α.carrier ⊆ Kᶜ →
      segment ℝ p q ⊆ segment ℝ α.vertices[i] α.vertices[i + 1] →
        Disjoint (segment ℝ p q) F →
          ∃ η : PolygonalPath,
            η.source = p ∧
              η.target = q ∧
                η.carrier ⊆ (K ∪ F)ᶜ := by
  intro hαK hpq_subset hdisj
  have hpq_safe : segment ℝ p q ⊆ (K ∪ F)ᶜ := by
    intro z hz
    have hz_segment : z ∈ segment ℝ α.vertices[i] α.vertices[i + 1] :=
      hpq_subset hz
    have hzα : z ∈ α.carrier := by
      rw [α.carrier_eq]
      right
      exact ⟨i, hi, hz_segment⟩
    have hz_notK : z ∉ K := hαK hzα
    have hz_notF : z ∉ F := by
      intro hzF
      exact (Set.disjoint_left.mp hdisj) hz hzF
    exact by
      simp [hz_notK, hz_notF]
  rcases PolygonalPathSegment p q with ⟨η, hηsource, hηtarget, hηcarrier⟩
  refine ⟨η, hηsource, hηtarget, ?_⟩
  intro z hz
  exact hpq_safe (by simpa [hηcarrier] using hz)
