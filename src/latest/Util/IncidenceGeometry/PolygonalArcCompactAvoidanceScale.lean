import Util.IncidenceGeometry.PolygonalArcCarrierCompact
import Util.IncidenceGeometry.PositiveSeparation

open Classical
noncomputable section

lemma PolygonalArcCompactAvoidanceScale (γ : PolygonalArc)
    (F : Set (EuclideanSpace ℝ (Fin 2))) :
    IsCompact F →
      Disjoint F γ.carrier →
        ∃ η : ℝ, 0 < η ∧
          ∀ z : EuclideanSpace ℝ (Fin 2),
            (∃ p ∈ γ.carrier, dist z p < η) → z ∉ F := by
  intro hF hFγ
  by_cases hFnonempty : F.Nonempty
  · have hγcompact : IsCompact γ.carrier := PolygonalArcCarrierCompact γ
    have hseg : 0 + 1 < γ.vertices.length := by
      have hlen : 2 ≤ γ.vertices.length := γ.length_ge_two
      omega
    have h0 : 0 < γ.vertices.length := Nat.lt_of_succ_lt hseg
    have hγnonempty : γ.carrier.Nonempty := by
      refine ⟨γ.vertices[0]'h0, ?_⟩
      rw [γ.carrier_eq]
      refine ⟨0, hseg, ?_⟩
      simpa using
        (left_mem_segment ℝ (γ.vertices[0]'h0) (γ.vertices[0 + 1]'hseg))
    obtain ⟨δ, hδpos, hδ⟩ :=
      PositiveSeparation hFnonempty hγnonempty hF hγcompact hFγ
    refine ⟨δ, hδpos, ?_⟩
    intro z hzNear hzF
    rcases hzNear with ⟨p, hpγ, hzp⟩
    exact not_lt_of_ge (hδ z hzF p hpγ) hzp
  · refine ⟨1, by norm_num, ?_⟩
    intro z _ hzF
    exact hFnonempty ⟨z, hzF⟩
