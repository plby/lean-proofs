import StackExchange.Puzzling139335.N5.StrictFrame.Geometry
import StackExchange.Puzzling139335.N5.SideContacts

/-!
# The strict actual singleton frame in the five-incidence case

Every premise is an actual normalized dissection, its protected center, or
an actual congruence from piece zero to piece two. The side-contact theorem
supplies the diagonal interval; no angle or supporting-hull certificate is
assumed.
-/

open Set

namespace Puzzling139335.N5

/-- The actual singleton-corner placement has strict frame parameters and
strict source-coordinate bounds. Both possible row orders are retained. -/
theorem Normalized.exists_strict_corner_frame {d : SquareDissection}
    (h : Normalized d) (hc : d.HasProtectedCenter)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (he : e '' d.piece 0 = d.piece 2) :
    ∃ c s : ℝ, c ^ 2 + s ^ 2 = 1 ∧ 0 < s ∧ s < c ∧
      0 < e.symm (corner 2) 1 ∧
      e.symm (corner 2) 1 < e.symm (corner 2) 0 ∧
      e.symm (corner 2) 0 < c ∧ c < 1 ∧
      0 < c * e.symm (corner 2) 1 - s * e.symm (corner 2) 0 ∧
      c * e.symm (corner 2) 0 + s * e.symm (corner 2) 1 < 1 ∧
      CornerPlacementForm e (e.symm (corner 2)) c s := by
  obtain ⟨a, _ha, haHalf, hcontact⟩ := h.exists_diagonal_contact_interval hc
  obtain ⟨hk, c, s, hunit, hs, hsc, hcpos, hA, hB, hf⟩ := h.corner_frame_exists e he
  have hC := (h.third_corner_preimage e he).1
  have hdiag : e.symm (corner 2) 0 = e.symm (corner 2) 1 →
      e.symm (corner 2) 0 < 1 / 2 :=
    StrictFrame.diagonal_member_lt_half_of_contact_interval haHalf hcontact hC
  obtain ⟨hspos, hsc', hkh, hhc, hc1, hz, hd⟩ :=
    h.strict_parameters_of_diagonal_bound e he hC hunit hs hsc hcpos hA hB hf hdiag
  exact ⟨c, s, hunit, hspos, hsc', hk, hkh, hhc, hc1, hz, hd, hf⟩

/-- The same strict frame written with an angle strictly between zero and
forty-five degrees, without discarding either actual placement orientation. -/
theorem Normalized.exists_strict_corner_angle {d : SquareDissection}
    (h : Normalized d) (hc : d.HasProtectedCenter)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (he : e '' d.piece 0 = d.piece 2) :
    ∃ θ : ℝ, θ ∈ Ioo (0 : ℝ) (Real.pi / 4) ∧
      0 < e.symm (corner 2) 1 ∧
      e.symm (corner 2) 1 < e.symm (corner 2) 0 ∧
      e.symm (corner 2) 0 < Real.cos θ ∧ Real.cos θ < 1 ∧
      0 < Real.cos θ * e.symm (corner 2) 1 - Real.sin θ * e.symm (corner 2) 0 ∧
      Real.cos θ * e.symm (corner 2) 0 + Real.sin θ * e.symm (corner 2) 1 < 1 ∧
      CornerPlacementForm e (e.symm (corner 2)) (Real.cos θ) (Real.sin θ) := by
  obtain ⟨c, s, hunit, hs, hsc, hk, hkh, hhc, hc1, hz, hd, hf⟩ :=
    h.exists_strict_corner_frame hc e he
  obtain ⟨θ, hθ, hcos, hsin⟩ := StrictFrame.exists_angle_of_strict_frame hunit hs hsc
  refine ⟨θ, hθ, hk, hkh, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [hcos] using hhc
  · simpa only [hcos] using hc1
  · simpa only [hcos, hsin] using hz
  · simpa only [hcos, hsin] using hd
  · simpa only [hcos, hsin] using hf

end Puzzling139335.N5
