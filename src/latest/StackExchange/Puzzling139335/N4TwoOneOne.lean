import StackExchange.Puzzling139335.N4TwoOneOne.Normalization
import StackExchange.Puzzling139335.N4TwoOneOne.Preparation
import StackExchange.Puzzling139335.N4TwoOneOne.TopFaceSuffix
import StackExchange.Puzzling139335.N4TwoOneOne.PrefixEndpoints
import StackExchange.Puzzling139335.N4TwoOneOne.AlignedFaces
import StackExchange.Puzzling139335.N4TwoOneOne.AlignedOutgoing

/-!
# The reflected-singleton degree-(2,1,1,0) obstruction

An actual two-corner piece, two reflected singleton-corner pieces, and a
cornerless fourth piece cannot protect the square center. The theorem assumes
only the normalized corner incidences and reflection identity. Every support
direction, contact interval, source endpoint, and scalar certificate premise
is derived from those geometric hypotheses.
-/

open Set

namespace Puzzling139335.N4TwoOneOne

open PlaneIsometries SupportContacts

/-- The geometric contradiction after the actual singleton congruence has
been put in its derived coordinate form. -/
theorem normalized_impossible {d : SquareDissection} {θ u v : ℝ}
    (hcfg : Configuration d) (h : SourceData d θ u v) (hc : d.HasProtectedCenter) :
    False := by
  obtain ⟨e, l, T, he, g, hface⟩ := h.exists_derived_geometry hcfg
  have hfit : e '' d.piece 0 ⊆ unitSquare := by
    rw [he]
    exact d.piece_subset 3
  have hRfit : rightMap θ u v '' d.piece 0 ⊆ unitSquare := by
    rw [h.right_image]
    exact d.piece_subset 1
  have hunit : linearMatrix e 1 0 ^ 2 + linearMatrix e 1 1 ^ 2 = 1 := by
    simpa [sideNormalX, sideNormalY, sideSign] using sideNormal_unit e 1 true
  have hnonzero := h.fourth_top_row_nonzero hcfg hc e he
  have hDL : (!₂[T, 1] : Plane) ∈ e '' d.piece 0 := by
    rw [he]
    exact g.middle_left_endpoint
  have hDR : (!₂[1 - T, 1] : Plane) ∈ e '' d.piece 0 := by
    rw [he]
    exact g.middle_right_endpoint
  rcases hasTwoSupportPoints_angle_classification h.source_support h.angle_pos
      (h.angle_lt_half_pi hcfg) (h.cos_pos hcfg) h.sin_pos hunit hface with
    haxis | hprefix | hincoming | houtgoing | hsuffix
  · exact haxis.elim hnonzero.1 hnonzero.2
  · obtain ⟨φ, hφ, hφθ, hnormal₀, hnormal₁⟩ := hprefix
    obtain ⟨X, Y, hX, hY, hstep, hsupport, hstrip⟩ :=
      exists_top_face_endpoints e hfit hnormal₀ hnormal₁ hDL hDR
    exact prefix_inconsistent_of_endpoints (d.piece_subset 0) hRfit
      h.bottom_left h.bottom_right g.source_left_endpoint g.source_right_endpoint
      g.incoming_endpoint g.outgoing_endpoint h.u_le_half g.l_bounds.1
      hφ hφθ (h.angle_lt_half_pi hcfg) hX hY hstep hsupport hstrip
  · exact incoming_aligned_false hcfg h hc e he hincoming.1 hincoming.2
  · exact AlignedOutgoing.no_aligned_outgoing h (h.angle_lt_half_pi hcfg)
      (h.v_pos hcfg)
      (outgoing_aligned_translation hcfg h e he houtgoing.1 houtgoing.2)
  · obtain ⟨φ, hθφ, hφπ, hnormal₀, hnormal₁⟩ := hsuffix
    obtain ⟨X, Y, hX, hY, hstep, hsupport, _⟩ :=
      exists_suffix_top_face_endpoints e hfit hnormal₀ hnormal₁ hDL hDR
    exact suffix_inconsistent_of_endpoints (d.piece_subset 0) hRfit
      h.bottom_right g.source_left_endpoint g.outgoing_endpoint h.u_le_half
      g.l_bounds.1 h.angle_pos hθφ hφπ hX hY hstep hsupport

/-- The complete actual reflected-singleton case, with no coordinate,
support-angle, hull, contact-interval, or scalar-certificate assumptions. -/
theorem Configuration.not_protectedCenter {d : SquareDissection}
    (hcfg : Configuration d) : ¬ d.HasProtectedCenter := by
  intro hc
  obtain ⟨d', hcfg', hcenter, θ, u, v, hdata⟩ := hcfg.exists_sourceData
  exact normalized_impossible hcfg' hdata (hcenter.mpr hc)

end Puzzling139335.N4TwoOneOne
