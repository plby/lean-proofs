import StackExchange.Puzzling139335.N5.Prepared.Geometry
import StackExchange.Puzzling139335.N5.FaceNormals.Angles
import StackExchange.Puzzling139335.N5.AxisFaces.Normalized
import StackExchange.Puzzling139335.N5.TerminalFace.Normalized
import StackExchange.Puzzling139335.N5.AlignedFace
import StackExchange.Puzzling139335.N5.OutgoingAlignedFace
import StackExchange.Puzzling139335.N5.PrefixFace.Prepared
import StackExchange.Puzzling139335.N5.SuffixFace

/-!
# The final five-incidence support-direction split

Two actual endpoints on the fourth piece's top side give a nontrivial
support level in the prototype.  The unit top-row normal is constrained
by the actual three corner supports.  Its five possible non-axis forms
are all excluded below, including both placement orientations.
-/

open Set

namespace Puzzling139335.N5

open PlaneIsometries

/-- The fourth piece has a genuine two-point support level, obtained by
pulling back its two distinct top-contact endpoints. -/
theorem Prepared.fourth_top_support_nontrivial {d : SquareDissection}
    (q : Prepared d) :
    HasTwoPointSupport (d.piece 0)
      (linearMatrix q.eD 1 0) (linearMatrix q.eD 1 1) := by
  have hleft : Schoenflies.Plane.mk q.b 1 ∈ q.eD '' d.piece 0 := by
    rw [q.image_D]
    exact (q.top_fourth q.b).mpr ⟨le_rfl, q.b_lt_m.le⟩
  have hright : Schoenflies.Plane.mk q.m 1 ∈ q.eD '' d.piece 0 := by
    rw [q.image_D]
    exact (q.top_fourth q.m).mpr ⟨q.b_lt_m.le, le_rfl⟩
  apply FourthSide.hasTwoPointSupport_of_upper_contact q.eD q.fit_D
  refine ⟨Schoenflies.Plane.mk q.b 1, ⟨hleft, rfl⟩,
    Schoenflies.Plane.mk q.m 1, ⟨hright, rfl⟩, ?_⟩
  intro heq
  exact q.b_lt_m.ne (congrArg (fun p : Plane => p 0) heq)

/-- The actual source supports force the fourth piece's top normal into
the proved allowed families. -/
theorem Prepared.fourth_top_normal_allowed {d : SquareDissection}
    (q : Prepared d) :
    AllowedNormal (Real.cos q.θ) (Real.sin q.θ)
      (linearMatrix q.eD 1 0) (linearMatrix q.eD 1 1) := by
  have hnorm : linearMatrix q.eD 1 0 ^ 2 + linearMatrix q.eD 1 1 ^ 2 = 1 := by
    simpa [pow_two] using linearMatrix_row_dot q.eD 1 1
  exact allowedNormal_of_support_inequalities (d.piece_subset 0)
    q.normalized.below_diagonal q.normalized.bottom_left q.normalized.bottom_right
    q.C_mem q.unit q.sin_pos q.sin_lt_cos q.corner_support hnorm q.fourth_top_support_nontrivial

/-- Every support direction of the prepared actual configuration is
impossible.  There is no remaining angle or placement classification
hypothesis in this theorem. -/
theorem Prepared.impossible {d : SquareDissection} (q : Prepared d) : False := by
  have hnorm : linearMatrix q.eD 1 0 ^ 2 + linearMatrix q.eD 1 1 ^ 2 = 1 := by
    simpa [pow_two] using linearMatrix_row_dot q.eD 1 1
  obtain ⟨hnx, hny⟩ := q.normalized.fourth_top_row_nonzero q.eD q.image_D
  rcases allowedNormal_angle_cases q.angle hnorm hnx hny q.fourth_top_normal_allowed with
    ⟨hrow₀, hrow₁⟩ | ⟨hrow₀, hrow₁⟩ | ⟨r, hr, hrow₀, hrow₁⟩ |
      ⟨φ, hφ, hφθ, hrow₀, hrow₁⟩ | ⟨ψ, hθψ, hψ, hrow₀, hrow₁⟩
  · exact q.normalized.incoming_aligned_face_impossible q.eR q.eD q.image_R q.image_D
      q.unit q.cos_pos q.sin_pos q.b_lt_m q.m_lt_one q.transverse_pos q.R_form
      hrow₀ hrow₁ q.top_singleton q.top_fourth
      ((q.right_singleton q.b).mpr ⟨le_rfl, q.b_lt_one.le⟩)
  · exact q.outgoing_aligned_impossible hrow₀ hrow₁
  · have hnot := q.normalized.terminal_top_normal_excludes_center q.eD q.image_D hr
      hrow₀ hrow₁
      ⟨Schoenflies.Plane.mk q.b 1, (q.top_fourth q.b).mpr ⟨le_rfl, q.b_lt_m.le⟩, rfl⟩
    exact hnot (interior_subset q.center_fourth)
  · exact q.prefix_face_impossible hφ hφθ hrow₀ hrow₁
  · exact q.suffix_face_impossible hθψ hψ hrow₀ hrow₁

end Puzzling139335.N5
