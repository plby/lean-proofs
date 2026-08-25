import StackExchange.Puzzling139335.CornerSupport.Frames

/-!
# Edges between orthogonal support bisectors

Equality in the separation bound forces both support projections to attain
their extremal values. The edge is therefore perpendicular to the sum of the
bisectors and is a positive multiple of their difference.
-/

open Set

namespace Puzzling139335.CornerSupport.Equality

variable {P : Set Plane} {v w : Plane}

private theorem reverse_bisector_projection (hv : SupportCorner P v)
    (hw : SupportCorner P w) :
    ‖w - v‖ ≤ inner ℝ hw.bisector (w - v) := by
  have hproj := hw.bisector_projection hv.mem
  have hneg : v - w = -(w - v) := by abel
  rw [hneg, inner_neg_right, norm_neg] at hproj
  linarith

/-- Orthogonal corner bisectors have difference of length two. -/
theorem bisector_difference_norm (hv : SupportCorner P v) (hw : SupportCorner P w)
    (horth : inner ℝ hv.bisector hw.bisector = 0) :
    ‖hw.bisector - hv.bisector‖ = (2 : ℝ) := by
  have hnorm := norm_sub_sq_real hw.bisector hv.bisector
  rw [hv.bisector_norm_sq, hw.bisector_norm_sq,
    real_inner_comm hv.bisector hw.bisector, horth] at hnorm
  nlinarith [norm_nonneg (hw.bisector - hv.bisector)]

/-- Orthogonal corner bisectors attain both extremal edge projections. -/
theorem edge_projections_of_bisectors_orthogonal
    (hv : SupportCorner P v) (hw : SupportCorner P w)
    (horth : inner ℝ hv.bisector hw.bisector = 0) :
    inner ℝ hv.bisector (w - v) = -‖w - v‖ ∧
      inner ℝ hw.bisector (w - v) = ‖w - v‖ := by
  have hvproj := hv.bisector_projection hw.mem
  have hwproj := reverse_bisector_projection hv hw
  have hcs := real_inner_le_norm (hw.bisector - hv.bisector) (w - v)
  rw [inner_sub_left, bisector_difference_norm hv hw horth] at hcs
  constructor <;> linarith

/-- The edge between orthogonal support bisectors is perpendicular to their sum. -/
theorem edge_orthogonal_to_bisector_sum
    (hv : SupportCorner P v) (hw : SupportCorner P w)
    (horth : inner ℝ hv.bisector hw.bisector = 0) :
    inner ℝ (hv.bisector + hw.bisector) (w - v) = 0 := by
  obtain ⟨hvproj, hwproj⟩ := edge_projections_of_bisectors_orthogonal hv hw horth
  rw [inner_add_left, hvproj, hwproj]
  ring

/-- At distinct support corners the edge projects positively onto the
difference of the outward bisectors, without an orthogonality assumption. -/
theorem edge_projection_pos (hv : SupportCorner P v) (hw : SupportCorner P w)
    (hvw : v ≠ w) :
    0 < inner ℝ (hw.bisector - hv.bisector) (w - v) := by
  have hvproj := hv.bisector_projection hw.mem
  have hwproj := reverse_bisector_projection hv hw
  have hpos : 0 < ‖w - v‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hvw.symm)
  rw [inner_sub_left]
  linarith

/-- The displacement is exactly half its length times the bisector difference. -/
theorem edge_eq_smul_bisector_difference
    (hv : SupportCorner P v) (hw : SupportCorner P w)
    (horth : inner ℝ hv.bisector hw.bisector = 0) :
    w - v = (‖w - v‖ / 2) • (hw.bisector - hv.bisector) := by
  obtain ⟨hvproj, hwproj⟩ := edge_projections_of_bisectors_orthogonal hv hw horth
  have hproj : inner ℝ (w - v) (hw.bisector - hv.bisector) = 2 * ‖w - v‖ := by
    rw [real_inner_comm (hw.bisector - hv.bisector) (w - v),
      inner_sub_left, hvproj, hwproj]
    ring
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  apply sq_eq_zero_iff.mp
  rw [norm_sub_sq_real, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : 0 ≤ ‖w - v‖ / 2),
    bisector_difference_norm hv hw horth, inner_smul_right, hproj]
  ring

end Puzzling139335.CornerSupport.Equality
