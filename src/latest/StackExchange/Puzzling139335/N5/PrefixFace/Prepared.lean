import StackExchange.Puzzling139335.N5.PrefixFace
import StackExchange.Puzzling139335.N5.Prepared.Geometry
import StackExchange.Puzzling139335.N5.TopFace.Coordinates

/-!
# The strict prefix face in the actual prepared configuration

The two endpoints are the actual inverse images of the fourth piece's
top interval.  Either placement orientation gives the same oriented source
endpoint relation, so the finite-point obstruction applies.
-/

open Set

namespace Puzzling139335.N5

open PlaneIsometries

private theorem prefix_false_of_oriented_endpoints {d : SquareDissection}
    (q : Prepared d) {φ : ℝ} (hφ : 0 < φ) (hφθ : φ < q.θ)
    (hrow₀ : linearMatrix q.eD 1 0 = Real.cos φ)
    (hrow₁ : linearMatrix q.eD 1 1 = Real.sin φ)
    {X Y : Plane} (hX : X ∈ d.piece 0) (hY : Y ∈ d.piece 0)
    (hXtop : q.eD X 1 = 1)
    (hXY₀ : X 0 = Y 0 - (q.m - q.b) * Real.sin φ)
    (hXY₁ : X 1 = Y 1 + (q.m - q.b) * Real.cos φ) : False := by
  apply prefix_face_impossible_of_points
    (h := q.C 0) (k := q.C 1) (b := q.b) (T := 1 - q.m) (j := q.m - q.b)
    (d.piece_subset 0) q.angle.1 q.angle.2 hφ hφθ q.C_height_lt_cos q.b_pos
    (sub_pos.mpr q.b_lt_m) (by ring) q.right_contact_mem q.incoming_arm_endpoint_mem
    hX hY _ _ hXY₀ hXY₁
  · intro p hp
    exact (q.corner_support p hp).1
  · intro p hp
    simpa only [hrow₀, hrow₁] using q.fourth_top_support hX hXtop p hp

/-- A strict prefix normal cannot be the top row of the actual fourth
placement.  The normal and both source endpoints come from that placement. -/
theorem Prepared.prefix_face_impossible {d : SquareDissection} (q : Prepared d)
    {φ : ℝ} (hφ : 0 < φ) (hφθ : φ < q.θ)
    (hrow₀ : linearMatrix q.eD 1 0 = Real.cos φ)
    (hrow₁ : linearMatrix q.eD 1 1 = Real.sin φ) : False := by
  have hunit : Real.cos φ ^ 2 + Real.sin φ ^ 2 = 1 := by
    nlinarith only [Real.sin_sq_add_cos_sq φ]
  have hleftTop : q.eD (q.eD.symm (Schoenflies.Plane.mk q.b 1)) 1 = 1 := by
    rw [q.eD.apply_symm_apply]
    rfl
  have hrightTop : q.eD (q.eD.symm (Schoenflies.Plane.mk q.m 1)) 1 = 1 := by
    rw [q.eD.apply_symm_apply]
    rfl
  rcases eD_top_row_forms q.eD (Real.cos φ) (Real.sin φ) hrow₀ hrow₁ with hform | hform
  · obtain ⟨hx, hy⟩ := eD_top_inverse_endpoints_first hunit hform q.b q.m
    apply prefix_false_of_oriented_endpoints q hφ hφθ hrow₀ hrow₁
      q.D_left_mem q.D_right_mem hleftTop
    · linarith only [hx]
    · linarith only [hy]
  · obtain ⟨hx, hy⟩ := eD_top_inverse_endpoints_second hunit hform q.b q.m
    apply prefix_false_of_oriented_endpoints q hφ hφθ hrow₀ hrow₁
      q.D_right_mem q.D_left_mem hrightTop
    · exact hx
    · exact hy

end Puzzling139335.N5
