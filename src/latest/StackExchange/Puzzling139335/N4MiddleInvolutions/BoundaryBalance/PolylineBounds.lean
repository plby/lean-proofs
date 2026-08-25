import StackExchange.Puzzling139335.N4MiddleInvolutions.BoundaryBalance.SegmentBounds.StraightVariation
import StackExchange.Puzzling139335.LoopVariation.Geometric.ArcCuts
import StackExchange.Puzzling139335.SquareGeometry
import Wikipedia.SchoenfliesTheorem.ModelCurve

/-! Quantitative variation of the three straight sides of an outer boundary arc. -/

open Set

namespace Puzzling139335.N4MiddleInvolutions.BoundaryBalance

/-- Concatenation preserves the three endpoint-distance lower bounds, with
one finite-resolution penalty for each straight side. -/
theorem three_segments_variation_lower {p q r s : Plane} {ε : ℝ}
    (hpq : p ≠ q) (hqr : q ≠ r) (hrs : r ≠ s)
    (hmeetAB : ∀ z ∈ segment ℝ p q, z ∈ segment ℝ q r → z = q)
    (hmeetC : ∀ z ∈ segment ℝ p q ∪ segment ℝ q r,
      z ∈ segment ℝ r s → z = r)
    (hε : 0 < ε) :
    dist p q + dist q r + dist r s - 3 * ε ≤
      LoopVariation.arcVariation ε
        ((segment ℝ p q ∪ segment ℝ q r) ∪ segment ℝ r s) := by
  have hp := dist_sub_le_arcVariation_segment hε hpq
  have hq := dist_sub_le_arcVariation_segment hε hqr
  have hr := dist_sub_le_arcVariation_segment hε hrs
  have hsum := (LoopVariation.arcVariation_three_arc_bounds
    (Schoenflies.isArcBetween_segment hpq) (Schoenflies.isArcBetween_segment hqr)
    (Schoenflies.isArcBetween_segment hrs) hmeetAB hmeetC hε).1
  linarith

/-- The U-shaped lower contact arc has variation approaching its explicit
length from below, regardless of the other tile boundary arcs. -/
theorem lower_three_sides_variation_lower {a b ε : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hε : 0 < ε) :
    1 + a + b - 3 * ε ≤
      LoopVariation.arcVariation ε
        ((segment ℝ (Schoenflies.Plane.mk 0 a) (Schoenflies.Plane.mk 0 0) ∪
          segment ℝ (Schoenflies.Plane.mk 0 0) (Schoenflies.Plane.mk 1 0)) ∪
          segment ℝ (Schoenflies.Plane.mk 1 0) (Schoenflies.Plane.mk 1 b)) := by
  have hleft : Schoenflies.Plane.mk 0 a ≠ Schoenflies.Plane.mk 0 0 := by
    intro heq
    exact (ne_of_gt ha) (congrArg (fun z : Plane => z 1) heq)
  have hbase : Schoenflies.Plane.mk 0 0 ≠ Schoenflies.Plane.mk 1 0 := by
    intro heq
    have h := congrArg (fun z : Plane => z 0) heq
    norm_num at h
  have hright : Schoenflies.Plane.mk 1 0 ≠ Schoenflies.Plane.mk 1 b := by
    intro heq
    exact (ne_of_lt hb) (congrArg (fun z : Plane => z 1) heq)
  have hmeetAB : ∀ z ∈ segment ℝ (Schoenflies.Plane.mk 0 a) (Schoenflies.Plane.mk 0 0),
      z ∈ segment ℝ (Schoenflies.Plane.mk 0 0) (Schoenflies.Plane.mk 1 0) →
      z = Schoenflies.Plane.mk 0 0 := by
    intro z hzA hzB
    have hz0 := (Schoenflies.mem_segment_vert.mp hzA).1
    have hz1 := (Schoenflies.mem_segment_horiz.mp hzB).1
    ext i
    fin_cases i
    · exact hz0
    · exact hz1
  have hmeetC : ∀ z ∈
      segment ℝ (Schoenflies.Plane.mk 0 a) (Schoenflies.Plane.mk 0 0) ∪
        segment ℝ (Schoenflies.Plane.mk 0 0) (Schoenflies.Plane.mk 1 0),
      z ∈ segment ℝ (Schoenflies.Plane.mk 1 0) (Schoenflies.Plane.mk 1 b) →
      z = Schoenflies.Plane.mk 1 0 := by
    intro z hzAB hzC
    have hz0 := (Schoenflies.mem_segment_vert.mp hzC).1
    rcases hzAB with hzA | hzB
    · have hz0' := (Schoenflies.mem_segment_vert.mp hzA).1
      exact False.elim (by linarith)
    · have hz1 := (Schoenflies.mem_segment_horiz.mp hzB).1
      ext i
      fin_cases i
      · exact hz0
      · exact hz1
  have hdleft : dist (Schoenflies.Plane.mk 0 a) (Schoenflies.Plane.mk 0 0) = a := by
    apply (sq_eq_sq₀ dist_nonneg ha.le).mp
    simp [plane_dist_sq, Schoenflies.Plane.mk]
  have hdbase : dist (Schoenflies.Plane.mk 0 0) (Schoenflies.Plane.mk 1 0) = 1 := by
    apply (sq_eq_sq₀ dist_nonneg zero_le_one).mp
    norm_num [plane_dist_sq, Schoenflies.Plane.mk]
  have hdright : dist (Schoenflies.Plane.mk 1 0) (Schoenflies.Plane.mk 1 b) = b := by
    apply (sq_eq_sq₀ dist_nonneg hb.le).mp
    simp [plane_dist_sq, Schoenflies.Plane.mk]
  have hbound := three_segments_variation_lower hleft hbase hright hmeetAB hmeetC hε
  simpa only [hdleft, hdbase, hdright, add_comm a 1] using hbound

end Puzzling139335.N4MiddleInvolutions.BoundaryBalance
