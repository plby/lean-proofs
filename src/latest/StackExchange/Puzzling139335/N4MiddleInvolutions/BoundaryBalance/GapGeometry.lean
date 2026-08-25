import StackExchange.Puzzling139335.N4OuterPair.SideGaps
import StackExchange.Puzzling139335.SquareGeometry

/-! The two separated vertical gaps available to middle exterior arcs. -/

open Set

namespace Puzzling139335.N4MiddleInvolutions.BoundaryBalance

/-- The closed middle gap on the vertical line with horizontal coordinate `x`. -/
def verticalGap (x c : ℝ) : Set Plane :=
  segment ℝ (Schoenflies.Plane.mk x c) (Schoenflies.Plane.mk x (1 - c))

theorem verticalGap_coord {x c : ℝ} {z : Plane} (hz : z ∈ verticalGap x c) :
    z 0 = x :=
  (Schoenflies.mem_segment_vert.mp hz).1

theorem mem_verticalGap_iff {x c : ℝ} {z : Plane} (hc : c ≤ 1 / 2) :
    z ∈ verticalGap x c ↔ z 0 = x ∧ z 1 ∈ Icc c (1 - c) := by
  rw [verticalGap, Schoenflies.mem_segment_vert,
    segment_eq_Icc (by linarith only [hc] : c ≤ 1 - c)]

theorem verticalGap_endpoint_distance (x : ℝ) {c : ℝ} (hc : c ≤ 1 / 2) :
    dist (Schoenflies.Plane.mk x c) (Schoenflies.Plane.mk x (1 - c)) = 1 - 2 * c := by
  apply (sq_eq_sq₀ dist_nonneg (by linarith only [hc] : 0 ≤ 1 - 2 * c)).mp
  simp [plane_dist_sq, Schoenflies.Plane.mk]
  ring

/-- A square-boundary point strictly between the two horizontal sides lies
on one of the vertical sides. -/
theorem frontier_square_point_on_vertical_side {z : Plane}
    (hz : z ∈ frontier unitSquare) (hz0 : 0 < z 1) (hz1 : z 1 < 1) :
    z 0 = 0 ∨ z 0 = 1 := by
  have hzS : z ∈ unitSquare := isClosed_unitSquare.closure_eq ▸ hz.1
  by_cases hzero : z 0 = 0
  · exact Or.inl hzero
  by_cases hone : z 0 = 1
  · exact Or.inr hone
  exfalso
  apply hz.2
  change z ∈ interior (horizontalBand 0 1)
  apply (mem_interior_horizontalBand_iff 0 1 z).mpr
  exact ⟨⟨lt_of_le_of_ne hzS.1.1 (Ne.symm hzero),
    lt_of_le_of_ne hzS.1.2 hone⟩, hz0, hz1⟩

/-- A connected set contained in the two vertical gaps stays entirely in
one of them, since its horizontal coordinate cannot pass through `1/2`. -/
theorem preconnected_subset_one_verticalGap {A : Set Plane} {a b : ℝ}
    (hA : IsPreconnected A) (hsub : A ⊆ verticalGap 0 a ∪ verticalGap 1 b) :
    A ⊆ verticalGap 0 a ∨ A ⊆ verticalGap 1 b := by
  have hne : ∀ z ∈ A, z 0 ≠ (1 / 2 : ℝ) := by
    intro z hz
    rcases hsub hz with hzL | hzR
    · rw [verticalGap_coord hzL]
      norm_num
    · rw [verticalGap_coord hzR]
      norm_num
  rcases hA.mapsTo_Ioi_or_Iio (Schoenflies.Plane.continuous_coord 0).continuousOn hne with
    hright | hleft
  · right
    intro z hz
    rcases hsub hz with hzL | hzR
    · have hlt := hright hz
      change (1 / 2 : ℝ) < z 0 at hlt
      rw [verticalGap_coord hzL] at hlt
      norm_num at hlt
    · exact hzR
  · left
    intro z hz
    rcases hsub hz with hzL | hzR
    · exact hzL
    · have hlt := hleft hz
      change z 0 < (1 / 2 : ℝ) at hlt
      rw [verticalGap_coord hzR] at hlt
      norm_num at hlt

end Puzzling139335.N4MiddleInvolutions.BoundaryBalance
