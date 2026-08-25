import StackExchange.Puzzling139335.DoubleCorner.LocalCover
import StackExchange.Puzzling139335.JordanTransport
import StackExchange.Puzzling139335.PlaneIsometries
import StackExchange.Puzzling139335.SquareSymmetry.SideRigidity.Normalized

/-!
# Rotating actual boundary points at a double corner

The first short square-side segment belongs to one of the two pieces.
Its rotated images, when they lie in the interior of the square, also
belong to that piece's boundary by local coverage.
-/

open Set Metric

namespace Puzzling139335.DoubleCorner

open PlaneIsometries

theorem interior_unitSquare_of_coordinates {p : Plane}
    (h0 : p 0 ∈ Ioo (0 : ℝ) 1) (h1 : p 1 ∈ Ioo (0 : ℝ) 1) :
    p ∈ interior unitSquare := by
  let U : Set Plane := {q | q 0 ∈ Ioo (0 : ℝ) 1 ∧ q 1 ∈ Ioo (0 : ℝ) 1}
  have hU : IsOpen U :=
    (isOpen_Ioo.preimage (EuclideanSpace.proj (0 : Fin 2)).continuous).inter
      (isOpen_Ioo.preimage (EuclideanSpace.proj (1 : Fin 2)).continuous)
  have hsub : U ⊆ unitSquare := by
    intro q hq
    exact ⟨⟨hq.1.1.le, hq.1.2.le⟩, ⟨hq.2.1.le, hq.2.2.le⟩⟩
  exact hU.subset_interior_iff.mpr hsub ⟨h0, h1⟩

theorem interior_unitSquare_of_pos_of_mem_ball_one {p : Plane}
    (h0 : 0 < p 0) (h1 : 0 < p 1) (hp : p ∈ ball 0 1) :
    p ∈ interior unitSquare := by
  have hn : ‖p‖ < 1 := by simpa using mem_ball.mp hp
  have hc (i : Fin 2) : p i < 1 := by
    have hpi : |p i| ≤ ‖p‖ := by simpa using PiLp.norm_apply_le p i
    exact lt_of_le_of_lt (le_trans (le_abs_self _) hpi) hn
  exact interior_unitSquare_of_coordinates ⟨h0, hc 0⟩ ⟨h1, hc 1⟩

theorem bottom_point_frontier_of_local_rotation_cover
    {P Q : Set Plane} (hP : IsClosed P) (hPsub : P ⊆ unitSquare)
    (hQsub : Q ⊆ unitSquare) (hzero : (0 : Plane) ∈ P)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (hePQ : e '' P = Q)
    {c s : ℝ} (hc : 0 < c) (hs : 0 < s)
    (he : ∀ p, e p = directCoordinates c s 0 p)
    {ε : ℝ} (hcover : ball 0 ε ∩ unitSquare ⊆ P ∪ Q)
    {x : Plane} (hxball : x ∈ ball 0 ε) (hxSquare : x ∈ unitSquare)
    (hx1 : x 1 = 0) : x ∈ frontier P := by
  have hxP : x ∈ P := by
    rcases hcover ⟨hxball, hxSquare⟩ with hxP | hxQ
    · exact hxP
    · obtain ⟨y, hy, hxy⟩ := (Set.ext_iff.mp hePQ x).mpr hxQ
      have hyS := hPsub hy
      have heq : s * y 0 + c * y 1 = 0 := by
        have h := congrArg (fun p : Plane => p 1) hxy
        simpa [he, directCoordinates, hx1] using h
      have hsy : s * y 0 = 0 := by
        have hcy := mul_nonneg hc.le hyS.2.1
        have hsy := mul_nonneg hs.le hyS.1.1
        linarith
      have hcy : c * y 1 = 0 := by linarith
      have hy0 : y 0 = 0 := (mul_eq_zero.mp hsy).resolve_left hs.ne'
      have hy1 : y 1 = 0 := (mul_eq_zero.mp hcy).resolve_left hc.ne'
      have hyzero : y = 0 := plane_ext hy0 hy1
      have hxzero : x = 0 := by
        rw [← hxy, hyzero, he]
        ext i
        fin_cases i <;> simp [directCoordinates]
      exact hxzero ▸ hzero
  rw [hP.frontier_eq]
  refine ⟨hxP, ?_⟩
  intro hxint
  have hcoord := SquareSymmetry.interior_unitSquare_coordinates (interior_mono hPsub hxint)
  exact (ne_of_gt hcoord.2.1) hx1

/-- A rotated boundary set that stays locally inside the square is again
part of the source boundary, since only the two pieces occur nearby. -/
theorem rotated_boundary_subset
    {P Q A : Set Plane} (hP : IsClosed P) (hQ : IsClosed Q)
    (hdis : Disjoint (interior P) Q)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (hePQ : e '' P = Q)
    {ε : ℝ} (hcover : ball 0 ε ∩ unitSquare ⊆ P ∪ Q)
    (hzero : (0 : Plane) ∈ frontier P) (hA : A ⊆ frontier P)
    (hball : e '' A ⊆ ball 0 ε)
    (hint : ∀ x ∈ e '' A, x ≠ 0 → x ∈ interior unitSquare) :
    e '' A ⊆ frontier P := by
  intro x hx
  by_cases hx0 : x = 0
  · exact hx0 ▸ hzero
  apply frontier_switch_of_local_cover hP hQ hdis hcover (hball hx) (hint x hx hx0)
  have hf : e '' frontier P = frontier (e '' P) := e.toHomeomorph.image_frontier P
  rw [← hePQ, ← hf]
  exact image_mono hA hx

/-- Positive coordinates of the first rotated ray. -/
theorem rotation_bottom_ray_pos
    (e : Plane ≃ᵃⁱ[ℝ] Plane) {c s : ℝ} (hc : 0 < c) (hs : 0 < s)
    (he : ∀ p, e p = directCoordinates c s 0 p)
    {x : Plane} (hx0 : 0 < x 0) (hx1 : x 1 = 0) :
    0 < e x 0 ∧ 0 < e x 1 := by
  rw [he]
  simpa [directCoordinates, hx1] using
    And.intro (mul_pos hc hx0) (mul_pos hs hx0)

/-- For a rotation smaller than 45 degrees, the second rotated ray is
also strictly inside the positive quadrant. -/
theorem rotation_twice_bottom_ray_pos
    (e : Plane ≃ᵃⁱ[ℝ] Plane) {c s : ℝ} (hc : 0 < c) (hs : 0 < s)
    (hsc : s < c) (he : ∀ p, e p = directCoordinates c s 0 p)
    {x : Plane} (hx0 : 0 < x 0) (hx1 : x 1 = 0) :
    0 < e (e x) 0 ∧ 0 < e (e x) 1 := by
  have h0 : e (e x) 0 = (c - s) * (c + s) * x 0 := by
    rw [he (e x), he x]
    simp [directCoordinates, hx1]
    ring
  have h1 : e (e x) 1 = 2 * c * s * x 0 := by
    rw [he (e x), he x]
    simp [directCoordinates, hx1]
    ring
  rw [h0, h1]
  constructor
  · exact mul_pos (mul_pos (sub_pos.mpr hsc) (add_pos hc hs)) hx0
  · exact mul_pos (mul_pos (mul_pos (by norm_num) hc) hs) hx0

end Puzzling139335.DoubleCorner
