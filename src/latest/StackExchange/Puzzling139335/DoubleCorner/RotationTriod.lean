import StackExchange.Puzzling139335.DoubleCorner.RotationBoundary
import StackExchange.Puzzling139335.DoubleCorner.RotationAlgebra
import StackExchange.Puzzling139335.DoubleCorner.Triod
import StackExchange.Puzzling139335.DoubleCorner.RotationParameters
import StackExchange.Puzzling139335.SquareGeometry

/-!
# A double corner excludes rotations smaller than forty-five degrees

Three genuine radial segments would otherwise lie in the boundary of one
Jordan piece: a short outer side and its first two rotated images.
-/

open Set Metric

namespace Puzzling139335.DoubleCorner

open PlaneIsometries

theorem positive_rotation_double_corner_cos_le_sin
    {P Q : Set Plane} (hP : IsJordanRegion P) (hQ : IsJordanRegion Q)
    (hPsub : P ⊆ unitSquare) (hQsub : Q ⊆ unitSquare)
    (hdis : Disjoint (interior P) (interior Q)) (hzero : (0 : Plane) ∈ P)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (hePQ : e '' P = Q)
    {c s : ℝ} (hc : 0 < c) (hs : 0 < s)
    (he : ∀ p, e p = directCoordinates c s 0 p)
    {ε : ℝ} (hε : 0 < ε)
    (hcover : ball 0 ε ∩ unitSquare ⊆ P ∪ Q) : c ≤ s := by
  by_contra hnle
  have hsc : s < c := lt_of_not_ge hnle
  let t : ℝ := min (ε / 2) (1 / 2 : ℝ)
  have ht : 0 < t := lt_min (by positivity) (by norm_num)
  have htε : t < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have ht1 : t < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  let a : Plane := !₂[t, 0]
  let A : Set Plane := segment ℝ (0 : Plane) a
  have hadist : dist a 0 = t := by
    apply (sq_eq_sq₀ dist_nonneg ht.le).mp
    rw [plane_dist_sq]
    simp [a]
  have ha : a ≠ 0 := by
    intro h
    have h0 := congrArg (fun p : Plane => p 0) h
    exact ht.ne' (by simpa [a] using h0)
  have hAε : A ⊆ ball 0 ε :=
    (convex_ball (0 : Plane) ε).segment_subset (mem_ball_self hε)
      (mem_ball.mpr (hadist ▸ htε))
  have hA1 : A ⊆ ball 0 1 :=
    (convex_ball (0 : Plane) 1).segment_subset (mem_ball_self zero_lt_one)
      (mem_ball.mpr (hadist ▸ ht1))
  have hAc (x : Plane) (hx : x ∈ A) : 0 ≤ x 0 ∧ x 0 ≤ t ∧ x 1 = 0 :=
    bottom_segment_coordinates ht.le hx
  have hAsub : A ⊆ unitSquare := by
    intro x hx
    obtain ⟨hx0, hx0t, hx1⟩ := hAc x hx
    exact ⟨⟨hx0, hx0t.trans ht1.le⟩, by simp [hx1]⟩
  have hAfront : A ⊆ frontier P := by
    intro x hx
    exact bottom_point_frontier_of_local_rotation_cover hP.isClosed hPsub hQsub
      hzero e hePQ hc hs he hcover (hAε hx) (hAsub hx) (hAc x hx).2.2
  have h0front : (0 : Plane) ∈ frontier P :=
    hAfront (left_mem_segment ℝ 0 a)
  have he0 : e 0 = 0 := normalized_rotation_fixes_zero e he
  have he_ball (r : ℝ) : e '' ball (0 : Plane) r = ball 0 r := by
    have h := e.toIsometryEquiv.image_ball 0 r
    change e '' ball 0 r = ball (e 0) r at h
    simpa only [he0] using h
  have hBε : e '' A ⊆ ball 0 ε := by
    rw [← he_ball ε]
    exact image_mono hAε
  have hB1 : e '' A ⊆ ball 0 1 := by
    rw [← he_ball 1]
    exact image_mono hA1
  have hCε : e '' (e '' A) ⊆ ball 0 ε := by
    rw [← he_ball ε]
    exact image_mono hBε
  have hC1 : e '' (e '' A) ⊆ ball 0 1 := by
    rw [← he_ball 1]
    exact image_mono hB1
  have hApos (x : Plane) (hx : x ∈ A) (hxne : x ≠ 0) : 0 < x 0 := by
    obtain ⟨hx0, _, hx1⟩ := hAc x hx
    by_contra hxnot
    have hxzero : x 0 = 0 := le_antisymm (le_of_not_gt hxnot) hx0
    exact hxne (plane_ext hxzero hx1)
  have hBint (x : Plane) (hx : x ∈ e '' A) (hxne : x ≠ 0) :
      x ∈ interior unitSquare := by
    obtain ⟨y, hy, rfl⟩ := hx
    have hyne : y ≠ 0 := by intro h; exact hxne (h ▸ he0)
    obtain ⟨h0, h1⟩ := rotation_bottom_ray_pos e hc hs he
      (hApos y hy hyne) (hAc y hy).2.2
    exact interior_unitSquare_of_pos_of_mem_ball_one h0 h1
      (hB1 (mem_image_of_mem e hy))
  have hBfront : e '' A ⊆ frontier P :=
    rotated_boundary_subset hP.isClosed hQ.isClosed (hQ.disjoint_interior_left hdis)
      e hePQ hcover h0front hAfront hBε hBint
  have hCint (x : Plane) (hx : x ∈ e '' (e '' A)) (hxne : x ≠ 0) :
      x ∈ interior unitSquare := by
    obtain ⟨_, ⟨y, hy, rfl⟩, rfl⟩ := hx
    have hyne : y ≠ 0 := by
      intro h
      apply hxne
      rw [h, he0, he0]
    obtain ⟨h0, h1⟩ := rotation_twice_bottom_ray_pos e hc hs hsc he
      (hApos y hy hyne) (hAc y hy).2.2
    exact interior_unitSquare_of_pos_of_mem_ball_one h0 h1
      (hC1 (mem_image_of_mem e (mem_image_of_mem e hy)))
  have hCfront : e '' (e '' A) ⊆ frontier P :=
    rotated_boundary_subset hP.isClosed hQ.isClosed (hQ.disjoint_interior_left hdis)
      e hePQ hcover h0front hBfront hCε hCint
  have hAarc : Schoenflies.IsArcBetween A 0 a := Schoenflies.isArcBetween_segment ha.symm
  have hBarc : Schoenflies.IsArcBetween (e '' A) 0 (e a) := by
    have h := hAarc.image_homeomorph e.toHomeomorph
    change Schoenflies.IsArcBetween (e '' A) (e 0) (e a) at h
    simpa only [he0] using h
  have hCarc : Schoenflies.IsArcBetween (e '' (e '' A)) 0 (e (e a)) := by
    have h := hBarc.image_homeomorph e.toHomeomorph
    change Schoenflies.IsArcBetween (e '' (e '' A)) (e 0) (e (e a)) at h
    simpa only [he0] using h
  obtain ⟨hAB, hAC, hBC⟩ := bottom_rotation_trio_intersections e ht hc hs hsc he
  exact hP.frontier_isJordanCurve.no_three_endpoint_arcs hAarc hBarc hCarc
    hAfront hBfront hCfront hAB hAC hBC

end Puzzling139335.DoubleCorner
