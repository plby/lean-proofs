import StackExchange.Puzzling139335.N7.ThirdPlacement
import StackExchange.Puzzling139335.ReflectionSeparation
import StackExchange.Puzzling139335.DoubleCorner.Reflection

/-!
# The gap between the two known copies at the top-right corner

The matrix forced by the actual third placement leaves a diagonal gap
between that image and the horizontal reflection of the source.  The
proof is a coordinate inequality for actual set images.  It needs no
angle measure, polygonal germ, or auxiliary sector hypothesis.
-/

open Set Metric

namespace Puzzling139335.N7

open ReflectionSeparation

noncomputable section

def nearTopRight (t : ℝ) : Plane := !₂[1 - t, 1 - t]

/-- The two endpoints of a segment lying across the gap at scale one quarter. -/
def gapLeft (c s : ℝ) : Plane := !₂[1 - c / 4, 1 - s / 4]

def gapRight (c s : ℝ) : Plane := !₂[1 - s / 4, 1 - c / 4]

theorem source_cosine_gt_sine (e : Plane ≃ᵃⁱ[ℝ] Plane) {b : Plane}
    (hbsquare : b ∈ unitSquare) (hhalf : b 1 ≤ (1 / 2 : ℝ))
    (hne : b ≠ corner 0)
    (ha : e (corner 1) = corner 2) (hb : e b = corner 1) :
    b 1 < 1 - b 0 := by
  have hunit := source_parameters_unit e ha hb
  have hpos := source_parameters_positive e hbsquare hhalf hne ha hb
  by_contra hnot
  have hle : 1 - b 0 ≤ b 1 := le_of_not_gt hnot
  have hsquare := mul_self_le_mul_self hpos.2.le hle
  nlinarith only [hunit, hhalf, hpos.1, hsquare]

theorem thirdMap_inverse_second {c s : ℝ} (hunit : c ^ 2 + s ^ 2 = 1)
    (p : Plane) :
    c * ((thirdMap c s p) 0 - 1) - s * ((thirdMap c s p) 1 - 1) = p 1 := by
  simp only [thirdMap, Matrix.cons_val_zero, Matrix.cons_val_one]
  linear_combination p 1 * hunit

theorem nearTopRight_not_mem_horizontal {P : Set Plane} {c s t : ℝ}
    (hst : s < c) (ht : 0 < t)
    (hsupport : ∀ p ∈ P, c * p 1 ≤ s * (1 - p 0)) :
    nearTopRight t ∉ horizontal '' P := by
  rintro ⟨p, hp, heq⟩
  have hx := congrArg (fun q : Plane => q 0) heq
  have hy := congrArg (fun q : Plane => q 1) heq
  simp only [horizontal_apply_zero, horizontal_apply_one, nearTopRight,
    Matrix.cons_val_zero, Matrix.cons_val_one] at hx hy
  have hs := hsupport p hp
  have hpositive := mul_pos (sub_pos.mpr hst) ht
  have hpy : p 1 = t := by linarith only [hy]
  rw [hx, hpy] at hs
  nlinarith only [hs, hpositive]

theorem nearTopRight_not_mem_thirdMap {P : Set Plane} {c s t : ℝ}
    (hP : P ⊆ unitSquare) (hunit : c ^ 2 + s ^ 2 = 1)
    (hst : s < c) (ht : 0 < t) : nearTopRight t ∉ thirdMap c s '' P := by
  rintro ⟨p, hp, heq⟩
  have hinverse := thirdMap_inverse_second hunit p
  rw [heq] at hinverse
  simp only [nearTopRight, Matrix.cons_val_zero, Matrix.cons_val_one] at hinverse
  have hnonneg := (hP hp).2.1
  have hpositive := mul_pos (sub_pos.mpr hst) ht
  nlinarith only [hinverse, hnonneg, hpositive]

/-- Every positive ball at the top-right corner contains a strict
diagonal point of the square. -/
theorem exists_nearTopRight_mem_ball {ε : ℝ} (hε : 0 < ε) :
    ∃ t : ℝ, 0 < t ∧ nearTopRight t ∈ ball (corner 2) ε ∩ unitSquare := by
  let t : ℝ := min (ε / 4) (1 / 4)
  have ht : 0 < t := lt_min (by positivity) (by norm_num)
  have htε : t ≤ ε / 4 := min_le_left _ _
  have htquarter : t ≤ 1 / 4 := min_le_right _ _
  have hfour : 4 * t ≤ ε := by linarith only [htε]
  have hsq : (4 * t) ^ 2 ≤ ε ^ 2 := by
    simpa only [pow_two] using mul_self_le_mul_self (by positivity : 0 ≤ 4 * t) hfour
  have hdist : dist (nearTopRight t) (corner 2) ^ 2 = 2 * t ^ 2 := by
    rw [plane_dist_sq]
    norm_num [nearTopRight, corner, Fin.ext_iff]
    ring
  refine ⟨t, ht, ?_, ?_⟩
  · apply mem_ball.mpr
    apply (sq_lt_sq₀ dist_nonneg hε.le).mp
    rw [hdist]
    nlinarith only [hsq, sq_pos_of_pos ht]
  · change (0 ≤ 1 - t ∧ 1 - t ≤ 1) ∧ (0 ≤ 1 - t ∧ 1 - t ≤ 1)
    exact ⟨⟨by linarith only [htquarter], by linarith only [ht]⟩,
      ⟨by linarith only [htquarter], by linarith only [ht]⟩⟩

/-- The two actual normalized images do not cover any square
neighborhood of the top-right corner. -/
theorem not_topRight_local_cover {P : Set Plane} (e : Plane ≃ᵃⁱ[ℝ] Plane)
    {b : Plane} (hP : P ⊆ unitSquare) (hbsquare : b ∈ unitSquare)
    (hhalf : b 1 ≤ (1 / 2 : ℝ)) (hne : b ≠ corner 0)
    (ha : e (corner 1) = corner 2) (hb : e b = corner 1)
    (hzero : e (corner 0) ∈ unitSquare) (hfit : e '' P ⊆ unitSquare)
    {ε : ℝ} (hε : 0 < ε) :
    ¬ ball (corner 2) ε ∩ unitSquare ⊆ horizontal '' P ∪ e '' P := by
  intro hcover
  obtain ⟨t, ht, hpoint⟩ := exists_nearTopRight_mem_ball hε
  have hunit := source_parameters_unit e ha hb
  have hst := source_cosine_gt_sine e hbsquare hhalf hne ha hb
  rcases hcover hpoint with hH | hT
  · exact nearTopRight_not_mem_horizontal hst ht
      (third_placement_support e hbsquare hhalf hne ha hb hzero hfit) hH
  · have hT' : nearTopRight t ∈ thirdMap (1 - b 0) (b 1) '' P := by
      simpa only [third_placement_formula e hbsquare hhalf hne ha hb hzero] using hT
    exact nearTopRight_not_mem_thirdMap hP hunit hst ht hT'

/-- In an actual normalized dissection, a third piece must also occur
at the top-right corner. -/
theorem topRight_has_other_owner (d : SquareDissection)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) {b : Plane}
    (hH : horizontal '' d.piece 0 = d.piece 1)
    (hT : e '' d.piece 0 = d.piece 2)
    (hbsquare : b ∈ unitSquare) (hhalf : b 1 ≤ (1 / 2 : ℝ))
    (hne : b ≠ corner 0)
    (ha : e (corner 1) = corner 2) (hb : e b = corner 1)
    (hzero : e (corner 0) ∈ unitSquare) :
    ∃ i : Fin 4, i ≠ 1 ∧ i ≠ 2 ∧ corner 2 ∈ d.piece i := by
  by_contra hnone
  have hother : ∀ i : Fin 4, i ≠ 1 → i ≠ 2 → corner 2 ∉ d.piece i := by
    intro i hi1 hi2 hmem
    exact hnone ⟨i, hi1, hi2, hmem⟩
  obtain ⟨ε, hε, hnear⟩ := d.two_piece_relative_neighborhood hother
  apply not_topRight_local_cover e (d.piece_subset 0) hbsquare hhalf hne ha hb hzero
    (by simpa only [hT] using d.piece_subset 2) hε
  simpa only [hH, hT] using hnear

end

end Puzzling139335.N7
