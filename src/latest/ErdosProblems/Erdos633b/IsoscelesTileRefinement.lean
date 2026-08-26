import ErdosProblems.Erdos633b.IsoscelesHalfAngles
import ErdosProblems.Erdos633b.RightTileNecessity
import ErdosProblems.Erdos633b.VeryObtuseNecessity
import ErdosProblems.Erdos633b.RationalAngleSides

/-! Right-half refinement and original-corner comparisons restrict an
isosceles reference tile in a dissection of a scalene outer triangle. -/

namespace Erdos633b

theorem tile_angles_injective_of_reptiling {S T : Triangle} (h : ReptilingAngles S T)
    (hscalene : Function.Injective T.angle) : Function.Injective S.angle := by
  obtain ⟨e, he⟩ := h
  intro i j hij
  apply e.symm.injective
  apply hscalene
  simpa only [he, Equiv.apply_symm_apply] using hij

namespace Tiling

theorem isosceles_half_permutation {T : Triangle} {n : ℕ} (d : Tiling T n)
    (heq : d.tile.angle 0 = d.tile.angle 1) (hscalene : Function.Injective T.angle) :
    ∃ e : Equiv.Perm (Fin 3), ∀ j, T.angle (e j) = d.tile.firstHalf.angle j := by
  let h := isosceles_tiling d.tile (d.tile.isosceles_legs_of_base_angles heq)
  let d' := d.refine h
  have hr : d'.tile.angle 2 = Real.pi / 2 := d.tile.firstHalf_angle_two_of_isosceles heq
  obtain ⟨e, he⟩ := d'.reptiling_of_right_tile 2 hr hscalene
  change ∀ i, T.angle i = d.tile.firstHalf.angle (e i) at he
  refine ⟨e.symm, ?_⟩
  intro j
  simpa only [Equiv.apply_symm_apply] using he (e.symm j)

theorem isosceles_base_angle_lt_pi_four {T : Triangle} {n : ℕ} (d : Tiling T n)
    (heq : d.tile.angle 0 = d.tile.angle 1) (hscalene : Function.Injective T.angle) :
    d.tile.angle 0 < Real.pi / 4 := by
  obtain ⟨e, he⟩ := d.isosceles_half_permutation heq hscalene
  have h0 : T.angle (e 0) = Real.pi / 2 - d.tile.angle 0 := by
    rw [he, d.tile.firstHalf_angle_zero_of_isosceles heq]
  have h1 : T.angle (e 1) = d.tile.angle 0 := by rw [he, d.tile.firstHalf_angle_one]
  obtain ⟨j, hj⟩ := d.corner_row_positive (e 0)
  have hle := d.tile_angle_le_outer_of_corner_count_pos (e 0) j hj
  have hα : d.tile.angle 0 ≤ Real.pi / 4 := by
    fin_cases j
    · change d.tile.angle 0 ≤ T.angle (e 0) at hle
      linarith
    · change d.tile.angle 1 ≤ T.angle (e 0) at hle
      linarith
    · change d.tile.angle 2 ≤ T.angle (e 0) at hle
      linarith [d.tile.angle_sum, d.tile.firstHalf.angle_pos 0,
        d.tile.firstHalf_angle_zero_of_isosceles heq]
  apply lt_of_le_of_ne hα
  intro hαeq
  have hsame : T.angle (e 0) = T.angle (e 1) := by linarith
  have hindex := e.injective (hscalene hsame)
  exact (by decide : (0 : Fin 3) ≠ 1) hindex

theorem isosceles_base_angle_ge_pi_six {T : Triangle} {n : ℕ} (d : Tiling T n)
    (heq : d.tile.angle 0 = d.tile.angle 1) (hscalene : Function.Injective T.angle) :
    Real.pi / 6 ≤ d.tile.angle 0 := by
  by_contra hn
  have hlarge : 2 * Real.pi / 3 < d.tile.angle 2 := by linarith [d.tile.angle_sum]
  have hrep := d.reptiling_of_very_obtuse_tile 2 hlarge hscalene
  have hi := tile_angles_injective_of_reptiling hrep hscalene
  exact (by decide : (0 : Fin 3) ≠ 1) (hi heq)

theorem isosceles_base_angle_eq_pi_six {T : Triangle} {n : ℕ} (d : Tiling T n)
    (heq : d.tile.angle 0 = d.tile.angle 1) (hscalene : Function.Injective T.angle) :
    d.tile.angle 0 = Real.pi / 6 := by
  obtain ⟨e, he⟩ := d.isosceles_half_permutation heq hscalene
  have hright : T.angle (e 2) = Real.pi / 2 := by
    rw [he, d.tile.firstHalf_angle_two_of_isosceles heq]
  have ha := d.isosceles_base_angle_lt_pi_four heq hscalene
  have hb := d.isosceles_base_angle_ge_pi_six heq hscalene
  have hγ : Real.pi / 2 < d.tile.angle 2 := by linarith [d.tile.angle_sum]
  have hz : d.cornerAngleCount (e 2) 2 = 0 := by
    by_contra hn
    have hle := d.tile_angle_le_outer_of_corner_count_pos (e 2) 2 (Nat.pos_of_ne_zero hn)
    linarith
  let m := d.cornerAngleCount (e 2) 0 + d.cornerAngleCount (e 2) 1
  have hm : (m : ℝ) * d.tile.angle 0 = Real.pi / 2 := by
    have hc := d.angle_eq_three_counts (e 2)
    rw [← heq, hz, Nat.cast_zero, zero_mul, add_zero, hright] at hc
    dsimp only [m]
    push_cast
    linear_combination -hc
  have hmgt : 2 < m := by
    by_contra h
    have hcast : (m : ℝ) ≤ 2 := by exact_mod_cast (show m ≤ 2 by omega)
    have hmul := mul_le_mul_of_nonneg_right hcast (d.tile.angle_pos 0).le
    linarith
  have hmle : m ≤ 3 := by
    by_contra h
    have hcast : (4 : ℝ) ≤ m := by exact_mod_cast (show 4 ≤ m by omega)
    have hmul := mul_le_mul_of_nonneg_right hcast (d.tile.angle_pos 0).le
    linarith [Real.pi_pos]
  have hm3 : m = 3 := by omega
  rw [hm3] at hm
  norm_num at hm
  linarith

end Tiling
end Erdos633b
