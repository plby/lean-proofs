import ErdosProblems.Erdos633b.EvenAngleTurns
import ErdosProblems.Erdos633b.GroupOneSignedPerimeter

/-! The exact X-Y+Z coloring equation for case (7), with a positive
integer coloring count, derived from the actual oriented outer edges. -/

namespace Erdos633b.Tiling

local instance : Fact (Module.finrank ℝ Plane = 2) := ⟨by simp [Plane]⟩

theorem caseSeven_coloring_equation {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hrel : 3 * d.tile.angle 0 + 2 * d.tile.angle 1 = Real.pi)
    (hirr : Irrational (d.tile.angle 0 / Real.pi))
    (h1 : T.angle 1 = d.tile.angle 1)
    (h2 : T.angle 2 = d.tile.angle 0 + d.tile.angle 1) :
    ∃ M : ℤ, 0 < M ∧ (M : ℝ) * (d.tile.side 0 + d.tile.side 1 + d.tile.side 2) =
      T.side 0 - T.side 1 + T.side 2 := by
  let o : Orientation ℝ Plane (Fin 2) := (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.orientation
  let u : Plane := d.tile.points 1 - d.tile.points 0
  have hu : u ≠ 0 := sub_ne_zero.mpr (d.tile.independent.injective.ne (by decide))
  obtain ⟨f, hf, ht, _⟩ := d.tile.exists_groupOne_direction_color hrel hirr
  let w : Real.Angle → ℝ := fun x => paritySign (f x)
  let c (a : Fin n) : ℤ := paritySign
    (f ((d.tile.move (d.place a)).positiveEdgeDirection o u 0))
  let ε : ℤ := paritySign (f (T.positiveEdgeDirection o u 0))
  have hodd (x : Real.Angle) : w (x + (Real.pi : Real.Angle)) = -w x := by
    simp only [w, hf, paritySign_add_one, Int.cast_neg]
  have hc (a : Fin n) (j : Fin 3) :
      w ((d.tile.move (d.place a)).positiveEdgeDirection o u j) = (c a : ℝ) := by
    dsimp only [w, c]
    congr 2
    apply Triangle.positive_edge_color _ o hu f hf
    intro x k
    simpa only [Triangle.angle_move] using ht x k
  have hpat := d.tile.caseSeven_outer_color_pattern T o hu f hf ht h1 h2
  have houter : (∑ j : Fin 3, T.side j * w (T.positiveEdgeDirection o u j)) =
      (ε : ℝ) * (T.side 0 - T.side 1 + T.side 2) := by
    simp only [Fin.sum_univ_three, w, hpat.1, hpat.2, paritySign_add_one, Int.cast_neg, ε]
    ring
  have he := d.oriented_edge_length_cancellation o hu w hodd
  simp_rw [hc, ← Finset.sum_mul] at he
  rw [← Finset.mul_sum, houter] at he
  have heq : ((∑ a, c a : ℤ) : ℝ) *
      (d.tile.side 0 + d.tile.side 1 + d.tile.side 2) =
        (ε : ℝ) * (T.side 0 - T.side 1 + T.side 2) := by
    simpa only [Int.cast_sum, Fin.sum_univ_three, mul_comm] using he
  have hε : (ε : ℝ) ^ 2 = 1 := by
    rcases paritySign_unit (f (T.positiveEdgeDirection o u 0)) with h | h <;>
      simp only [ε, h, Int.cast_one, Int.cast_neg] <;> norm_num
  let M : ℤ := ε * ∑ a, c a
  have hM : (M : ℝ) * (d.tile.side 0 + d.tile.side 1 + d.tile.side 2) =
      T.side 0 - T.side 1 + T.side 2 := by
    calc
      _ = (ε : ℝ) * (((∑ a, c a : ℤ) : ℝ) *
          (d.tile.side 0 + d.tile.side 1 + d.tile.side 2)) := by
        dsimp only [M]
        rw [Int.cast_mul, mul_assoc]
      _ = (ε : ℝ) * ((ε : ℝ) * (T.side 0 - T.side 1 + T.side 2)) := by rw [heq]
      _ = _ := by rw [← mul_assoc, ← pow_two, hε, one_mul]
  have hp : 0 < T.side 0 - T.side 1 + T.side 2 := by
    have h : T.side 1 < T.side 2 + T.side 0 := T.side_lt_add_sides 1
    linarith
  have hMpos : (0 : ℝ) < M := pos_of_mul_pos_left (hM.symm ▸ hp)
    (by linarith [d.tile.side_pos 0, d.tile.side_pos 1, d.tile.side_pos 2] :
      0 ≤ d.tile.side 0 + d.tile.side 1 + d.tile.side 2)
  exact ⟨M, by exact_mod_cast hMpos, hM⟩

end Erdos633b.Tiling
