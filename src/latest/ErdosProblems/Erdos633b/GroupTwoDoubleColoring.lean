import ErdosProblems.Erdos633b.ColorTurnShifts
import ErdosProblems.Erdos633b.GroupOneSignedPerimeter
import ErdosProblems.Erdos633b.LocalAngleTypes
import ErdosProblems.Erdos633b.ReptilingOrdering

/-! Two positive integer perimeter equations for the doubled group-2 shape.
The second is obtained by reindexing the actual tile and outer triangle. -/

namespace Erdos633b.Tiling

local instance : Fact (Module.finrank ℝ Plane = 2) := ⟨by simp [Plane]⟩

theorem groupTwoDouble_coloring_equation {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hg : d.tile.angle 2 = 2 * Real.pi / 3)
    (hirr : Irrational (d.tile.angle 0 / Real.pi))
    (h1 : T.angle 1 = 2 * d.tile.angle 1)
    (h2 : T.angle 2 = d.tile.angle 0 + d.tile.angle 1) :
    ∃ M : ℤ, 0 < M ∧ (M : ℝ) * (d.tile.side 0 - d.tile.side 1 + d.tile.side 2) =
      T.side 0 + T.side 1 - T.side 2 := by
  let o : Orientation ℝ Plane (Fin 2) := (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.orientation
  let u : Plane := d.tile.points 1 - d.tile.points 0
  have hu : u ≠ 0 := sub_ne_zero.mpr (d.tile.independent.injective.ne (by decide))
  obtain ⟨f, hf, ha, hb, hc⟩ := d.tile.exists_groupTwo_direction_parity hg hirr
  let w : Real.Angle → ℝ := fun x => paritySign (f x)
  let c (a : Fin n) : ℤ := paritySign
    (f ((d.tile.move (d.place a)).positiveEdgeDirection o u 0))
  let ε : ℤ := paritySign (f (T.positiveEdgeDirection o u 0))
  have hodd (x : Real.Angle) : w (x + (Real.pi : Real.Angle)) = -w x := by
    simp only [w, hf, paritySign_add_one, Int.cast_neg]
  have hInner (a : Fin n) : (∑ j : Fin 3, d.tile.side j *
      w ((d.tile.move (d.place a)).positiveEdgeDirection o u j)) =
        (c a : ℝ) * (d.tile.side 0 - d.tile.side 1 + d.tile.side 2) := by
    have hpat := (d.tile.move (d.place a)).positive_color_pattern_odd_even o hu f hf
      (fun x => by simpa only [Triangle.angle_move] using hb x)
      (fun x => by simpa only [Triangle.angle_move] using hc x)
    simp only [Fin.sum_univ_three, w, hpat.1, hpat.2, paritySign_add_one, Int.cast_neg, c]
    ring
  have hO1 (x : Real.Angle) : f (x + (T.angle 1 : Real.Angle)) = f x := by
    rw [h1, show 2 * d.tile.angle 1 = d.tile.angle 1 + d.tile.angle 1 by ring,
      Real.Angle.coe_add, ← add_assoc, hb, hb, add_assoc,
      show (1 : ZMod 2) + 1 = 0 from by decide, add_zero]
  have hO2 (x : Real.Angle) : f (x + (T.angle 2 : Real.Angle)) = f x + 1 := by
    rw [h2, Real.Angle.coe_add, ← add_assoc, hb, ha]
  have hpat := T.positive_color_pattern_even_odd o hu f hf hO1 hO2
  have hOuter : (∑ j : Fin 3, T.side j * w (T.positiveEdgeDirection o u j)) =
      (ε : ℝ) * (T.side 0 + T.side 1 - T.side 2) := by
    simp only [Fin.sum_univ_three, w, hpat.1, hpat.2, paritySign_add_one, Int.cast_neg, ε]
    ring
  have he := d.oriented_edge_length_cancellation o hu w hodd
  simp_rw [hInner] at he
  rw [← Finset.sum_mul, hOuter] at he
  have heq : ((∑ a, c a : ℤ) : ℝ) * (d.tile.side 0 - d.tile.side 1 + d.tile.side 2) =
      (ε : ℝ) * (T.side 0 + T.side 1 - T.side 2) := by
    simpa only [Int.cast_sum] using he
  have hε : (ε : ℝ) ^ 2 = 1 := by
    rcases paritySign_unit (f (T.positiveEdgeDirection o u 0)) with h | h <;>
      simp only [ε, h, Int.cast_one, Int.cast_neg] <;> norm_num
  let M : ℤ := ε * ∑ a, c a
  have hM : (M : ℝ) * (d.tile.side 0 - d.tile.side 1 + d.tile.side 2) =
      T.side 0 + T.side 1 - T.side 2 := by
    calc
      _ = (ε : ℝ) * (((∑ a, c a : ℤ) : ℝ) *
          (d.tile.side 0 - d.tile.side 1 + d.tile.side 2)) := by
        dsimp only [M]
        rw [Int.cast_mul, mul_assoc]
      _ = (ε : ℝ) * ((ε : ℝ) * (T.side 0 + T.side 1 - T.side 2)) := by rw [heq]
      _ = _ := by rw [← mul_assoc, ← pow_two, hε, one_mul]
  have hp : 0 < T.side 0 + T.side 1 - T.side 2 := by
    have h : T.side 2 < T.side 0 + T.side 1 := T.side_lt_add_sides 2
    linarith
  have htile : 0 ≤ d.tile.side 0 - d.tile.side 1 + d.tile.side 2 := by
    have h : d.tile.side 1 < d.tile.side 2 + d.tile.side 0 := d.tile.side_lt_add_sides 1
    linarith
  have hMpos : (0 : ℝ) < M := pos_of_mul_pos_left (hM.symm ▸ hp) htile
  exact ⟨M, by exact_mod_cast hMpos, hM⟩

theorem groupTwoDouble_twin_equations {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hg : d.tile.angle 2 = 2 * Real.pi / 3)
    (hirr : ¬ ∀ i, IsRational (T.angle i / Real.pi))
    (h0 : T.angle 0 = 2 * d.tile.angle 0) (h1 : T.angle 1 = 2 * d.tile.angle 1)
    (h2 : T.angle 2 = d.tile.angle 0 + d.tile.angle 1) :
    ∃ M L : ℤ, 0 < M ∧ 0 < L ∧
      (M : ℝ) * (d.tile.side 0 - d.tile.side 1 + d.tile.side 2) =
        T.side 0 + T.side 1 - T.side 2 ∧
      (L : ℝ) * (-d.tile.side 0 + d.tile.side 1 + d.tile.side 2) =
        T.side 0 + T.side 1 - T.side 2 := by
  obtain ⟨M, hM, heM⟩ := d.groupTwoDouble_coloring_equation hg
    (d.groupTwo_first_angle_irrational hg hirr) h1 h2
  let e : Equiv.Perm (Fin 3) := Equiv.swap 0 1
  let U : Triangle := T.reindex e
  let d' : Tiling U n := (d.reindexTile e).reindexOuter e
  have hirrU : ¬ ∀ i, IsRational (U.angle i / Real.pi) := by
    intro h
    apply hirr
    intro i
    simpa only [U, Triangle.angle_reindex, Equiv.symm_apply_apply] using h (e i)
  have hg' : d'.tile.angle 2 = 2 * Real.pi / 3 := by
    change Triangle.angle (d.tile.reindex e) 2 = _
    rw [Triangle.angle_reindex]
    exact hg
  have h1' : U.angle 1 = 2 * d'.tile.angle 1 := by
    change Triangle.angle (T.reindex e) 1 = 2 * Triangle.angle (d.tile.reindex e) 1
    rw [Triangle.angle_reindex, Triangle.angle_reindex]
    exact h0
  have h2' : U.angle 2 = d'.tile.angle 0 + d'.tile.angle 1 := by
    change Triangle.angle (T.reindex e) 2 =
      Triangle.angle (d.tile.reindex e) 0 + Triangle.angle (d.tile.reindex e) 1
    rw [Triangle.angle_reindex, Triangle.angle_reindex, Triangle.angle_reindex]
    change T.angle 2 = d.tile.angle 1 + d.tile.angle 0
    rw [h2, add_comm]
  obtain ⟨L, hL, heL⟩ := d'.groupTwoDouble_coloring_equation hg'
    (d'.groupTwo_first_angle_irrational hg' hirrU) h1' h2'
  change (L : ℝ) * (Triangle.side (d.tile.reindex e) 0 -
    Triangle.side (d.tile.reindex e) 1 + Triangle.side (d.tile.reindex e) 2) =
      Triangle.side (T.reindex e) 0 + Triangle.side (T.reindex e) 1 -
        Triangle.side (T.reindex e) 2 at heL
  simp only [Triangle.side_reindex] at heL
  change (L : ℝ) * (d.tile.side 1 - d.tile.side 0 + d.tile.side 2) =
    T.side 1 + T.side 0 - T.side 2 at heL
  refine ⟨M, L, hM, hL, heM, ?_⟩
  linear_combination heL

end Erdos633b.Tiling
