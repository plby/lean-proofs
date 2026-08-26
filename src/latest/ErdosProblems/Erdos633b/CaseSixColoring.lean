import ErdosProblems.Erdos633b.GeneralParityPerimeter

/-! Two positive integer perimeter equations for the case-(6) shape.
The alternate group-1 character distinguishes a from the other two sides. -/

namespace Erdos633b.Tiling

theorem caseSix_twin_equations {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hrel : 3 * d.tile.angle 0 + 2 * d.tile.angle 1 = Real.pi)
    (hirr : Irrational (d.tile.angle 0 / Real.pi))
    (h1 : T.angle 1 = 2 * d.tile.angle 0) (h2 : T.angle 2 = 2 * d.tile.angle 1) :
    ∃ M L : ℤ, 0 < M ∧ 0 < L ∧
      (M : ℝ) * (d.tile.side 0 + d.tile.side 1 + d.tile.side 2) =
        -T.side 0 + T.side 1 + T.side 2 ∧
      (L : ℝ) * (-d.tile.side 0 + d.tile.side 1 + d.tile.side 2) =
        -T.side 0 + T.side 1 + T.side 2 := by
  obtain ⟨f, fp, ft, _⟩ := d.tile.exists_groupOne_direction_color hrel hirr
  have hO1 (x : Real.Angle) : f (x + (T.angle 1 : Real.Angle)) = f x + 0 := by
    rw [h1, parity_double_shift f (d.tile.angle 0) 1 (fun z => ft z 0), add_zero]
  have hO2 (x : Real.Angle) : f (x + (T.angle 2 : Real.Angle)) = f x + 0 := by
    rw [h2, parity_double_shift f (d.tile.angle 1) 1 (fun z => ft z 1), add_zero]
  obtain ⟨N, heN⟩ := d.parity_perimeter f fp 1 1 0 0
    (fun x => ft x 1) (fun x => ft x 2) hO1 hO2
  simp only [show (1 : ZMod 2) + 1 = 0 from by decide, zero_add] at heN
  norm_num [paritySign] at heN
  let M : ℤ := -N
  have hM : (M : ℝ) * (d.tile.side 0 + d.tile.side 1 + d.tile.side 2) =
      -T.side 0 + T.side 1 + T.side 2 := by
    dsimp only [M]
    rw [Int.cast_neg]
    linear_combination -heN
  have hout : 0 < -T.side 0 + T.side 1 + T.side 2 := by
    have h : T.side 0 < T.side 1 + T.side 2 := T.side_lt_add_sides 0
    linarith
  have hMp : 0 < M := by
    have htile : 0 ≤ d.tile.side 0 + d.tile.side 1 + d.tile.side 2 := by
      linarith [d.tile.side_pos 0, d.tile.side_pos 1, d.tile.side_pos 2]
    exact_mod_cast pos_of_mul_pos_left (hM.symm ▸ hout) htile
  obtain ⟨g, gp, ga, gb, gc⟩ := d.tile.exists_groupOne_alternate_direction_color hrel hirr
  have hG1 (x : Real.Angle) : g (x + (T.angle 1 : Real.Angle)) = g x + 0 := by
    rw [h1, parity_double_shift g (d.tile.angle 0) 1 ga, add_zero]
  have hG2 (x : Real.Angle) : g (x + (T.angle 2 : Real.Angle)) = g x + 0 := by
    rw [h2, parity_double_shift g (d.tile.angle 1) 0
      (fun z => by simpa only [add_zero] using gb z), add_zero]
  obtain ⟨L, heL⟩ := d.parity_perimeter g gp 0 0 0 0
    (fun x => by simpa only [add_zero] using gb x)
    (fun x => by simpa only [add_zero] using gc x) hG1 hG2
  norm_num [paritySign] at heL
  have hL : (L : ℝ) * (-d.tile.side 0 + d.tile.side 1 + d.tile.side 2) =
      -T.side 0 + T.side 1 + T.side 2 := by linear_combination -heL
  have hLp : 0 < L := by
    have htile : 0 ≤ -d.tile.side 0 + d.tile.side 1 + d.tile.side 2 := by
      have h : d.tile.side 0 < d.tile.side 1 + d.tile.side 2 := d.tile.side_lt_add_sides 0
      linarith
    exact_mod_cast pos_of_mul_pos_left (hL.symm ▸ hout) htile
  exact ⟨M, L, hMp, hLp, hM, hL⟩

end Erdos633b.Tiling
