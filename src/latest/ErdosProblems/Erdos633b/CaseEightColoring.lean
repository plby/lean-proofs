import ErdosProblems.Erdos633b.ParityPerimeter
import ErdosProblems.Erdos633b.LocalAngleTypes
import ErdosProblems.Erdos633b.ReptilingOrdering

/-! The two complementary integer perimeter equations for case (8). -/

namespace Erdos633b.Tiling

theorem caseEight_twin_equations {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hg : d.tile.angle 2 = 2 * Real.pi / 3)
    (hirr : ¬ ∀ i, IsRational (T.angle i / Real.pi))
    (h1 : T.angle 1 = 2 * d.tile.angle 1)
    (h2 : T.angle 2 = 2 * d.tile.angle 0 + d.tile.angle 1) :
    ∃ M L : ℤ, 0 < M ∧ 0 < L ∧
      (M : ℝ) * (d.tile.side 0 - d.tile.side 1 + d.tile.side 2) =
        T.side 0 + T.side 1 - T.side 2 ∧
      (L : ℝ) * (-d.tile.side 0 + d.tile.side 1 + d.tile.side 2) =
        -T.side 0 + T.side 1 + T.side 2 := by
  obtain ⟨f, hp, ha, hb, hc⟩ := d.tile.exists_groupTwo_direction_parity hg
    (d.groupTwo_first_angle_irrational hg hirr)
  have hO1 (x : Real.Angle) : f (x + (T.angle 1 : Real.Angle)) = f x + 0 := by
    rw [h1, show 2 * d.tile.angle 1 = d.tile.angle 1 + d.tile.angle 1 by ring,
      Real.Angle.coe_add, ← add_assoc, hb, hb, add_assoc,
      show (1 : ZMod 2) + 1 = 0 from by decide]
  have hO2 (x : Real.Angle) : f (x + (T.angle 2 : Real.Angle)) = f x + 1 := by
    rw [h2, show 2 * d.tile.angle 0 + d.tile.angle 1 =
      d.tile.angle 0 + d.tile.angle 0 + d.tile.angle 1 by ring,
      Real.Angle.coe_add, Real.Angle.coe_add, ← add_assoc, ← add_assoc, hb, ha, ha]
  obtain ⟨M, heM⟩ := d.groupTwo_parity_perimeter f hp hb hc 0 1 hO1 hO2
  simp only [show (1 : ZMod 2) + 1 = 0 from by decide, zero_add] at heM
  norm_num [paritySign] at heM
  have hM : (M : ℝ) * (d.tile.side 0 - d.tile.side 1 + d.tile.side 2) =
      T.side 0 + T.side 1 - T.side 2 := by linear_combination heM
  have hMp : 0 < M := by
    have htile : 0 ≤ d.tile.side 0 - d.tile.side 1 + d.tile.side 2 := by
      have h : d.tile.side 1 < d.tile.side 2 + d.tile.side 0 := d.tile.side_lt_add_sides 1
      linarith
    have hout : 0 < T.side 0 + T.side 1 - T.side 2 := by
      have h : T.side 2 < T.side 0 + T.side 1 := T.side_lt_add_sides 2
      linarith
    exact_mod_cast pos_of_mul_pos_left (hM.symm ▸ hout) htile
  let e : Equiv.Perm (Fin 3) := Equiv.swap 0 1
  let d' := d.reindexTile e
  have hg' : d'.tile.angle 2 = 2 * Real.pi / 3 := by
    change Triangle.angle (d.tile.reindex e) 2 = _
    rw [Triangle.angle_reindex]
    exact hg
  have hα : d.tile.angle 0 = d'.tile.angle 1 := by
    change d.tile.angle 0 = Triangle.angle (d.tile.reindex e) 1
    rw [Triangle.angle_reindex]
    rfl
  have hβ : d.tile.angle 1 = d'.tile.angle 0 := by
    change d.tile.angle 1 = Triangle.angle (d.tile.reindex e) 0
    rw [Triangle.angle_reindex]
    rfl
  obtain ⟨g, gp, ga, gb, gc⟩ := d'.tile.exists_groupTwo_direction_parity hg'
    (d'.groupTwo_first_angle_irrational hg' hirr)
  have hG1 (x : Real.Angle) : g (x + (T.angle 1 : Real.Angle)) = g x + 0 := by
    rw [h1, hβ, show 2 * d'.tile.angle 0 = d'.tile.angle 0 + d'.tile.angle 0 by ring,
      Real.Angle.coe_add, ← add_assoc, ga, ga, add_zero]
  have hG2 (x : Real.Angle) : g (x + (T.angle 2 : Real.Angle)) = g x + 0 := by
    rw [h2, hα, hβ, show 2 * d'.tile.angle 1 + d'.tile.angle 0 =
      d'.tile.angle 1 + d'.tile.angle 1 + d'.tile.angle 0 by ring,
      Real.Angle.coe_add, Real.Angle.coe_add, ← add_assoc, ← add_assoc, ga, gb, gb,
      add_assoc, show (1 : ZMod 2) + 1 = 0 from by decide]
  obtain ⟨N, heN⟩ := d'.groupTwo_parity_perimeter g gp gb gc 0 0 hG1 hG2
  norm_num [paritySign] at heN
  change (N : ℝ) * (Triangle.side (d.tile.reindex e) 0 -
    Triangle.side (d.tile.reindex e) 1 + Triangle.side (d.tile.reindex e) 2) = _ at heN
  simp only [Triangle.side_reindex] at heN
  change (N : ℝ) * (d.tile.side 1 - d.tile.side 0 + d.tile.side 2) =
    T.side 0 + -T.side 1 + -T.side 2 at heN
  let L : ℤ := -N
  have hL : (L : ℝ) * (-d.tile.side 0 + d.tile.side 1 + d.tile.side 2) =
      -T.side 0 + T.side 1 + T.side 2 := by
    dsimp only [L]
    rw [Int.cast_neg]
    linear_combination -heN
  have hLp : 0 < L := by
    have htile : 0 ≤ -d.tile.side 0 + d.tile.side 1 + d.tile.side 2 := by
      have h : d.tile.side 0 < d.tile.side 1 + d.tile.side 2 := d.tile.side_lt_add_sides 0
      linarith
    have hout : 0 < -T.side 0 + T.side 1 + T.side 2 := by
      have h : T.side 0 < T.side 1 + T.side 2 := T.side_lt_add_sides 0
      linarith
    exact_mod_cast pos_of_mul_pos_left (hL.symm ▸ hout) htile
  exact ⟨M, L, hMp, hLp, hM, hL⟩

end Erdos633b.Tiling
