import ErdosProblems.Erdos633b.ThreePieceCoordinates

/-! Sufficiency of the 30-60-90 case, by an actual three-piece congruent dissection. -/

namespace Erdos633b

namespace ThreePiece

def cycle : Equiv.Perm (Fin 3) := (Equiv.swap 0 1).trans (Equiv.swap 1 2)

theorem cycle_symm (i : Fin 3) : cycle.symm i = i + 1 := by fin_cases i <;> decide

noncomputable def one_patch (d : ℝ) (hd : 0 < d) (he : d ^ 2 = 3) (T : Triangle)
    (hs : ∀ i, T.side i ^ 2 = ![3, 1, 4] i) : Patch (reference d hd) T.support 1 := by
  let V : Triangle := T.reindex cycle
  have hv (i : Fin 3) : V.side i ^ 2 = ![1, 4, 3] i := by
    rw [Triangle.side_reindex, cycle_symm, hs]
    fin_cases i <;> rfl
  have hside (i : Fin 3) : V.side i = (1 : ℕ) * (reference d hd).side i := by
    have h1 := reference_side_sq d hd he i
    have h2 := hv i
    have hp1 := (reference d hd).side_pos i
    have hp2 := V.side_pos i
    norm_num only [Nat.cast_one, one_mul]
    nlinarith
  have result := quadratic_patch_congruent (reference d hd) V 1 (by decide) hside
  change Patch (reference d hd) (Triangle.support (T.reindex cycle)) 1 at result
  rwa [Triangle.support_reindex] at result

noncomputable def three_piece_tiling (d : ℝ) (hd : 0 < d) (he : d ^ 2 = 3) :
    Tiling (outer d hd) 3 := by
  have pF := one_patch d hd he (remaining d hd).firstHalf (first_side_sq d hd he)
  have pG := one_patch d hd he (remaining d hd).secondHalf (second_side_sq d hd he)
  have pS := pF.glueTwo pG (remaining d hd).halves_disjoint_interiors
  rw [Triangle.halves_cover] at pS
  have pR := (Tiling.single (reference d hd)).toPatch
  change Patch (reference d hd) (reference d hd).support 1 at pR
  exact edge_patch_assemble (outer d hd) (reference d hd) (1 / 3)
    (by norm_num) (by norm_num) 1 2 pR pS

theorem outer_angle_zero (d : ℝ) (hd : 0 < d) : (outer d hd).angle 0 = Real.pi / 2 := by
  change InnerProductGeometry.angle ((!₂[3, 0] : Plane) - 0) ((!₂[0, d] : Plane) - 0) = _
  apply (InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two _ _).mp
  simp [PiLp.inner_apply, Fin.sum_univ_two]

theorem outer_angles (d : ℝ) (hd : 0 < d) (he : d ^ 2 = 3) :
    (outer d hd).angle 0 = Real.pi / 2 ∧ (outer d hd).angle 1 = Real.pi / 6 ∧
      (outer d hd).angle 2 = Real.pi / 3 := by
  let U := outer d hd
  have h0 : U.angle 0 = Real.pi / 2 := outer_angle_zero d hd
  have hs0 : U.side 0 ^ 2 = 12 := outer_side_sq d hd he 0
  have hs1 : U.side 1 ^ 2 = 3 := outer_side_sq d hd he 1
  have hratio : U.side 0 = 2 * U.side 1 := by
    nlinarith [U.side_pos 0, U.side_pos 1]
  have hs := U.sine_law 1 0
  rw [hratio, h0, Real.sin_pi_div_two, one_mul] at hs
  have hsin : Real.sin (U.angle 1) = 1 / 2 := by nlinarith [U.side_pos 1]
  have hacute : U.angle 1 < Real.pi / 2 := by linarith [U.angle_sum, U.angle_pos 2]
  have h1 : U.angle 1 = Real.pi / 6 := Real.injOn_sin
    ⟨by linarith [U.angle_pos 1, Real.pi_pos], hacute.le⟩
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
    (hsin.trans Real.sin_pi_div_six.symm)
  exact ⟨h0, h1, by linarith [U.angle_sum]⟩

end ThreePiece

theorem case_three_sufficient (T : Triangle) (hA : T.angle 0 = Real.pi / 6)
    (hB : T.angle 1 = Real.pi / 2) (hC : T.angle 2 = Real.pi / 3) : HasNonsquareTiling T := by
  have hd : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have he : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  let U := ThreePiece.outer (Real.sqrt 3) hd
  let e : Equiv.Perm (Fin 3) := Equiv.swap 0 1
  have hang := ThreePiece.outer_angles (Real.sqrt 3) hd he
  have hi : ∀ i, Triangle.angle (U.reindex e) i = T.angle i := by
    intro i
    rw [Triangle.angle_reindex]
    fin_cases i
    · change U.angle 1 = T.angle 0
      exact hang.2.1.trans hA.symm
    · change U.angle 0 = T.angle 1
      exact hang.1.trans hB.symm
    · have hindex : e.symm (2 : Fin 3) = 2 := by decide
      change U.angle (e.symm 2) = T.angle 2
      rw [hindex]
      exact hang.2.2.trans hC.symm
  have hn : ¬ IsSquare (3 : ℕ) := by
    rintro ⟨k, hk⟩
    by_cases h : k ≤ 1
    · rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl <;> norm_num at hk
    · have hk2 : 2 ≤ k := by omega
      nlinarith
  have result := (ThreePiece.three_piece_tiling (Real.sqrt 3) hd he).reindexOuter e
  exact ⟨3, hn, ⟨result.transportAngles hi⟩⟩

theorem case_three_sufficient_reindexed (T : Triangle) (e : Equiv.Perm (Fin 3))
    (hA : T.angle (e 0) = Real.pi / 6) (hB : T.angle (e 1) = Real.pi / 2)
    (hC : T.angle (e 2) = Real.pi / 3) : HasNonsquareTiling T := by
  have result := case_three_sufficient (T.reindex e.symm)
    (by simpa only [Triangle.angle_reindex, Equiv.symm_symm] using hA)
    (by simpa only [Triangle.angle_reindex, Equiv.symm_symm] using hB)
    (by simpa only [Triangle.angle_reindex, Equiv.symm_symm] using hC)
  exact hasNonsquareTiling_of_support_eq (T.support_reindex e.symm) result

end Erdos633b
