import ErdosProblems.Erdos633b.TriquadraticTriangles

/-! The exact case-(7) angles and half-angle parameter of the constructed outer triangle. -/

namespace Erdos633b.TriquadraticCoordinates

theorem norm_e : ‖(!₂[1, 0] : Plane)‖ = 1 := by
  norm_num [EuclideanSpace.norm_eq, Fin.sum_univ_two]

theorem norm_turn_e (s d : ℝ) (he : d ^ 2 = 4 - s ^ 2) :
    ‖(!₂[-s / 2, d / 2] : Plane)‖ = 1 := by
  have h : ‖(!₂[-s / 2, d / 2] : Plane)‖ ^ 2 = 1 := by
    simp [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
    nlinarith
  nlinarith [norm_nonneg (!₂[-s / 2, d / 2] : Plane)]

theorem outer_cos_zero (c s d : ℝ) (hc : 0 < c) (hs : 0 < s) (hs1 : s < 1)
    (hd : 0 < d) (he : d ^ 2 = 4 - s ^ 2) :
    Real.cos ((outer c s d hc hs hs1 hd).angle 0) = 1 - 2 * s ^ 2 + s ^ 4 / 2 := by
  have hw : ‖w s d‖ = 1 := by nlinarith [unit_w s d he, norm_nonneg (w s d)]
  have hC : bigC c s = (c ^ 2 * (1 - s ^ 2)) • (!₂[1, 0] : Plane) := by
    ext i
    fin_cases i <;> simp [bigC]
  have ht := (parameter_denominator_pos s hs hs1).1
  change Real.cos (InnerProductGeometry.angle (bigB c s d - (0 : Plane)) (bigC c s - 0)) = _
  rw [sub_zero, sub_zero, bigB, hC,
    InnerProductGeometry.angle_smul_left_of_pos _ _ (sq_pos_of_pos hc),
    InnerProductGeometry.angle_smul_right_of_pos _ _ (mul_pos (sq_pos_of_pos hc) ht),
    InnerProductGeometry.cos_angle, hw, norm_e]
  simp [PiLp.inner_apply, Fin.sum_univ_two, w]

theorem outer_cos_two (c s d : ℝ) (hc : 0 < c) (hs : 0 < s) (hs1 : s < 1)
    (hd : 0 < d) (he : d ^ 2 = 4 - s ^ 2) :
    Real.cos ((outer c s d hc hs hs1 hd).angle 2) = s / 2 := by
  have ht := parameter_denominator_pos s hs hs1
  have hCA : (0 : Plane) - bigC c s =
      (c ^ 2 * (1 - s ^ 2)) • (-(!₂[1, 0] : Plane)) := by
    ext i
    fin_cases i <;> simp [bigC]
  have hCB : bigB c s d - bigC c s =
      ((2 - s ^ 2) * c ^ 2 * s) • (!₂[-s / 2, d / 2] : Plane) := by
    ext i
    fin_cases i <;> simp [bigB, bigC, w] <;> ring
  change Real.cos (InnerProductGeometry.angle ((0 : Plane) - bigC c s) (bigB c s d - bigC c s)) = _
  rw [hCA, hCB,
    InnerProductGeometry.angle_smul_left_of_pos _ _ (mul_pos (sq_pos_of_pos hc) ht.1),
    InnerProductGeometry.angle_smul_right_of_pos _ _
      (mul_pos (mul_pos ht.2 (sq_pos_of_pos hc)) hs),
    InnerProductGeometry.cos_angle, norm_neg, norm_e, norm_turn_e s d he]
  simp [PiLp.inner_apply, Fin.sum_univ_two, neg_div]

theorem angles_from_cosines (A B C s : ℝ) (hs : 0 < s) (hs1 : s < 1)
    (hA0 : 0 < A) (hApi : A < Real.pi) (hC0 : 0 < C) (hCpi : C < Real.pi)
    (hsum : A + B + C = Real.pi)
    (hA : Real.cos A = 1 - 2 * s ^ 2 + s ^ 4 / 2) (hC : Real.cos C = s / 2) :
    C = A / 2 + B ∧ 2 * Real.sin (A / 4) = s := by
  have hClo : Real.pi / 3 < C := by
    by_contra hn
    have hh := Real.cos_le_cos_of_nonneg_of_le_pi hC0.le
      (by linarith [Real.pi_pos] : Real.pi / 3 ≤ Real.pi) (le_of_not_gt hn)
    rw [Real.cos_pi_div_three, hC] at hh
    linarith
  have hChi : C < Real.pi / 2 := by
    by_contra hn
    have hh := Real.cos_le_cos_of_nonneg_of_le_pi
      (by linarith [Real.pi_pos] : 0 ≤ Real.pi / 2) hCpi.le (le_of_not_gt hn)
    rw [hC, Real.cos_pi_div_two] at hh
    linarith
  have hcos : Real.cos (2 * Real.pi - 4 * C) = 1 - 2 * s ^ 2 + s ^ 4 / 2 := by
    rw [Real.cos_sub, Real.cos_two_pi, Real.sin_two_pi]
    simp only [one_mul, zero_mul, add_zero]
    rw [show 4 * C = 2 * (2 * C) by ring, Real.cos_two_mul, Real.cos_two_mul, hC]
    ring
  have heq : A = 2 * Real.pi - 4 * C := Real.injOn_cos ⟨hA0.le, hApi.le⟩
    ⟨by linarith, by linarith [Real.pi_pos]⟩ (hA.trans hcos.symm)
  refine ⟨by linarith, ?_⟩
  rw [heq, show (2 * Real.pi - 4 * C) / 4 = Real.pi / 2 - C by ring,
    Real.sin_pi_div_two_sub, hC]
  ring

theorem outer_angle_relations (c s d : ℝ) (hc : 0 < c) (hs : 0 < s) (hs1 : s < 1)
    (hd : 0 < d) (he : d ^ 2 = 4 - s ^ 2) :
    (outer c s d hc hs hs1 hd).angle 2 =
        (outer c s d hc hs hs1 hd).angle 0 / 2 + (outer c s d hc hs hs1 hd).angle 1 ∧
      2 * Real.sin ((outer c s d hc hs hs1 hd).angle 0 / 4) = s := by
  let T := outer c s d hc hs hs1 hd
  exact angles_from_cosines (T.angle 0) (T.angle 1) (T.angle 2) s hs hs1
    (T.angle_pos 0) (T.angle_lt_pi 0) (T.angle_pos 2) (T.angle_lt_pi 2)
    T.angle_sum (outer_cos_zero c s d hc hs hs1 hd he) (outer_cos_two c s d hc hs hs1 hd he)

end Erdos633b.TriquadraticCoordinates
