import ErdosProblems.Erdos633b.GroupTwoNormalization
import ErdosProblems.Erdos633b.CaseOne

/-! All geometric and rational-normalization work for case (4), with the exact count.
The remaining nonsquare assertion for the integral count is not assumed here. -/

namespace Erdos633b

theorem group_two_rational_swap (A B : ℝ) (hA : 0 < A) (hAπ : A < Real.pi)
    (hB : 0 < B) (hBπ : B < Real.pi) (hsum : A + B = 2 * Real.pi / 3)
    (hrat : IsRational (Real.sqrt 3 * Real.tan (A / 2))) :
    IsRational (Real.sqrt 3 * Real.tan (B / 2)) := by
  obtain ⟨⟨q, hq⟩, ⟨p, hp⟩⟩ := (groupTwo_rationality_iff A hA hAπ).mp hrat
  have hBval : B = 2 * Real.pi / 3 - A := by linarith
  have hc3 : Real.cos (2 * Real.pi / 3) = -(1 / 2) := by
    rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring,
      Real.cos_pi_sub, Real.cos_pi_div_three]
  have hs3 : Real.sin (2 * Real.pi / 3) = Real.sqrt 3 / 2 := by
    rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring,
      Real.sin_pi_sub, Real.sin_pi_div_three]
  apply (groupTwo_rationality_iff B hB hBπ).mpr
  constructor
  · refine ⟨(3 * p + q) / 2, ?_⟩
    push_cast
    rw [hp, hq, hBval, Real.sin_sub, hs3, hc3]
    linear_combination -(Real.cos A / 2) * Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  · refine ⟨(-p + q) / 2, ?_⟩
    push_cast
    rw [hp, hq, hBval, Real.cos_sub, hs3, hc3]
    ring

theorem case_four_acute_geometric_counts (T : Triangle) (h0 : T.angle 0 = Real.pi / 3)
    (h1 : T.angle 1 < Real.pi / 3)
    (hrat : IsRational (Real.sqrt 3 * Real.tan (T.angle 1 / 2))) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ c ^ 2 = a ^ 2 + a * b + b ^ 2 ∧
      Nonempty (Tiling T (Sixty.commonScale a b ^ 2 * b * (a + b))) := by
  have hd : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have he : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  obtain ⟨a, b, c, ha, hb, hc, hrel, hα⟩ :=
    Sixty.integral_reference_of_rational_parameter (Real.sqrt 3) hd he
      (T.angle 1) (T.angle_pos 1) h1 hrat
  let U := Sixty.caseFourOuter (Real.sqrt 3) hd a b ha hb
  have hu0 : U.angle 0 = Real.pi / 3 := Sixty.corner_angle_zero _ hd he _ _ _ _
  have hu1 : U.angle 1 = T.angle 1 := by
    exact (Sixty.corner_angle_one _ hd a b (Sixty.commonScale a b * b : ℕ)
      (by exact_mod_cast ha) (by exact_mod_cast hb)
      (by exact_mod_cast mul_pos (Sixty.commonScale_pos a b) hb)).trans hα
  have hu2 : U.angle 2 = T.angle 2 := by linarith [U.angle_sum, T.angle_sum]
  have hangs : ∀ i, U.angle i = T.angle i := by
    intro i
    fin_cases i
    · exact hu0.trans h0.symm
    · exact hu1
    · exact hu2
  exact ⟨a, b, c, ha, hb, hc, hrel,
    ⟨(Sixty.case_four_integer_tiling _ hd he a b c ha hb hc hrel).transportAngles hangs⟩⟩

theorem case_four_geometric_counts (T : Triangle) (hC : T.angle 2 = Real.pi / 3)
    (hrat : IsRational (Real.sqrt 3 * Real.tan (T.angle 0 / 2))) :
    HasNonsquareTiling T ∨
      ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ c ^ 2 = a ^ 2 + a * b + b ^ 2 ∧
        Nonempty (Tiling T (Sixty.commonScale a b ^ 2 * b * (a + b))) := by
  by_cases heq : T.angle 0 = T.angle 1
  · exact Or.inl (case_one_sufficient T heq)
  right
  have transport (e : Equiv.Perm (Fin 3))
      (h0 : Triangle.angle (T.reindex e) 0 = Real.pi / 3)
      (h1 : Triangle.angle (T.reindex e) 1 < Real.pi / 3)
      (hr : IsRational (Real.sqrt 3 * Real.tan (Triangle.angle (T.reindex e) 1 / 2))) :
      ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ c ^ 2 = a ^ 2 + a * b + b ^ 2 ∧
        Nonempty (Tiling T (Sixty.commonScale a b ^ 2 * b * (a + b))) := by
    obtain ⟨a, b, c, ha, hb, hc, hrel, ⟨d⟩⟩ :=
      case_four_acute_geometric_counts (T.reindex e) h0 h1 hr
    refine ⟨a, b, c, ha, hb, hc, hrel, ⟨?_⟩⟩
    exact { tile := d.tile
            place := d.place
            covers := d.covers.trans (T.support_reindex e)
            disjoint_interiors := d.disjoint_interiors }
  by_cases hlt : T.angle 0 < T.angle 1
  · let e : Equiv.Perm (Fin 3) := (Equiv.swap 0 2).trans (Equiv.swap 1 2)
    have hzero : Triangle.angle (T.reindex e) 0 = T.angle 2 := by
      rw [Triangle.angle_reindex]
      congr 1
    have hone : Triangle.angle (T.reindex e) 1 = T.angle 0 := by
      rw [Triangle.angle_reindex]
      congr 1
    exact transport e (hzero.trans hC) (by rw [hone]; linarith [T.angle_sum])
      (by rw [hone]; exact hrat)
  · have hrev : T.angle 1 < T.angle 0 := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm heq)
    have hrat1 := group_two_rational_swap (T.angle 0) (T.angle 1)
      (T.angle_pos 0) (T.angle_lt_pi 0) (T.angle_pos 1) (T.angle_lt_pi 1)
      (by linarith [T.angle_sum]) hrat
    let e : Equiv.Perm (Fin 3) := Equiv.swap 0 2
    have hzero : Triangle.angle (T.reindex e) 0 = T.angle 2 := by
      rw [Triangle.angle_reindex]
      congr 1
    have hone : Triangle.angle (T.reindex e) 1 = T.angle 1 := by
      rw [Triangle.angle_reindex]
      congr 1
    exact transport e (hzero.trans hC) (by rw [hone]; linarith [T.angle_sum])
      (by rw [hone]; exact hrat1)

end Erdos633b
