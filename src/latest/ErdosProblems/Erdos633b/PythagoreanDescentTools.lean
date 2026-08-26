import ErdosProblems.Erdos633b.EulerTools
import Mathlib.NumberTheory.PythagoreanTriples

/-! Integer certificates for the doubled-leg Pythagorean descent. -/

namespace Erdos633b.PythagoreanDescent

theorem positive_square_root (a : ℤ) (ha : 0 < a) (hs : IsSquare a) :
    ∃ k : ℤ, 0 < k ∧ a = k ^ 2 := by
  obtain ⟨k, hk⟩ := hs
  have hk0 : k ≠ 0 := by intro hh; simp [hh] at hk; omega
  refine ⟨|k|, abs_pos.mpr hk0, ?_⟩
  simpa [sq_abs, sq] using hk

theorem square_mod_four (a : ℤ) : a ^ 2 % 4 = (a % 2) ^ 2 := by
  have hr : a % 4 = 0 ∨ a % 4 = 1 ∨ a % 4 = 2 ∨ a % 4 = 3 := by omega
  rcases hr with h | h | h | h
  all_goals have h2 : a % 2 = (a % 4) % 2 := by omega
  all_goals rw [sq, Int.mul_emod, h2, h]; norm_num

theorem odd_of_dvd_odd (a b : ℤ) (hb : b % 2 = 1) (hd : a ∣ b) : a % 2 = 1 := by
  rcases Int.emod_two_eq_zero_or_one a with ha | ha
  · have hh : (2 : ℤ) ∣ b := (Int.dvd_of_emod_eq_zero ha).trans hd
    have hh' : b % 2 = 0 := Int.emod_eq_zero_of_dvd hh
    omega
  · exact ha

/-- Factor a positive product equality using a reduced fraction, with the needed coprimalities. -/
theorem four_factors (u v x y : ℤ) (hu : 0 < u) (hv : 0 < v)
    (hx : 0 < x) (_hy : 0 < y) (hc : IsCoprime u v) (he : u * v = x * y) :
    ∃ α β γ δ : ℤ, 0 < α ∧ 0 < β ∧ 0 < γ ∧ 0 < δ ∧
      u = α * β ∧ v = γ * δ ∧ x = α * γ ∧ y = β * δ ∧
      IsCoprime α δ ∧ IsCoprime β γ := by
  obtain ⟨β, γ, hγ, hβγ, hβu, _, hcross⟩ :=
    EulerDescent.reduced_ratio u x (ne_of_gt hx)
  have hβ : 0 < β := pos_of_mul_pos_left (hcross ▸ mul_pos hu hγ) (le_of_lt hx)
  obtain ⟨α, hu'⟩ := hβu
  have hα : 0 < α := pos_of_mul_pos_right (hu' ▸ hu) (le_of_lt hβ)
  have huE : u = α * β := by linarith [hu']
  have hxE : x = α * γ := by
    apply mul_left_cancel₀ (ne_of_gt hβ)
    linear_combination -hcross + γ * hu'
  have hcross' : β * v = γ * y := by
    apply mul_left_cancel₀ (ne_of_gt hα)
    linear_combination he - v * huE + y * hxE
  have hγv : γ ∣ v := hβγ.symm.dvd_of_dvd_mul_left
    (hcross'.symm ▸ dvd_mul_right γ y)
  obtain ⟨δ, hvE⟩ := hγv
  have hδ : 0 < δ := pos_of_mul_pos_right (hvE ▸ hv) (le_of_lt hγ)
  have hyE : y = β * δ := by
    apply mul_left_cancel₀ (ne_of_gt hγ)
    linear_combination -hcross' + β * hvE
  have hαδ : IsCoprime α δ := hc.of_isCoprime_of_dvd_left ⟨β, huE⟩
    |>.of_isCoprime_of_dvd_right ⟨γ, by simpa [mul_comm] using hvE⟩
  exact ⟨α, β, γ, δ, hα, hβ, hγ, hδ, huE, hvE, hxE, hyE, hαδ, hβγ⟩

theorem sum_squares_coprime_three (a b : ℤ) (hc : IsCoprime a b) :
    IsCoprime (a ^ 2 + b ^ 2) 3 := by
  apply (EulerDescent.coprime_three_iff _).mpr
  intro hd
  have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mpr hd
  have hf : ∀ x y : ZMod 3, x ^ 2 + y ^ 2 = 0 → x = 0 ∧ y = 0 := by decide
  obtain ⟨ha, hb⟩ := hf a b (by simpa using hz)
  have ha' := (ZMod.intCast_zmod_eq_zero_iff_dvd a 3).mp ha
  have hb' := (ZMod.intCast_zmod_eq_zero_iff_dvd b 3).mp hb
  have hunit : IsUnit (3 : ℤ) := hc.isUnit_of_dvd' ha' hb'
  norm_num [Int.isUnit_iff] at hunit

theorem two_sums_coprime (a b : ℤ) (hc : IsCoprime a b) :
    IsCoprime (a ^ 2 + b ^ 2) (a ^ 2 + 4 * b ^ 2) := by
  let X := a ^ 2 + b ^ 2
  let Y := a ^ 2 + 4 * b ^ 2
  have hXb : IsCoprime X b := by
    simpa only [X, sq] using (hc.pow_left (m := 2)).add_mul_left_left b
  have hX3 : IsCoprime X 3 := sum_squares_coprime_three a b hc
  apply Int.isCoprime_iff_gcd_eq_one.mpr
  let g : ℤ := Int.gcd X Y
  have hgX : g ∣ X := Int.gcd_dvd_left X Y
  have hgY : g ∣ Y := Int.gcd_dvd_right X Y
  have hg3b : g ∣ 3 * b ^ 2 := by
    rw [show 3 * b ^ 2 = Y - X by dsimp [X, Y]; ring]
    exact dvd_sub hgY hgX
  have hunit : IsUnit g := (hX3.mul_right (hXb.pow_right (n := 2))).isUnit_of_dvd' hgX hg3b
  simpa [g] using Int.isUnit_iff_natAbs_eq.mp hunit

theorem parameters (a b : ℤ) (ha : a % 4 = 3) (hb : 0 < b)
    (hc : IsCoprime a b) (hs : IsSquare (a ^ 2 + b ^ 2)) :
    ∃ m n : ℤ, 0 < m ∧ 0 < n ∧ IsCoprime m n ∧ m % 2 = 0 ∧ n % 2 = 1 ∧
      a = m ^ 2 - n ^ 2 ∧ b = 2 * m * n := by
  obtain ⟨c, hcpos, he⟩ := positive_square_root _ (by nlinarith [sq_nonneg a]) hs
  have ht : PythagoreanTriple a b c := by simpa [PythagoreanTriple, sq] using he
  obtain ⟨m, n, heA, heB, _, hmn, hpar, hm⟩ :=
    ht.coprime_classification' (Int.isCoprime_iff_gcd_eq_one.mp hc) (by omega) hcpos
  have hmpos : 0 < m := by
    by_contra hh
    have hm0 : m = 0 := by omega
    simp [hm0] at heB
    omega
  have hnpos : 0 < n := pos_of_mul_pos_right (heB ▸ hb) (by positivity)
  have hpar' : m % 2 = 0 ∧ n % 2 = 1 := by
    rcases hpar with hh | ⟨hm', hn'⟩
    · exact hh
    · have hh := congrArg (fun z : ℤ => z % 4) heA
      rw [ha, Int.sub_emod, square_mod_four, square_mod_four, hm', hn'] at hh
      norm_num at hh
  exact ⟨m, n, hmpos, hnpos, Int.isCoprime_iff_gcd_eq_one.mpr hmn,
    hpar'.1, hpar'.2, heA, heB⟩

end Erdos633b.PythagoreanDescent
