import ErdosProblems.Erdos587.WideTerminal

/-! Primitive Bézout parameters and arithmetic ranges in the critical branch. -/

namespace Erdos587

lemma first_side_lt_step_of_proper {t u v H J : ℕ} (hv : 0 < v)
    (horient : u * H ≤ v * J)
    (hproper : ∀ x₁ ≤ H, ∀ y₁ ≤ J, ∀ x₂ ≤ H, ∀ y₂ ≤ J,
      t + u * x₁ + v * y₁ = t + u * x₂ + v * y₂ → x₁ = x₂ ∧ y₁ = y₂) : H < v := by
  by_contra h
  have hvH : v ≤ H := by omega
  have huJ : u ≤ J := by
    have hh : v * u ≤ v * J := by
      calc
        _ = u * v := Nat.mul_comm _ _
        _ ≤ u * H := Nat.mul_le_mul_left u hvH
        _ ≤ v * J := horient
    exact Nat.le_of_mul_le_mul_left hh hv
  have hh := hproper v hvH 0 (Nat.zero_le J) 0 (Nat.zero_le H) u huJ (by ring)
  omega

lemma coprime_of_nat_bezout {a u b v : ℕ} (hab : a * u = b * v + 1) : b.Coprime u := by
  have hh : b.Coprime (b * v + 1) := by
    rw [Nat.coprime_mul_left_add_right]
    exact Nat.coprime_one_right b
  rw [← hab] at hh
  exact hh.of_dvd_right (dvd_mul_left u a)

lemma exists_nat_positive_bezout {u v : ℕ} (hu : 0 < u) (hv : 0 < v) (huv : u.Coprime v) :
    ∃ a b : ℕ, a * u = b * v + 1 ∧ b.Coprime u := by
  by_cases hv1 : v = 1
  · subst v
    refine ⟨1, u - 1, ?_, ?_⟩
    · omega
    · apply coprime_of_nat_bezout (a := 1) (v := 1)
      omega
  · obtain ⟨a, ha, hmod⟩ := Nat.exists_mul_mod_eq_one_of_coprime huv (by omega)
    let b := (u * a) / v
    have hab : a * u = b * v + 1 := by
      have hh := Nat.mod_add_div (u * a) v
      rw [hmod] at hh
      dsimp [b]
      nlinarith
    exact ⟨a, b, hab, coprime_of_nat_bezout hab⟩

lemma critical_parameter_ranges {t u v H J T C : ℝ}
    (ht : 0 ≤ t) (hu : 0 ≤ u) (hv : 0 ≤ v) (hH : 0 ≤ H) (hJ : 0 ≤ J)
    (hT : 0 < T) (hC : 0 < C)
    (hupper : t + u * H + v * J ≤ T) (horient : u * H ≤ v * J)
    (hspan : T ≤ C * (u * H + v * J))
    (hJlo : T ^ (1 / 4 : ℝ) ≤ J) (hJhi : J ≤ T ^ (1 / 4 + 1 / 1000 : ℝ))
    (hprod : T ^ (3 / 4 : ℝ) ≤ H * J) :
    Real.sqrt T * T ^ (-(1 / 1000 : ℝ)) ≤ H ∧
      u ≤ Real.sqrt T * T ^ (1 / 1000 : ℝ) ∧
      (1 / (2 * C)) * T ^ (3 / 4 - 1 / 1000 : ℝ) ≤ v ∧
      v ≤ T ^ (3 / 4 : ℝ) := by
  have huH : u * H ≤ T := by nlinarith
  have hvJ : v * J ≤ T := by nlinarith
  have hpowJ : 0 < T ^ (1 / 4 + 1 / 1000 : ℝ) := Real.rpow_pos_of_pos hT _
  have hHlo : T ^ (1 / 2 - 1 / 1000 : ℝ) ≤ H := by
    apply (mul_le_mul_iff_left₀ hpowJ).mp
    calc
      _ = T ^ (3 / 4 : ℝ) := by rw [← Real.rpow_add hT]; norm_num
      _ ≤ H * J := hprod
      _ ≤ _ := mul_le_mul_of_nonneg_left hJhi hH
  have huhi : u ≤ T ^ (1 / 2 + 1 / 1000 : ℝ) := by
    apply (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos hT (1 / 2 - 1 / 1000 : ℝ))).mp
    calc
      _ ≤ u * H := mul_le_mul_of_nonneg_left hHlo hu
      _ ≤ T := huH
      _ = _ := by rw [← Real.rpow_add hT]; norm_num
  have hvlo : (1 / (2 * C)) * T ^ (3 / 4 - 1 / 1000 : ℝ) ≤ v := by
    have hmass : (1 / (2 * C)) * T ≤ v * J := by
      have hh : T ≤ (v * J) * (2 * C) := by
        nlinarith [mul_le_mul_of_nonneg_left horient hC.le]
      have hh' := (div_le_iff₀ (show 0 < 2 * C by positivity)).mpr hh
      simpa only [div_eq_mul_inv, one_mul, mul_comm] using hh'
    apply (mul_le_mul_iff_left₀ hpowJ).mp
    calc
      _ = (1 / (2 * C)) * T := by rw [mul_assoc, ← Real.rpow_add hT]; norm_num
      _ ≤ v * J := hmass
      _ ≤ _ := mul_le_mul_of_nonneg_left hJhi hv
  have hvhi : v ≤ T ^ (3 / 4 : ℝ) := by
    apply (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos hT (1 / 4 : ℝ))).mp
    calc
      _ ≤ v * J := mul_le_mul_of_nonneg_left hJlo hv
      _ ≤ T := hvJ
      _ = _ := by rw [← Real.rpow_add hT]; norm_num
  refine ⟨?_, ?_, hvlo, hvhi⟩
  · rw [Real.sqrt_eq_rpow, ← Real.rpow_add hT]
    convert hHlo using 1 <;> ring
  · rw [Real.sqrt_eq_rpow, ← Real.rpow_add hT]
    exact huhi

end Erdos587
