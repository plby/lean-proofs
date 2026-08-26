import ErdosProblems.Erdos1148.RealDirichletZeroAlternative

/-! # A uniform polynomial lower bound or a zero in a prescribed interval -/

namespace Erdos1148.DukeArithmetic

lemma hyperbola_error_at_scaled_square {δ : ℝ} (hδ : 0 < δ) (hδ4 : δ ≤ 1 / 4)
    {C q : ℕ} (hC : 0 < C) (hq : 0 < q) (hCδ : 24 ≤ δ * C) :
    12 * ((q : ℝ) / (1 - (1 - δ))) * (((C * q) ^ 2 : ℕ) : ℝ) ^
      (1 - 2 * (1 - δ)) ≤ 1 / 2 := by
  have hC0 : (0 : ℝ) < C := by exact_mod_cast hC
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hCq : (0 : ℝ) < C * q := mul_pos hC0 hq0
  have hN1 : (1 : ℝ) ≤ (((C * q) ^ 2 : ℕ) : ℝ) := by
    exact_mod_cast Nat.pow_pos (Nat.mul_pos hC hq)
  have hp : (((C * q) ^ 2 : ℕ) : ℝ) ^ (1 - 2 * (1 - δ)) ≤ 1 / ((C : ℝ) * q) := by
    calc
      _ ≤ (((C * q) ^ 2 : ℕ) : ℝ) ^ (-(1 / 2) : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
      _ = ((C : ℝ) * q) ^ (-1 : ℝ) := by
        rw [Nat.cast_pow, Nat.cast_mul, ← Real.rpow_natCast_mul hCq.le]
        norm_num
      _ = _ := by rw [Real.rpow_neg_one, one_div]
  rw [show 1 - (1 - δ) = δ by ring]
  calc
    _ ≤ 12 * ((q : ℝ) / δ) * (1 / ((C : ℝ) * q)) :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ = 12 / (δ * C) := by field_simp
    _ ≤ _ := by
      apply (div_le_iff₀ (mul_pos hδ hC0)).mpr
      linarith

theorem realDirichlet_polynomial_lower_bound_or_zero {δ : ℝ}
    (hδ : 0 < δ) (hδ4 : δ ≤ 1 / 4) :
    ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ), 0 < q → ∀ (χ : DirichletCharacter ℝ q), χ ≠ 1 →
      c * (q : ℝ) ^ (-(4 * δ)) ≤ realDirichletValue χ 1 ∨
        ∃ β : ℝ, 1 - δ ≤ β ∧ β < 1 ∧ realDirichletValue χ β = 0 := by
  obtain ⟨C, hC⟩ := exists_nat_gt (24 / δ)
  have hC0 : (0 : ℝ) < C := (by positivity : (0 : ℝ) < 24 / δ).trans hC
  have hCnat : 0 < C := Nat.cast_pos.mp hC0
  have hCδ : 24 ≤ δ * C := by
    have h := (div_lt_iff₀ hδ).mp hC
    nlinarith
  let c := δ / (2 * (C : ℝ) ^ (4 * δ))
  refine ⟨c, by dsimp [c]; positivity, ?_⟩
  intro q hq χ hχ
  let : NeZero q := ⟨Nat.ne_zero_of_lt hq⟩
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hN : 0 < (C * q) ^ 2 := Nat.pow_pos (Nat.mul_pos hCnat hq)
  have hs : 0 < 1 - δ := by linarith
  have hs1 : 1 - δ < 1 := by linarith
  rcases realDirichlet_lower_bound_or_zero χ hχ hs hs1 hN
    (hyperbola_error_at_scaled_square hδ hδ4 hCnat hq hCδ) with hbound | hzero
  · left
    have hp : ((((C * q) ^ 2 * (C * q) ^ 2 : ℕ) : ℝ) ^ (1 - (1 - δ))) =
        (C : ℝ) ^ (4 * δ) * (q : ℝ) ^ (4 * δ) := by
      rw [show (C * q) ^ 2 * (C * q) ^ 2 = (C * q) ^ 4 by ring,
        Nat.cast_pow, Nat.cast_mul, show 1 - (1 - δ) = δ by ring,
        ← Real.rpow_natCast_mul (mul_nonneg hC0.le hq0.le)]
      norm_num only [Nat.cast_ofNat]
      rw [Real.mul_rpow hC0.le hq0.le]
    rw [hp, show 1 - (1 - δ) = δ by ring] at hbound
    convert hbound using 1
    dsimp [c]
    rw [Real.rpow_neg hq0.le]
    ring
  · exact Or.inr hzero

end Erdos1148.DukeArithmetic
