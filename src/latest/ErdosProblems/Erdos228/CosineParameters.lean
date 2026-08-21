import ErdosProblems.Erdos228.CosineConstruction

/-!
# Existence of parameters for the cosine construction

This file supplies the elementary dyadic parameter choice required by
`CosineConstruction.Parameters`.
-/

namespace Erdos228.CosineConstruction

open Filter

noncomputable section

private lemma parameterNumerator_two_mul_add_one_add_one (k : ℕ) :
    parameterNumerator (2 * k + 1) + 1 = 4098 * 4 ^ k := by
  have hpow : 0 < 2 ^ ((2 * k + 1) + 11) := by positivity
  have hone : 1 ≤ 2 ^ ((2 * k + 1) + 11) + 2 ^ (2 * k + 1) :=
    hpow.trans_le (Nat.le_add_right _ _)
  rw [parameterNumerator, Nat.sub_add_cancel hone]
  simp [pow_add, pow_mul]
  ring

/-- For every sufficiently large `n`, the odd dyadic scale needed by the
cosine construction can be chosen in the prescribed quantitative window. -/
theorem eventually_exists_parameters :
    ∀ᶠ n : ℕ in atTop, ∃ t gamma, Parameters n t gamma := by
  filter_upwards [eventually_ge_atTop (2 ^ 40 * 4098)] with n hn
  have hnpos : 0 < n := lt_of_lt_of_le (by positivity) hn
  have hx : (1 : ℝ) ≤ (n : ℝ) / (2 ^ 40 * 4098) := by
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ 40 * 4098)]
    exact_mod_cast hn
  obtain ⟨k, hklo, hkhi⟩ := exists_nat_pow_near hx (by norm_num : (1 : ℝ) < 4)
  let t := 2 * k + 1
  let gamma := (parameterNumerator t : ℝ) / n
  refine ⟨t, gamma, ?_⟩
  constructor
  · exact hnpos
  · exact ⟨k, by simp [t]⟩
  · dsimp only [gamma]
    field_simp
  · dsimp only [gamma, t]
    have hnum : ((parameterNumerator (2 * k + 1) : ℕ) : ℝ) + 1 =
        4098 * 4 ^ k := by
      exact_mod_cast parameterNumerator_two_mul_add_one_add_one k
    rw [lt_div_iff₀ (by positivity : (0 : ℝ) < (n : ℝ))]
    have hkpow : (1 : ℝ) ≤ 4 ^ k := one_le_pow₀ (by norm_num)
    have hnupper : (n : ℝ) < (2 ^ 40 * 4098) * 4 ^ (k + 1) := by
      simpa [mul_comm] using (div_lt_iff₀
        (by positivity : (0 : ℝ) < 2 ^ 40 * 4098)).mp hkhi
    rw [show (4 : ℝ) ^ (k + 1) = 4 ^ k * 4 by rw [pow_succ]] at hnupper
    norm_num at hnupper ⊢
    nlinarith
  · dsimp only [gamma, t]
    have hnum : ((parameterNumerator (2 * k + 1) : ℕ) : ℝ) + 1 =
        4098 * 4 ^ k := by
      exact_mod_cast parameterNumerator_two_mul_add_one_add_one k
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ))]
    have hnlower : (2 ^ 40 * 4098 : ℝ) * 4 ^ k ≤ n := by
      simpa [mul_comm] using (le_div_iff₀
        (by positivity : (0 : ℝ) < 2 ^ 40 * 4098)).mp hklo
    norm_num at hnlower ⊢
    nlinarith

end

end Erdos228.CosineConstruction
