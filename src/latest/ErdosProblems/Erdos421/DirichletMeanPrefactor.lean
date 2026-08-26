import ErdosProblems.Erdos421.DirichletLogPrefactor

/-! # A uniform logarithmic bound for the sampled mean-value prefactor -/

namespace Erdos421

noncomputable def dirichletMeanPrefactorConstant (k : ℕ) : ℝ :=
  (2 + 4 * (k : ℝ) ^ 2) * (1 + 4 * (2 : ℝ) ^ k * (2 * k + 1))

theorem dirichletMeanPrefactorConstant_pos (k : ℕ) :
    0 < dirichletMeanPrefactorConstant k := by
  unfold dirichletMeanPrefactorConstant
  positivity

theorem dirichletMean_prefactor_ambient {X M : ℕ} (hX : 2 ≤ X) (hM : 1 ≤ M)
    (hMX : M ≤ X) (hlog : 1 ≤ Real.log X) (k : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    (2 + (Real.log ((2 * M) ^ k : ℕ)) ^ 2) *
      (T + 1 + 4 * ((2 * M) ^ k : ℕ) * (1 + Real.log ((2 * M) ^ k : ℕ))) ≤
      (dirichletMeanPrefactorConstant k * (Real.log X) ^ 3) * (T + (M : ℝ) ^ k) := by
  have hL : 0 < Real.log X := by linarith
  have hMp : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hMk : (1 : ℝ) ≤ (M : ℝ) ^ k := one_le_pow₀ hM1
  have hlength := dirichlet_log_length_le hX (by omega : 1 ≤ 2 * M) hMX le_rfl
  have hlogN : Real.log ((2 * M) ^ k : ℕ) ≤ 2 * k * Real.log X := by
    rw [Nat.cast_pow, Real.log_pow]
    have h := mul_le_mul_of_nonneg_left hlength (Nat.cast_nonneg k)
    nlinarith
  have hlogN0 := Real.log_natCast_nonneg ((2 * M) ^ k)
  have hfirst : 2 + (Real.log ((2 * M) ^ k : ℕ)) ^ 2 ≤
      (2 + 4 * (k : ℝ) ^ 2) * (Real.log X) ^ 2 := by
    have hs := pow_le_pow_left₀ hlogN0 hlogN 2
    have hL2 : 1 ≤ (Real.log X) ^ 2 := one_le_pow₀ hlog
    nlinarith
  have hlogfactor : 1 + Real.log ((2 * M) ^ k : ℕ) ≤ (2 * k + 1) * Real.log X := by
    nlinarith
  have hNeq : (((2 * M) ^ k : ℕ) : ℝ) = (2 : ℝ) ^ k * (M : ℝ) ^ k := by
    push_cast
    rw [mul_pow]
  have hterm : 4 * ((2 * M) ^ k : ℕ) * (1 + Real.log ((2 * M) ^ k : ℕ)) ≤
      (4 * (2 : ℝ) ^ k * (2 * k + 1)) * Real.log X * (T + (M : ℝ) ^ k) := by
    have h := mul_le_mul_of_nonneg_left hlogfactor
      (by positivity : 0 ≤ 4 * (2 : ℝ) ^ k * (M : ℝ) ^ k)
    have hleft : 4 * ((2 * M) ^ k : ℕ) * (1 + Real.log ((2 * M) ^ k : ℕ)) =
        4 * (2 : ℝ) ^ k * (M : ℝ) ^ k * (1 + Real.log ((2 * M) ^ k : ℕ)) := by
      rw [hNeq]
      ring
    rw [hleft]
    apply h.trans
    have ht := mul_le_mul_of_nonneg_left
      (show (M : ℝ) ^ k ≤ T + (M : ℝ) ^ k by linarith)
      (show 0 ≤ (4 * (2 : ℝ) ^ k * (2 * k + 1)) * Real.log X by positivity)
    nlinarith
  have hsecond : T + 1 + 4 * ((2 * M) ^ k : ℕ) * (1 + Real.log ((2 * M) ^ k : ℕ)) ≤
      (1 + 4 * (2 : ℝ) ^ k * (2 * k + 1)) * Real.log X * (T + (M : ℝ) ^ k) := by
    have hb := mul_le_mul_of_nonneg_right hlog (show 0 ≤ T + (M : ℝ) ^ k by positivity)
    nlinarith
  apply (mul_le_mul hfirst hsecond (by positivity) (by positivity)).trans_eq
  unfold dirichletMeanPrefactorConstant
  ring

end Erdos421
