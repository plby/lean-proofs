import ErdosProblems.Erdos421.PrimeFactorMeanSquare

/-! # Logarithmic mean-square savings when the cofactor is at least the time length -/

namespace Erdos421

open Complex MeasureTheory Filter Topology

theorem dirichlet_mean_factor_le_log {X M U C : ℕ} (hX : 2 ≤ X) (hM : 1 ≤ M)
    (hMX : M ≤ X) (hUM : U ≤ 2 * M) (hCM : C ≤ M) {u v : ℝ}
    (huv : u ≤ v) (hlen : v - u ≤ M) (hlog : 1 ≤ Real.log X) :
    (v - u + 4 * U * (1 + Real.log U)) * C / (M : ℝ) ^ 2 ≤ 25 * Real.log X := by
  have hMp : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hXp : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hlogp : 0 < Real.log X := by linarith
  have hUlog : Real.log U ≤ 2 * Real.log X := by
    by_cases hU : U = 0
    · subst U
      simp only [Nat.cast_zero, Real.log_zero]
      positivity
    have hUpos : (0 : ℝ) < U := by exact_mod_cast Nat.pos_of_ne_zero hU
    have hb := Real.log_le_log hUpos (by exact_mod_cast
      (show U ≤ 2 * X by omega) : (U : ℝ) ≤ 2 * X)
    have hlog2X : Real.log (2 * X) ≤ 2 * Real.log X := by
      simpa only [two_mul] using (unsmoothing_log_bounds
        (by exact_mod_cast hX) hXp.le le_rfl).2
    exact hb.trans hlog2X
  have hUr : (U : ℝ) ≤ 2 * M := by exact_mod_cast hUM
  have hCr : (C : ℝ) ≤ M := by exact_mod_cast hCM
  have hfactor : 0 ≤ v - u + 4 * U * (1 + Real.log U) := by
    have := Real.log_natCast_nonneg U
    positivity
  have hupper : v - u + 4 * U * (1 + Real.log U) ≤
      (M : ℝ) * (1 + 8 * (1 + 2 * Real.log X)) := by
    have hterm := mul_le_mul hUr (add_le_add le_rfl hUlog)
      (by positivity : 0 ≤ 1 + Real.log U) (by positivity : (0 : ℝ) ≤ 2 * M)
    nlinarith
  have hnum := mul_le_mul hupper hCr (Nat.cast_nonneg C) (by positivity)
  apply (div_le_iff₀ (sq_pos_of_pos hMp)).mpr
  have hscalar : 1 + 8 * (1 + 2 * Real.log X) ≤ 25 * Real.log X := by linarith
  have hprod := mul_le_mul_of_nonneg_right hscalar (sq_nonneg (M : ℝ))
  nlinarith

theorem primeFactor_short_mean_log_saving {δ : ℝ} (hδ : 0 < δ)
    {A ε : ℝ} (hA : 0 ≤ A) (hε : 0 < ε) :
    ∀ᶠ X : ℕ in atTop, ∀ H J : ℕ, (X : ℝ) ^ δ ≤ H → H ≤ X → J ≤ H →
      ∀ (S : Finset ℕ) (a : ℕ → ℂ) (M U : ℕ), 1 ≤ M → M ≤ X → U ≤ 2 * M → S.card ≤ M →
      (∀ n ∈ S, M ≤ n ∧ n ≤ U) → (∀ n ∈ S, ‖a n‖ ≤ 1) →
      ∀ σ u v : ℝ, 1 ≤ σ → (Real.log X) ^ (A + 10) ≤ u → u ≤ v → v ≤ X → v - u ≤ M →
      (∫ t in u..v, ‖dirichletPolynomial S a (σ + t * I) *
        primeDirichletBlock H J (σ + t * I)‖ ^ 2) ≤ ε / (Real.log X) ^ A := by
  let B : ℝ := (A + 1) / 2
  let η : ℝ := Real.sqrt ε / 5
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hη : 0 < η := by dsimp only [η]; positivity
  have hloglarge : ∀ᶠ X : ℕ in atTop, 1 ≤ Real.log X :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop _)
  filter_upwards [primeFactor_ambient_mean_square hδ hB hη, eventually_ge_atTop (2 : ℕ),
    hloglarge] with X hsave hX hlog
  intro H J hXH hHX hJ S a M U hM hMX hUM hcard hS ha σ u v hσ hlo huv hhi hlen
  have hlo' : (Real.log X) ^ (2 * B + 9) ≤ u := by
    simpa only [show 2 * B + 9 = A + 10 by dsimp only [B]; ring] using hlo
  have hb := hsave H J hXH hHX hJ S a M U hM hS ha σ u v hσ hlo' huv hhi
  have hlogp : 0 < Real.log X := by linarith
  have hpow : (Real.log X) ^ A ≠ 0 := (Real.rpow_pos_of_pos hlogp _).ne'
  have he : (η / (Real.log X) ^ B) ^ 2 * (25 * Real.log X) = ε / (Real.log X) ^ A := by
    have hsplit : ((Real.log X) ^ B) ^ 2 = (Real.log X) ^ A * Real.log X := by
      rw [← Real.rpow_mul_natCast hlogp.le B 2]
      simp only [Nat.cast_ofNat]
      rw [show B * (2 : ℝ) = A + 1 by dsimp only [B]; ring,
        Real.rpow_add hlogp A 1, Real.rpow_one]
    have hηsq : 25 * η ^ 2 = ε := by
      dsimp only [η]
      have hsq := Real.sq_sqrt hε.le
      nlinarith
    rw [div_pow, hsplit]
    field_simp
    nlinarith [hηsq]
  exact (hb.trans (mul_le_mul_of_nonneg_left
    (dirichlet_mean_factor_le_log hX hM hMX hUM hcard huv hlen hlog)
    (sq_nonneg _))).trans_eq he

end Erdos421
