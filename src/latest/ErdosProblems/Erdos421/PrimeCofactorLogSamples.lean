import ErdosProblems.Erdos421.PrimeCofactorSamples
import ErdosProblems.Erdos421.InverseLogParameters

/-! # Unconditional logarithmic bounds for simultaneous prime/cofactor samples -/

namespace Erdos421

open Complex Filter Topology

theorem prime_cofactor_sample_log_saving {k : ℕ} (hk : 5 ≤ k) {e A ε : ℝ}
    (he : 0 < e) (hA : 0 ≤ A) (hε : 0 < ε) :
    ∀ᶠ X : ℕ in atTop, ∀ M H J : ℕ, 1 ≤ M → 1 ≤ H → M ≤ X → H ≤ X → J ≤ H → M * H = X →
      (X : ℝ) ^ (1 / ((k : ℝ) + 1)) ≤ H → (H : ℝ) ≤ (X : ℝ) ^ (1 / (k : ℝ)) →
      ∀ (S : Finset ℕ) (a : ℕ → ℂ), (∀ n ∈ S, M ≤ n ∧ n ≤ 2 * M) →
      (∀ n ∈ S, ‖a n‖ ≤ 1) → S.card ≤ M →
      ∀ σ u v : ℝ, 1 ≤ σ → (Real.log X) ^ (2 * (A + twoFactorSampleExponent k) + 9) ≤ u →
      u ≤ v → v ≤ X → v - u ≤ (X : ℝ) ^ (9 / 10 - e) →
      ∀ (F : Finset ℕ) (t : ℕ → ℝ), (∀ i ∈ F, u ≤ t i ∧ t i ≤ v) →
      (∀ i ∈ F, ∀ j ∈ F, i ≠ j → 1 ≤ |t i - t j|) →
      ∀ V W : ℝ, 0 < V → 0 < W →
      (∀ i ∈ F, V ≤ ‖dirichletPolynomial S a (σ + t i * I)‖) →
      (∀ i ∈ F, W ≤ ‖primeDirichletBlock H J (σ + t i * I)‖) →
      (F.card : ℝ) * V ^ 2 * W ^ 2 ≤ ε / (Real.log X) ^ A := by
  let d : ℝ := min (e / 2) (1 / (60 * k))
  let δ : ℝ := 1 / ((k : ℝ) + 1)
  let P : ℝ := A + twoFactorSampleExponent k
  let C : ℝ := twoFactorSampleConstant k
  let ε₀ : ℝ := ε / (2 * C)
  have hkp : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hd : 0 < d := by dsimp only [d]; positivity
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  have hP : 0 ≤ P := by dsimp only [P]; positivity
  have hC : 0 < C := (twoFactorSampleConstant_bounds k).1
  have hε₀ : 0 < ε₀ := by dsimp only [ε₀]; positivity
  have hlargeLog : ∀ᶠ X : ℕ in atTop, 1 ≤ Real.log X :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop _)
  filter_upwards [primeDirichletBlock_ambient_log_saving hδ hP hε₀,
    inverse_log_above_inverse_power hd hε₀ P, eventually_ge_atTop (2 : ℕ), hlargeLog]
    with X hsave hηlower hX hlog
  intro M H J hM hH hMX hHX hJ hprod hHlo hHhi S a hS ha hcard σ u v hσ hlo huv hhi htime
    F t ht hsep V W hV hW hlargeM hlargeH
  have hlogp : 0 < Real.log X := by linarith
  by_cases hF : F.Nonempty
  · obtain ⟨i, hi⟩ := hF
    have hV1 : V ≤ 1 := (hlargeM i hi).trans
      (dirichletPolynomial_norm_le_one S a hM (fun n hn ↦ (hS n hn).1) ha hcard hσ (t i))
    have hti : 0 ≤ t i :=
      (Real.rpow_nonneg (Real.log_natCast_nonneg X) _).trans (hlo.trans (ht i hi).1)
    have hprime : ‖primeDirichletBlock H J (σ + t i * I)‖ ≤ ε₀ / (Real.log X) ^ P := by
      apply hsave H J hHlo hHX hJ (σ + t i * I)
      · simpa only [add_re, ofReal_re, mul_I_re, ofReal_im, neg_zero, add_zero] using hσ
      · simpa only [add_im, ofReal_im, mul_I_im, ofReal_re, zero_add, abs_of_nonneg hti]
          using hlo.trans (ht i hi).1
      · simpa only [add_im, ofReal_im, mul_I_im, ofReal_re, zero_add, abs_of_nonneg hti]
          using (ht i hi).2.trans hhi
    have hWη : W ≤ ε₀ / (Real.log X) ^ P := (hlargeH i hi).trans hprime
    have hprod' : (M : ℝ) * H = X := by exact_mod_cast hprod
    have hb := prime_cofactor_sample_numeric_bound hX hM hH hMX hHX hJ hlog hprod'
      S a hS ha hσ hk he.le (min_le_left _ _) (min_le_right _ _) hHlo hHhi hηlower
      F t huv htime ht hsep hV hW hV1 hWη hlargeM hlargeH
    apply hb.trans_eq
    exact twoFactor_log_weight_identity hlogp hC (twoFactorSampleExponent k)
  · have hcard0 : F.card = 0 := Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hF)
    simp only [hcard0, Nat.cast_zero, zero_mul]
    positivity

end Erdos421
