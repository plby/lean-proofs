import ErdosProblems.Erdos421.PrimeCofactorLogSamples
import ErdosProblems.Erdos421.DyadicSampleEnergy
import ErdosProblems.Erdos421.SamplePacking

/-! # Unconditional mean-square savings at separated sample points -/

namespace Erdos421

open Complex Filter Topology

theorem prime_cofactor_sample_energy_log_saving {k : ℕ} (hk : 5 ≤ k) {e A ε : ℝ}
    (he : 0 < e) (hA : 0 ≤ A) (hε : 0 < ε) :
    ∀ᶠ X : ℕ in atTop, ∀ M H J : ℕ, 1 ≤ M → 1 ≤ H → M ≤ X → H ≤ X → J ≤ H → M * H = X →
      (X : ℝ) ^ (1 / ((k : ℝ) + 1)) ≤ H → (H : ℝ) ≤ (X : ℝ) ^ (1 / (k : ℝ)) →
      ∀ (S : Finset ℕ) (a : ℕ → ℂ), (∀ n ∈ S, M ≤ n ∧ n ≤ 2 * M) →
      (∀ n ∈ S, ‖a n‖ ≤ 1) → S.card ≤ M →
      ∀ σ u v : ℝ, 1 ≤ σ → (Real.log X) ^ (2 * (A + twoFactorSampleExponent k) + 13) ≤ u →
      u ≤ v → v ≤ X → v - u ≤ (X : ℝ) ^ (9 / 10 - e) →
      ∀ (F : Finset ℕ) (t : ℕ → ℝ), (∀ i ∈ F, u ≤ t i ∧ t i ≤ v) →
      (∀ i ∈ F, ∀ j ∈ F, i ≠ j → 1 ≤ |t i - t j|) →
      (∑ i ∈ F, ‖dirichletPolynomial S a (σ + t i * I) *
        primeDirichletBlock H J (σ + t i * I)‖ ^ 2) ≤ ε / (Real.log X) ^ A := by
  let ε₀ : ℝ := ε / (32 * amplitudeLogConstant ^ 2)
  have hκ := amplitudeLogConstant_pos
  have hε₀ : 0 < ε₀ := by dsimp only [ε₀]; positivity
  have hA' : 0 ≤ A + 2 := by linarith
  have hlargeLog : ∀ᶠ X : ℕ in atTop, 1 ≤ Real.log X :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop _)
  filter_upwards [prime_cofactor_sample_log_saving hk he hA' hε₀,
    inverse_log_above_inverse_power (by norm_num : (0 : ℝ) < 1)
      (by positivity : 0 < ε / 4) A, eventually_ge_atTop (2 : ℕ), hlargeLog]
    with X hsave herror hX hlog
  intro M H J hM hH hMX hHX hJ hprod hHlo hHhi S a hS ha hcard σ u v hσ hlo huv hhi htime
    F t ht hsep
  have hlogp : 0 < Real.log X := by linarith
  have hXp : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hu : 0 ≤ u := (Real.rpow_nonneg (Real.log_natCast_nonneg X) _).trans hlo
  have hcardF : (F.card : ℝ) ≤ X + 1 := by
    have hb := separated_sample_card_le F t huv ht hsep
    linarith
  let f : ℕ → ℝ := fun i ↦ ‖dirichletPolynomial S a (σ + t i * I)‖
  let g : ℕ → ℝ := fun i ↦ ‖primeDirichletBlock H J (σ + t i * I)‖
  have hf : ∀ i ∈ F, 0 ≤ f i ∧ f i ≤ 1 := by
    intro i _
    exact ⟨norm_nonneg _, dirichletPolynomial_norm_le_one S a hM
      (fun n hn ↦ (hS n hn).1) ha hcard hσ (t i)⟩
  have hg : ∀ i ∈ F, 0 ≤ g i ∧ g i ≤ 1 := by
    intro i _
    refine ⟨norm_nonneg _, ?_⟩
    dsimp only [g]
    rw [primeDirichletBlock_eq_polynomial]
    exact dirichletPolynomial_norm_le_one (primeBlockSupport H J) (fun _ ↦ 1) hH
      (fun n hn ↦ (primeBlockSupport_bounds hJ n hn).1) (by simp)
      ((primeBlockSupport_card_le H J).trans hJ) hσ (t i)
  have hfreq : (Real.log X) ^ (2 * ((A + 2) + twoFactorSampleExponent k) + 9) ≤ u := by
    convert hlo using 1
    congr 1
    ring
  have hlarge : ∀ T : Finset ℕ, T ⊆ F → ∀ V W : ℝ, 0 < V → 0 < W →
      (∀ i ∈ T, V ≤ f i) → (∀ i ∈ T, W ≤ g i) →
      (T.card : ℝ) * V ^ 2 * W ^ 2 ≤ ε₀ / (Real.log X) ^ (A + 2) := by
    intro T hTF V W hV hW hlargeM hlargeH
    exact hsave M H J hM hH hMX hHX hJ hprod hHlo hHhi S a hS ha hcard σ u v hσ hfreq
      huv hhi htime T t (fun i hi ↦ ht i (hTF hi))
      (fun i hi j hj hij ↦ hsep i (hTF hi) j (hTF hj) hij) V W hV hW hlargeM hlargeH
  have hb := dyadic_sample_square_sum F f g hf hg hX hlog hcardF
    (by positivity : 0 ≤ ε₀ / (Real.log X) ^ (A + 2)) hlarge
  have hbig : 16 * amplitudeLogConstant ^ 2 * (Real.log X) ^ 2 *
      (ε₀ / (Real.log X) ^ (A + 2)) = (ε / 2) / (Real.log X) ^ A := by
    dsimp only [ε₀]
    rw [Real.rpow_add hlogp A 2, Real.rpow_two]
    have hp : (Real.log X) ^ A ≠ 0 := (Real.rpow_pos_of_pos hlogp _).ne'
    field_simp
    ring
  have hsmall : 2 / (X : ℝ) ≤ (ε / 2) / (Real.log X) ^ A := by
    rw [Real.rpow_neg_one] at herror
    have hm : 2 * (X : ℝ)⁻¹ ≤ 2 * ((ε / 4) / (Real.log X) ^ A) :=
      mul_le_mul_of_nonneg_left herror (by norm_num : (0 : ℝ) ≤ 2)
    calc
      _ = 2 * (X : ℝ)⁻¹ := by ring
      _ ≤ 2 * ((ε / 4) / (Real.log X) ^ A) := hm
      _ = _ := by ring
  have hsum : (∑ i ∈ F, ‖dirichletPolynomial S a (σ + t i * I) *
      primeDirichletBlock H J (σ + t i * I)‖ ^ 2) = ∑ i ∈ F, (f i) ^ 2 * (g i) ^ 2 := by
    simp only [norm_mul, mul_pow, f, g]
  rw [hsum]
  rw [hbig] at hb
  exact (hb.trans (add_le_add le_rfl hsmall)).trans_eq (by ring)

end Erdos421
