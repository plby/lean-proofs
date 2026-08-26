import ErdosProblems.Erdos421.PrimeCofactorMeanSquare
import ErdosProblems.Erdos421.FactorLengthBands

/-! # A uniform prime/cofactor mean-square estimate up to the fifth-root scale -/

namespace Erdos421

open Complex MeasureTheory Filter Topology

theorem prime_cofactor_uniform_mean_square {δ e A ε : ℝ}
    (hδ : 0 < δ) (he : 0 < e) (hA : 0 ≤ A) (hε : 0 < ε) :
    ∀ᶠ X : ℕ in atTop, ∀ M H J : ℕ, 1 ≤ M → 1 ≤ H → M ≤ X → H ≤ X → J ≤ H → M * H = X →
      (X : ℝ) ^ δ ≤ H → (H : ℝ) ≤ (X : ℝ) ^ (1 / 5 : ℝ) →
      ∀ (S : Finset ℕ) (a : ℕ → ℂ), (∀ n ∈ S, M ≤ n ∧ n ≤ 2 * M) →
      (∀ n ∈ S, ‖a n‖ ≤ 1) → S.card ≤ M →
      ∀ σ u v : ℝ, 1 ≤ σ →
      (Real.log X) ^ (2 * (A + twoFactorSampleExponent (primeFactorMaxMoment δ)) + 13) ≤ u →
      u ≤ v → v + 1 ≤ X → v + 1 - u ≤ (X : ℝ) ^ (9 / 10 - e) →
      (∫ t in u..v, ‖dirichletPolynomial S a (σ + t * I) *
        primeDirichletBlock H J (σ + t * I)‖ ^ 2) ≤ ε / (Real.log X) ^ A := by
  let K := primeFactorMaxMoment δ
  have hall := (Filter.eventually_all_finset (Finset.Icc 5 K)).mpr
    (fun k hk ↦ prime_cofactor_mean_square_log_saving (Finset.mem_Icc.mp hk).1 he hA hε)
  have hlargeLog : ∀ᶠ X : ℕ in atTop, 1 ≤ Real.log X :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop _)
  filter_upwards [hall, eventually_ge_atTop (2 : ℕ), hlargeLog] with X hsave hX hlog
  intro M H J hM hH hMX hHX hJ hprod hHlo hHhi S a hS ha hcard σ u v hσ hlo huv hhi htime
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast (show 1 ≤ X by omega)
  obtain ⟨k, hk, hkK, hlow, hhigh⟩ := exists_factor_length_band hδ hX1 hHlo hHhi
  have hD : twoFactorSampleExponent k ≤ twoFactorSampleExponent K := by
    have hsq := Nat.pow_le_pow_left hkK 2
    dsimp only [twoFactorSampleExponent, K]
    omega
  have hDr : (twoFactorSampleExponent k : ℝ) ≤ twoFactorSampleExponent K := by exact_mod_cast hD
  have hfreq : (Real.log X) ^ (2 * (A + twoFactorSampleExponent k) + 13) ≤ u := by
    apply (Real.rpow_le_rpow_of_exponent_le hlog (by linarith :
      2 * (A + twoFactorSampleExponent k) + 13 ≤ 2 * (A + twoFactorSampleExponent K) + 13)).trans
    exact hlo
  exact hsave k (Finset.mem_Icc.mpr ⟨hk, hkK⟩) M H J hM hH hMX hHX hJ hprod
    hlow hhigh S a hS ha hcard σ u v hσ hfreq huv hhi htime

end Erdos421
