import ErdosProblems.Erdos587.HooleyMajorantMean
import ErdosProblems.Erdos587.HooleyPowerMargin

/-! # The unconditional quadratic majorant mean in the power-separated range -/

open scoped BigOperators

namespace Erdos587

theorem exists_delta_majorant_power_mean (r : ℕ) (hr : 0 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ M q D : ℕ, 1 ≤ M → 0 < q →
      (q : ℝ) * (M * 2 ^ D : ℕ) ^ (3 / (r : ℝ)) ≤ (M * 2 ^ D : ℕ) →
      ∀ a : ℤ, IsCoprime a (q : ℤ) → ∀ K : ℝ, 0 < K → K ≤ 2 ^ D →
      ∀ S : Finset DeltaApproximant,
      (∀ x ∈ S, 0 < x.index ∧ x.index ≤ M) →
      (∀ x ∈ S, 0 < x.denominator ∧ (x.denominator : ℝ) ≤ K) →
      (∀ x ∈ S, deltaApproximantError a q x ≠ 0) →
      (∀ x ∈ S, |deltaApproximantFrequencyError a q x| ≤
        2 / ((x.denominator : ℝ) * K)) →
      (∑ x ∈ S, deltaQuadraticMajorant K a q x) ≤
        C * (M * 2 ^ D : ℕ) * (max 1 (Real.log (Real.log (M * 2 ^ D : ℕ)))) ^ 7 := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  obtain ⟨C₀, hC₀, hmean⟩ := exists_delta_majorant_mean_with_margin r hr (inv_pos.mpr hrR)
  obtain ⟨C₁, hC₁, hmargin⟩ := exists_delta_power_margin_bound r hr
  refine ⟨C₀ * (1 + C₁), by positivity, ?_⟩
  intro M q D hM hq hsep a hcop K hK hKD S hindex hden hzero herror
  let N := M * 2 ^ D
  let Y := deltaProgressionCutoff r N
  have hDN : 2 ^ D ≤ N := by
    simpa only [one_mul] using Nat.mul_le_mul_right (2 ^ D) hM
  have hN : 1 ≤ N := (Nat.one_le_pow D 2 (by norm_num)).trans hDN
  have hE := hmargin N q D hN hDN hsep
  have h := hmean M q D Y hq (deltaProgressionCutoff_ge_sixteen r N)
    (deltaProgressionCutoff_power hr N) a hcop K hK hKD S hindex hden hzero herror
  let F := (max 1 (Real.log (Real.log (N : ℝ)))) ^ 7
  have hF : 1 ≤ F := one_le_pow₀ (le_max_left _ _)
  have hCF : C₁ * (N : ℝ) ≤ C₁ * (N : ℝ) * F :=
    le_mul_of_one_le_right (by positivity) hF
  calc
    _ ≤ C₀ * ((N : ℝ) * F + C₁ * N) := by
      apply h.trans
      exact mul_le_mul_of_nonneg_left (add_le_add le_rfl hE) hC₀.le
    _ ≤ C₀ * ((N : ℝ) * F + C₁ * N * F) :=
      mul_le_mul_of_nonneg_left (add_le_add le_rfl hCF) hC₀.le
    _ = _ := by dsimp only [F, N]; ring

end Erdos587
