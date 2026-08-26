import ErdosProblems.Erdos421.LowerSieveCoefficientGrowth

/-! # The lower sieve as a single finite divisor sum -/

namespace Erdos421

theorem lowerSieveCoefficient_divisor_sum {D z : ℕ} (hD : 1 ≤ D) (hz : 1 ≤ z)
    (n : ℕ) :
    (∑ k ∈ Finset.Icc 1 (z * D ^ 2), if k ∣ n then lowerSieveCoefficient D z k else 0) =
      canonicalLowerValue D z n := by
  have h := lowerSieveCoefficient_action_primes hD hz (fun k ↦ if k ∣ n then 1 else 0)
  simp only [mul_ite, mul_one, mul_zero, one_dvd, if_true] at h
  rw [h]
  unfold canonicalLowerValue buchstabLowerValue sieveDivisorSum
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hpn : p ∣ n
  · rw [if_pos hpn]
    apply Finset.sum_congr rfl
    intro d hd
    simp only [← Nat.dvd_div_iff_mul_dvd hpn]
  · rw [if_neg hpn]
    apply Finset.sum_eq_zero
    intro d hd
    have hnot : ¬p * d ∣ n := fun hpd ↦ hpn ((dvd_mul_right p d).trans hpd)
    rw [if_neg hnot]

theorem lowerSieveCoefficient_main_sum {D z : ℕ} (hD : 1 ≤ D) (hz : 1 ≤ z) :
    (∑ k ∈ Finset.Icc 1 (z * D ^ 2), lowerSieveCoefficient D z k / (k : ℝ)) =
      canonicalLowerMain D z := by
  have h := lowerSieveCoefficient_action_primes hD hz (fun k ↦ (k : ℝ)⁻¹)
  simp only [Nat.cast_one, inv_one] at h
  change (∑ k ∈ Finset.Icc 1 (z * D ^ 2), lowerSieveCoefficient D z k * (k : ℝ)⁻¹) = _
  rw [h]
  unfold canonicalLowerMain canonicalUpperMain
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro d hd
  simp only [Nat.cast_mul, mul_inv, div_eq_mul_inv]
  ring

theorem lowerSieveCoefficient_pointwise {D z : ℕ} (hD : 1 ≤ D) (hz : 1 ≤ z) (n : ℕ) :
    (∑ k ∈ Finset.Icc 1 (z * D ^ 2), if k ∣ n then lowerSieveCoefficient D z k else 0) ≤
      roughIndicator n z := by
  rw [lowerSieveCoefficient_divisor_sum hD hz]
  exact canonicalLowerValue_le hD z n

theorem exists_bounded_finite_lower_sieve {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ D z : ℕ, 0 < D → 2 ≤ z →
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      16 * Real.exp 1 + 33 + Real.log (32 / ε) ≤ Real.log D / Real.log z →
      ∃ ρ : ℕ → ℝ,
        (∀ k, z * D ^ 2 < k → ρ k = 0) ∧
        (∀ k, 0 < k → |ρ k| ≤ C * (k : ℝ) ^ η) ∧
        (∀ n, (∑ k ∈ Finset.Icc 1 (z * D ^ 2), if k ∣ n then ρ k else 0) ≤
          roughIndicator n z) ∧
        (1 - ε) * roughEulerProduct z ≤
          ∑ k ∈ Finset.Icc 1 (z * D ^ 2), ρ k / (k : ℝ) := by
  obtain ⟨C, hC, hb⟩ := lowerSieveCoefficient_subpower hη
  refine ⟨C, hC, ?_⟩
  intro D z hD hz ε hε hε1 hlevel
  refine ⟨lowerSieveCoefficient D z, fun k hk ↦ lowerSieveCoefficient_support hD (by omega) hk,
    hb D hD z, lowerSieveCoefficient_pointwise hD (by omega), ?_⟩
  rw [lowerSieveCoefficient_main_sum hD (by omega)]
  exact canonicalLowerMain_ge_one_sub hD hz hε hε1 hlevel

end Erdos421
