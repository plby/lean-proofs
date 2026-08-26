import ErdosProblems.Erdos421.PrimeLogHarmonicBound

/-! # Uniform reciprocal mass of a prime band bounded away from zero scale -/

namespace Erdos421

theorem finite_prime_reciprocal_band_le (P : Finset ℕ) {w z : ℝ}
    (hw : 1 < w) (hz : 2 ≤ z) (hP : ∀ p ∈ P, p.Prime ∧ w ≤ p ∧ (p : ℝ) ≤ z) :
    (∑ p ∈ P, (p : ℝ)⁻¹) ≤ 16 * Real.log z / Real.log w := by
  have hlw : 0 < Real.log w := Real.log_pos hw
  apply (le_div_iff₀ hlw).mpr
  calc
    _ = ∑ p ∈ P, Real.log w / (p : ℝ) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro p hp
      ring
    _ ≤ ∑ p ∈ P, Real.log (p : ℝ) / p := by
      apply Finset.sum_le_sum
      intro p hp
      exact div_le_div_of_nonneg_right
        (Real.log_le_log (by linarith) (hP p hp).2.1) (Nat.cast_nonneg p)
    _ ≤ _ := finite_prime_log_harmonic_le P hz (fun p hp ↦ ⟨(hP p hp).1, (hP p hp).2.2⟩)

theorem finite_prime_reciprocal_power_band (P : Finset ℕ) {X β γ : ℝ}
    (hX : 1 < X) (hβ : 0 < β) (hγ : 2 ≤ X ^ γ)
    (hP : ∀ p ∈ P, p.Prime ∧ X ^ β ≤ p ∧ (p : ℝ) ≤ X ^ γ) :
    (∑ p ∈ P, (p : ℝ)⁻¹) ≤ 16 * γ / β := by
  have hXp : 0 < X := by linarith
  have hLX : 0 < Real.log X := Real.log_pos hX
  have hw : 1 < X ^ β := Real.one_lt_rpow hX hβ
  have hb := finite_prime_reciprocal_band_le P hw hγ hP
  rw [Real.log_rpow hXp, Real.log_rpow hXp] at hb
  have heq : 16 * (γ * Real.log X) / (β * Real.log X) = 16 * γ / β := by field_simp
  rwa [heq] at hb

end Erdos421
