import ErdosProblems.Erdos67b.MRCofactorPerron
import ErdosProblems.Erdos67b.MRGSA10RpowAverage

/-!
# Distance retained under denominator scaling

Retaining the scale parameter gives a distance lower bound independent of
the reciprocal mass of the selected primes. Its exponential can be
averaged before taking a uniform cofactor bound.
-/

open scoped BigOperators ComplexConjugate

namespace Erdos67b

open MRHalaszBands

noncomputable section

theorem mrPretentiousTerm_scaled_ge_mul
    {A : Finset ℕ} (hA : ∀ p ∈ A, p.Prime)
    {f g : ℕ → ℂ} {u : ℝ} (hu : u ≤ 1) {p : ℕ} (hp : p.Prime)
    (hf : ‖f p‖ ≤ 1) (hg : ‖g p‖ ≤ 1) :
    u * pretentiousTerm f g p ≤ pretentiousTerm (mrPrimeScaledCoefficient A f u) g p := by
  by_cases hpA : p ∈ A
  · rw [pretentiousTerm, pretentiousTerm, mrPrimeScaledCoefficient_at_prime hA f u hp, if_pos hpA]
    have hre : (f p * (u : ℂ) * conj (g p)).re = u * (f p * conj (g p)).re := by
      rw [show f p * (u : ℂ) * conj (g p) = (u : ℂ) * (f p * conj (g p)) by ring]
      simp [Complex.mul_re]
    rw [hre, ← mul_div_assoc]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg p)
    nlinarith
  · have heq : pretentiousTerm (mrPrimeScaledCoefficient A f u) g p = pretentiousTerm f g p := by
      rw [pretentiousTerm, mrPrimeScaledCoefficient_at_prime hA f u hp, if_neg hpA]
      rfl
    rw [heq]
    exact mul_le_of_le_one_left (pretentiousTerm_nonneg hf hg) hu

theorem mrPretentiousDistSq_scaled_ge_mul
    {A : Finset ℕ} (hA : ∀ p ∈ A, p.Prime)
    {f g : ℕ → ℂ} {u : ℝ} (hu : u ≤ 1) (X : ℕ)
    (hf : ∀ p, p.Prime → ‖f p‖ ≤ 1)
    (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1) :
    u * pretentiousDistSq f g X ≤ pretentiousDistSq (mrPrimeScaledCoefficient A f u) g X := by
  unfold pretentiousDistSq
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  have hpPrime := (mem_primesUpTo.mp hp).1
  exact mrPretentiousTerm_scaled_ge_mul hA hu hpPrime (hf p hpPrime) (hg p hpPrime)

theorem mrIntegral_exp_scaledDistance_le_inv {c D : ℝ} (hc : 0 < c) (hD : 0 < D) :
    (∫ u : ℝ in 0..1, Real.exp (-c * u * D)) ≤ (c * D)⁻¹ := by
  have hfun : (fun u : ℝ ↦ Real.exp (-c * u * D)) =
      fun u ↦ Real.exp (-(c * D) * u) := by funext u; congr 1; ring
  rw [hfun, intervalIntegral_exp_neg_mul_eq (mul_pos hc hD).ne']
  rw [mul_one, inv_eq_one_div]
  apply div_le_div_of_nonneg_right _ (mul_pos hc hD).le
  linarith [Real.exp_nonneg (-(c * D))]

end

end Erdos67b
