import ErdosProblems.Erdos4.FGKMTProjectionComparison
import ErdosProblems.Erdos4.FGKMTPrimeLabels
import ErdosProblems.Erdos4.FGKMTQuantitativeTail
import ErdosProblems.Erdos4.FGKMTGrowingParameters

/-! Explicit reciprocal-square errors for the actual prime window. -/

open scoped BigOperators

namespace Erdos4.FGKMT

open RestrictedProductNorm Classical

theorem sievePrimeValue_above_precut {W R K : ℕ}
    (hpre : ∀ p : ℕ, p.Prime → p ≤ K → p ∣ W) (p : SievePrime W R) :
    K < sievePrimeValue W R p := by
  by_contra hle
  have hprime := sievePrimeValue_prime W R p
  exact (hprime.coprime_iff_not_dvd.mp (sievePrimeValue_coprime W R p))
    (hpre _ hprime (by omega))

theorem sievePrimeValue_square_tail {W R K : ℕ} (hK : 0 < K)
    (hpre : ∀ p : ℕ, p.Prime → p ≤ K → p ∣ W) :
    (∑ p : SievePrime W R, ((sievePrimeValue W R p : ℝ) ^ 2)⁻¹) ≤ (K : ℝ)⁻¹ := by
  have heq : (∑ p : SievePrime W R, ((sievePrimeValue W R p : ℝ) ^ 2)⁻¹) =
      ∑ p ∈ sievePrimeSet W R, ((p : ℝ) ^ 2)⁻¹ :=
    Finset.sum_coe_sort (sievePrimeSet W R) (fun p => ((p : ℝ) ^ 2)⁻¹)
  rw [heq]
  exact finite_reciprocal_square_tail hK (sievePrimeSet W R)
    (fun p hp => sievePrimeValue_above_precut hpre ⟨p, hp⟩)

theorem rational_projection_error_bound {W R K : ℕ} (hK : 0 < K)
    (hpre : ∀ p : ℕ, p.Prime → p ≤ K → p ∣ W) (k : ℕ) :
    (∑ p : SievePrime W R, 10 * (k : ℝ) ^ 2 / (sievePrimeValue W R p : ℝ) ^ 2) ≤
      10 * (k : ℝ) ^ 2 / K := by
  simp only [div_eq_mul_inv, ← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (sievePrimeValue_square_tail hK hpre) (by positivity)

theorem rational_ideal_sub_tail_le_true {W R K k : ℕ} {b : ℝ} (hb : 0 ≤ b)
    (hK : 0 < K) (hk : k + 1 ≤ K)
    (hpre : ∀ p : ℕ, p.Prime → p ≤ K → p ∣ W) (j : Fin k) :
    rationalIdealForm b R (sievePrimeValue W R) j -
      energy (rationalCoefficient (k := k) b R (sievePrimeValue W R)) * (10 * (k : ℝ) ^ 2 / K) ≤
        rationalTrueForm b R (sievePrimeValue W R) j := by
  have hlarge (p : SievePrime W R) : k + 2 ≤ sievePrimeValue W R p := by
    have hh := sievePrimeValue_above_precut hpre p
    omega
  have hlocal := rational_ideal_sub_error_le_true hb R (sievePrimeValue W R) hlarge j
  have herr := mul_le_mul_of_nonneg_left (rational_projection_error_bound (R := R) hK hpre k)
    (energy_nonneg (rationalCoefficient (k := k) b R (sievePrimeValue W R)))
  linarith

theorem rational_ideal_sum_sub_tail_le_true {W R K k : ℕ} {b : ℝ} (hb : 0 ≤ b)
    (hK : 0 < K) (hk : k + 1 ≤ K)
    (hpre : ∀ p : ℕ, p.Prime → p ≤ K → p ∣ W) :
    (∑ j : Fin k, rationalIdealForm b R (sievePrimeValue W R) j) -
      energy (rationalCoefficient (k := k) b R (sievePrimeValue W R)) * (10 * (k : ℝ) ^ 3 / K) ≤
        ∑ j : Fin k, rationalTrueForm b R (sievePrimeValue W R) j := by
  have hh := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin k)))
    (fun j _ => rational_ideal_sub_tail_le_true (R := R) hb hK hk hpre j)
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at hh
  have heq : (k : ℝ) * (energy (rationalCoefficient (k := k) b R (sievePrimeValue W R)) *
      (10 * (k : ℝ) ^ 2 / K)) = energy (rationalCoefficient (k := k) b R (sievePrimeValue W R)) *
        (10 * (k : ℝ) ^ 3 / K) := by ring
  rwa [heq] at hh

theorem growing_projection_loss_le (x : ℕ) :
    10 * (sieveDimension (growingIndex x) : ℝ) ^ 3 / growingPrecutoff x ≤
      1 / (sieveDimension (growingIndex x) : ℝ) := by
  have hk : (0 : ℝ) < sieveDimension (growingIndex x) := by
    exact_mod_cast sieveDimension_pos (growingIndex x)
  unfold growingPrecutoff
  push_cast
  apply (div_le_div_iff₀ (by positivity) hk).mpr
  nlinarith [pow_pos hk 4]

end Erdos4.FGKMT
