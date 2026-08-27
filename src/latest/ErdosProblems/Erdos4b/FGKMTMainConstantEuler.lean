/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTMainConstant

/-!
# Changing the forbidden modulus in the harmonic main constant

The Euler product gives an exact finite multiplier when new prime
divisors are added to the forbidden modulus. This identity is the
arithmetic step behind telescoping the multivariate coordinate sums.
-/

namespace Erdos4b.FGKMT

noncomputable section

open ArithmeticFunction Filter
open scoped BigOperators Topology

def sieveEulerFactor (M : ℕ) (g : ℕ → ℝ) (p : ℕ) : ℝ :=
  (1 + if p ∣ M then 0 else 1 / g p) * (1 - 1 / (p : ℝ))

def modulusEulerMultiplier (M e : ℕ) (g : ℕ → ℝ) : ℝ :=
  ∏ p ∈ e.primeFactors, (if p ∣ M then 1 else 1 + 1 / g p)

theorem harmonicCorrection_roughSieveWeight_isMultiplicative (M : ℕ) (g : ℕ → ℝ) :
    (harmonicCorrection (roughSieveWeight M g)).IsMultiplicative := by
  rw [harmonicCorrection_roughSieveWeight_eq]
  exact (roughHarmonicCorrection_isMultiplicative M g).mul (preSieveBoundary_isMultiplicative M)

theorem harmonicCorrection_roughSieveWeight_local_tsum (M : ℕ) (g : ℕ → ℝ)
    {p : ℕ} (hp : p.Prime) :
    (∑' j, harmonicCorrection (roughSieveWeight M g) (p ^ j)) = sieveEulerFactor M g p := by
  rw [tsum_eq_sum (s := Finset.range 3) (fun j hj => by
    have hj3 : 3 ≤ j := by simpa only [Finset.mem_range, not_lt] using hj
    exact harmonicCorrection_squarefreePrimeWeight_prime_pow_ge_three _ hp hj3)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one, zero_add]
  rw [(harmonicCorrection_roughSieveWeight_isMultiplicative M g).map_one]
  rw [roughSieveWeight, harmonicCorrection_squarefreePrimeWeight_prime _ hp,
    harmonicCorrection_squarefreePrimeWeight_prime_sq _ hp]
  unfold sieveEulerFactor
  ring

theorem sieveMainConstant_eulerProduct {M : ℕ} {g : ℕ → ℝ}
    (hs : Summable (fun n => |harmonicCorrection (roughSieveWeight M g) n|)) :
    Tendsto (fun N : ℕ => ∏ p ∈ N.primesBelow, sieveEulerFactor M g p)
      atTop (𝓝 (sieveMainConstant M g)) := by
  have hnorm : Summable (fun n => ‖harmonicCorrection (roughSieveWeight M g) n‖) := by
    simpa only [Real.norm_eq_abs] using hs
  have hEuler := (harmonicCorrection_roughSieveWeight_isMultiplicative M g).eulerProduct hnorm
  apply hEuler.congr'
  apply Eventually.of_forall
  intro N
  apply Finset.prod_congr rfl
  intro p hp
  exact harmonicCorrection_roughSieveWeight_local_tsum M g (Nat.prime_of_mem_primesBelow hp)

theorem sieveEulerFactor_modulus_mul (M e : ℕ) (g : ℕ → ℝ) {p : ℕ} (hp : p.Prime) :
    sieveEulerFactor M g p =
      (if p ∣ e then (if p ∣ M then 1 else 1 + 1 / g p) else 1) *
        sieveEulerFactor (M * e) g p := by
  unfold sieveEulerFactor
  simp only [hp.dvd_mul]
  by_cases hpM : p ∣ M <;> by_cases hpe : p ∣ e <;> simp [hpM, hpe]

theorem sieveEulerProduct_modulus_mul {M e N : ℕ} (he : 0 < e) (hN : e < N)
    (g : ℕ → ℝ) :
    (∏ p ∈ N.primesBelow, sieveEulerFactor M g p) =
      modulusEulerMultiplier M e g * ∏ p ∈ N.primesBelow, sieveEulerFactor (M * e) g p := by
  calc
    _ = ∏ p ∈ N.primesBelow,
        ((if p ∣ e then (if p ∣ M then 1 else 1 + 1 / g p) else 1) *
          sieveEulerFactor (M * e) g p) := by
      apply Finset.prod_congr rfl
      intro p hp
      exact sieveEulerFactor_modulus_mul M e g (Nat.prime_of_mem_primesBelow hp)
    _ = _ := by
      rw [Finset.prod_mul_distrib]
      congr 1
      rw [← Finset.prod_filter, primeFactors_eq_filtered_primesBelow he hN]
      rfl

theorem sieveMainConstant_modulus_mul_of_summable {M e : ℕ} (he : 0 < e)
    (g : ℕ → ℝ)
    (hsM : Summable (fun n => |harmonicCorrection (roughSieveWeight M g) n|))
    (hsMe : Summable (fun n => |harmonicCorrection (roughSieveWeight (M * e) g) n|)) :
    sieveMainConstant M g = modulusEulerMultiplier M e g * sieveMainConstant (M * e) g := by
  have hMe := (sieveMainConstant_eulerProduct hsMe).const_mul (modulusEulerMultiplier M e g)
  have hevent : (fun N : ℕ => modulusEulerMultiplier M e g *
      ∏ p ∈ N.primesBelow, sieveEulerFactor (M * e) g p) =ᶠ[atTop]
      (fun N : ℕ => ∏ p ∈ N.primesBelow, sieveEulerFactor M g p) := by
    filter_upwards [eventually_ge_atTop (e + 1)] with N hN
    exact (sieveEulerProduct_modulus_mul he (by omega) g).symm
  exact tendsto_nhds_unique (sieveMainConstant_eulerProduct hsM) (hMe.congr' hevent)

theorem sieveMainConstant_modulus_mul {k M e : ℕ} (hk : 0 < k) (hM : 0 < M)
    (he : 0 < e) (hsmall : ∀ p : ℕ, p.Prime → p ≤ k ^ 2 → p ∣ M) (g : ℕ → ℝ)
    (hg : ∀ p : ℕ, p.Prime → ¬p ∣ M → (p : ℝ) / 2 ≤ g p)
    (hclose : ∀ p : ℕ, p.Prime → ¬p ∣ M → |g p - p| ≤ 2 * (k : ℝ)) :
    sieveMainConstant M g = modulusEulerMultiplier M e g * sieveMainConstant (M * e) g := by
  have hsM := (harmonicCorrection_roughSieveWeight_moments hk hM hsmall g hg hclose).1
  have hsMe := (harmonicCorrection_roughSieveWeight_moments hk (Nat.mul_pos hM he)
    (fun p hp hpk => dvd_mul_of_dvd_left (hsmall p hp hpk) e) g
    (fun p hp hpMe => hg p hp (fun hpM => hpMe (dvd_mul_of_dvd_left hpM e)))
    (fun p hp hpMe => hclose p hp (fun hpM => hpMe (dvd_mul_of_dvd_left hpM e)))).1
  exact sieveMainConstant_modulus_mul_of_summable he g hsM hsMe

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.sieveMainConstant_modulus_mul
