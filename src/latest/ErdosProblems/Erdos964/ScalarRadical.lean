import Mathlib.RingTheory.Radical.NatInt
import BoundedGaps.Maynard.MaynardPreSievedTotientMean
import BoundedGaps.Maynard.CoprimeHarmonicMainTerm
import BoundedGaps.Maynard.AugmentedPreSievedPrimeMertens

/-!
# Radical and density identities for the scalar means
-/

namespace Erdos964

open scoped BigOperators
open BoundedGaps.Maynard UniqueFactorizationMonoid

theorem coprime_radical_iff (M r : ℕ) (hM : M ≠ 0) :
    r.Coprime (radical M) ↔ r.Coprime M := by
  constructor
  · intro h
    exact (h.pow_right M).coprime_dvd_right (Nat.dvd_radical_pow_self hM)
  · exact fun h => h.coprime_dvd_right radical_dvd_self

theorem totient_density_eq_prime_product (M : ℕ) (hM : 0 < M) :
    (M.totient : ℝ) / M = ∏ p ∈ M.primeFactors, (1 - (p : ℝ)⁻¹) := by
  have h := congrArg (fun q : ℚ => (q : ℝ)) (Nat.totient_eq_mul_prod_factors M)
  norm_num only [Rat.cast_natCast, Rat.cast_mul, Rat.cast_prod, Rat.cast_sub,
    Rat.cast_one, Rat.cast_inv] at h
  have hM0 : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  rw [h]
  field_simp

theorem coprimeHarmonicDensity_radical (M : ℕ) (hM : 0 < M) :
    coprimeHarmonicDensity (radical M) = coprimeHarmonicDensity M := by
  unfold coprimeHarmonicDensity
  rw [totient_density_eq_prime_product _ (Nat.radical_pos M),
    totient_density_eq_prime_product M hM, Nat.primeFactors_radical]

theorem squarefreeCoprimeInvTotientMean_radical (M Q : ℕ) (hM : M ≠ 0) :
    squarefreeCoprimeInvTotientMean (radical M) Q = squarefreeCoprimeInvTotientMean M Q := by
  unfold squarefreeCoprimeInvTotientMean
  apply Finset.sum_congr rfl
  intro n _
  simp only [coprime_radical_iff M n hM]

theorem primeLogDivisorMass_radical (M : ℕ) :
    primeLogDivisorMass (radical M) = primeLogDivisorMass M := by
  unfold primeLogDivisorMass
  rw [Nat.primeFactors_radical]

theorem primeLogDivisorMass_mul_of_coprime (M r : ℕ) (hcop : M.Coprime r) :
    primeLogDivisorMass (M * r) = primeLogDivisorMass M + primeLogDivisorMass r := by
  unfold primeLogDivisorMass
  rw [hcop.primeFactors_mul, Finset.sum_union hcop.disjoint_primeFactors]

theorem coprimeHarmonicDensity_mul (M r : ℕ) (hcop : M.Coprime r) :
    coprimeHarmonicDensity (M * r) = coprimeHarmonicDensity M * coprimeHarmonicDensity r := by
  unfold coprimeHarmonicDensity
  rw [Nat.totient_mul hcop, Nat.cast_mul, Nat.cast_mul]
  ring

theorem scaled_coprimeHarmonicDensity (M r : ℕ) (hr : 0 < r) (hcop : M.Coprime r) :
    ((r : ℝ) / r.totient) * coprimeHarmonicDensity (M * r) = coprimeHarmonicDensity M := by
  rw [coprimeHarmonicDensity_mul M r hcop]
  unfold coprimeHarmonicDensity
  have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  have hphi : (r.totient : ℝ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr hr).ne'
  field_simp

end Erdos964
