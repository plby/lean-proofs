/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos822.SharpBoundedMassProgressions
import ErdosProblems.Erdos822.PrimeMassArithmetic
import ErdosProblems.Erdos822.SmallDeterminantFilteredAverage

/-! # A sharp reciprocal bound after charging a determinant prime -/

namespace Erdos822

open scoped BigOperators Classical
open Filter

theorem exists_eventually_sharp_smallDeterminantFiber_bound (C : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ N : ℕ in atTop,
      ∀ (B : Finset ℕ) (x k r m' p h cutoff : ℕ), p.Prime → p ≤ N →
        k ∈ oddSmallFactors N → r ∈ middlePrimes N → 0 < m' →
        (∀ q ∈ largePrimes N, ∀ s ∈ outerPrimes x (k * r * q), k * r * q < s) →
        (∀ s ∈ outerPrimes x m', m' < s) →
        ¬ p ∣ Nat.totient k → ¬ p ∣ r - 1 →
        B ⊆ largeGcdFreeOddCofactors N cutoff →
        (∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ h → cutoff < ℓ) →
        Nat.Coprime p h → 0 < h → h ≤ N ^ 3 → primeDivisorReciprocalMass h ≤ C →
        (∑ q ∈ smallDeterminantLargePrimeFiberIn B N x k r m' p h, (1 : ℝ) / q) ≤
          K / (p * h : ℕ) := by
  obtain ⟨K, hK, hbound⟩ := exists_eventually_boundedMass_prime_progression_mass (C + 1)
  refine ⟨K, hK, ?_⟩
  filter_upwards [hbound, eventually_ge_atTop 2] with N hbound hN
  intro B x k r m' p h cutoff hp hpN hk hr hm' hlarge hlarge' hpK hpR hB hsupport hph hh hhN hmass
  by_cases hne : (smallDeterminantLargePrimeFiberIn B N x k r m' p h).Nonempty
  · obtain ⟨q₁, hq₁⟩ := hne
    have hq₁data := mem_smallDeterminantLargePrimeFiberIn_iff.mp hq₁
    have hbase := mem_smallDeterminantLargePrimeFiber_iff.mp hq₁data.1
    have hcoef : Nat.Coprime h (k * r) :=
      commonDivisor_coprime_leftFactor_of_largeGcdFree (hB hq₁data.2)
        (dvd_mul_right (k * r) q₁) hbase.2.2.1 hsupport
    have hne' : (smallDeterminantLargePrimeFiber N x k r m' p h).Nonempty := ⟨q₁, hq₁data.1⟩
    let q₀ := (smallDeterminantLargePrimeFiber N x k r m' p h).min' hne'
    have hsub := smallDeterminantLargePrimeFiber_subset_mul_residueClass
      (y := 0) hN hp hk hr hm' hlarge hlarge' hpK hpR hcoef hph (by positivity) hne'
    have hmodulus : (p * h) * N ≤ N ^ 21 := by
      calc
        _ ≤ (N * N ^ 3) * N := Nat.mul_le_mul_right _ (Nat.mul_le_mul hpN hhN)
        _ = N ^ 5 := by ring
        _ ≤ N ^ 21 := Nat.pow_le_pow_right (by omega) (by omega)
    have hmass' : primeDivisorReciprocalMass (p * h) ≤ C + 1 :=
      (primeDivisorReciprocalMass_prime_mul_le hp hh.ne').trans (add_le_add hmass le_rfl)
    apply hbound _ (N ^ 21) (p * h) q₀ (mul_pos hp.pos hh) hmodulus hmass'
    intro q hq
    have hqraw := (mem_smallDeterminantLargePrimeFiberIn_iff.mp hq).1
    have hqclass := mem_largePrimeResidueClass_iff.mp (hsub hqraw)
    have hqdata := mem_largePrimes_iff.mp hqclass.1
    have hqne : q ≠ N ^ 21 := by
      intro heq
      exact (Nat.Prime.not_prime_pow (by omega : 2 ≤ 21)) (heq ▸ hqdata.2.2)
    refine ⟨by omega, ?_, hqdata.2.2, hqclass.2.2⟩
    simpa [show N * N ^ 21 = N ^ 22 by ring] using hqdata.2.1
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
    simp only [Finset.sum_empty]
    positivity

#print axioms exists_eventually_sharp_smallDeterminantFiber_bound

end Erdos822
