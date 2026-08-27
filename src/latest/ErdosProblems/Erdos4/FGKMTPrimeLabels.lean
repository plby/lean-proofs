import ErdosProblems.Erdos4.FGKMTIdealGain
import Mathlib.NumberTheory.PrimeCounting

/-! The actual finite prime window, with all divisor-coverage hypotheses discharged. -/

open scoped BigOperators

namespace Erdos4.FGKMT

open DivisorCoefficients RestrictedProductNorm Classical

def sievePrimeSet (W R : ℕ) : Finset ℕ := (Nat.primesLE R).filter (fun p => p.Coprime W)

abbrev SievePrime (W R : ℕ) := ↥(sievePrimeSet W R)

def sievePrimeValue (W R : ℕ) (p : SievePrime W R) : ℕ := p

theorem sievePrimeValue_prime (W R : ℕ) (p : SievePrime W R) : (sievePrimeValue W R p).Prime :=
  Nat.prime_of_mem_primesLE (Finset.mem_filter.mp p.property).1

theorem sievePrimeValue_coprime (W R : ℕ) (p : SievePrime W R) :
    (sievePrimeValue W R p).Coprime W := (Finset.mem_filter.mp p.property).2

theorem sievePrimeValue_injective (W R : ℕ) : Function.Injective (sievePrimeValue W R) :=
  Subtype.val_injective

theorem sievePrimeValue_covers (W R : ℕ) (u : ℕ) (huR : u ≤ R) (_hu : Squarefree u)
    (huW : u.Coprime W) : ∀ q ∈ u.primeFactors, ∃ p : SievePrime W R, sievePrimeValue W R p = q := by
  intro q hq
  have hprime := Nat.prime_of_mem_primeFactors hq
  have hqR := (Nat.le_of_mem_primeFactors hq).trans huR
  have hqW := huW.of_dvd_left (Nat.dvd_of_mem_primeFactors hq)
  exact ⟨⟨q, Finset.mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨hqR, hprime⟩, hqW⟩⟩, rfl⟩

theorem rationalSieve_sum_ideal_gain {W R T K k : ℕ} {b : ℝ}
    (hb : 0 < b) (hR : 2 ≤ R) (hT : 1 ≤ T) (hTR : T ^ 2 ≤ R) (hK : 2 ≤ K)
    (hpre : ∀ p : ℕ, p.Prime → p ≤ K → p ∣ W)
    (hmean : (k : ℝ) * rationalMass W b R ≤
      (1 / 4) * (b * rationalSquareMass W b R * (Real.log (R : ℝ) / 2)))
    (hcollision : 4 * (k + 1) ^ 2 ≤ K - 1) :
    ((k : ℝ) * (sieveWindowDensity (sievePrimeValue W R) * rationalMass W b T ^ 2 /
      (2 * rationalSquareMass W b R))) *
        energy (rationalCoefficient (k := k) b R (sievePrimeValue W R)) ≤
      ∑ j : Fin k, rationalIdealForm b R (sievePrimeValue W R) j := by
  have hh := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin k)))
    (fun j _ => rationalIdealForm_energy_gain hb (sievePrimeValue W R)
      (sievePrimeValue_prime W R) (sievePrimeValue_injective W R) hR hT hTR hK
      (sievePrimeValue_coprime W R) (sievePrimeValue_covers W R) hpre j hmean hcollision)
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_assoc] using hh

end Erdos4.FGKMT
