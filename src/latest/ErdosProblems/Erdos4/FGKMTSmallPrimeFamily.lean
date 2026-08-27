import ErdosProblems.Erdos4.FGKMTSmallMaskProduct
import ErdosProblems.Erdos4.FGKMTSmallPresieveModulus

/-! The concrete small-prime mask family, excluding the exceptional prime. -/

open scoped BigOperators

namespace Erdos4.FGKMT

open BoundedGaps.Maynard Classical

theorem sieveWindowDensity_eq_product_density {P : Type*} [Fintype P] [DecidableEq P]
    (ell : P → ℕ) (hprime : ∀ p, (ell p).Prime) (hinj : Function.Injective ell) :
    sieveWindowDensity ell = coprimeHarmonicDensity (∏ p, ell p) := by
  have hphi : (∏ p, ell p).totient = ∏ p, (ell p - 1) := by
    simpa only [DivisorCoefficients.coordinateDivisor, if_true] using
      totient_coordinateDivisor ell hprime hinj (fun _ => some (0 : Fin 1)) 0
  unfold coprimeHarmonicDensity sieveWindowDensity
  rw [hphi, Nat.cast_prod, Nat.cast_prod, ← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro p _
  rw [Nat.cast_sub (hprime p).one_le, Nat.cast_one]

abbrev SmallSievePrime (D B : ℕ) := ↥(smallPresievePrimeSet D B)

def smallSievePrimeValue (D B : ℕ) (p : SmallSievePrime D B) : ℕ := p

theorem smallSievePrime_prime (D B : ℕ) (p : SmallSievePrime D B) :
    (smallSievePrimeValue D B p).Prime :=
  Nat.prime_of_mem_primesLE (Finset.mem_erase.mp p.property).2

instance smallSievePrime_fact (D B : ℕ) (p : SmallSievePrime D B) :
    Fact (smallSievePrimeValue D B p).Prime := ⟨smallSievePrime_prime D B p⟩

theorem smallSievePrime_ne_exception (D B : ℕ) (p : SmallSievePrime D B) :
    smallSievePrimeValue D B p ≠ B := (Finset.mem_erase.mp p.property).1

theorem smallSievePrime_coprime_exception (D : ℕ) {B : ℕ} (hB : B = 1 ∨ B.Prime)
    (p : SmallSievePrime D B) : (smallSievePrimeValue D B p).Coprime B := by
  rcases hB with rfl | hB
  · exact Nat.coprime_one_right _
  · exact (Nat.coprime_primes (smallSievePrime_prime D B p) hB).mpr (smallSievePrime_ne_exception D B p)

theorem smallSievePrime_injective (D B : ℕ) : Function.Injective (smallSievePrimeValue D B) :=
  Subtype.val_injective

theorem smallSievePrime_product (D B : ℕ) :
    (∏ p : SmallSievePrime D B, smallSievePrimeValue D B p) = smallPresieveModulus D B :=
  Finset.prod_coe_sort (smallPresievePrimeSet D B) id

theorem smallSievePrime_density (D B : ℕ) :
    sieveWindowDensity (smallSievePrimeValue D B) = coprimeHarmonicDensity (smallPresieveModulus D B) := by
  rw [sieveWindowDensity_eq_product_density (smallSievePrimeValue D B)
    (smallSievePrime_prime D B) (smallSievePrime_injective D B), smallSievePrime_product]

theorem smallSievePrime_density_ratio (D : ℕ) {B : ℕ} (hB : B = 1 ∨ B.Prime) :
    (1 / 2 : ℝ) ≤ coprimeHarmonicDensity (harmonicModulus D B) /
      sieveWindowDensity (smallSievePrimeValue D B) := by
  have hδ : 0 < sieveWindowDensity (smallSievePrimeValue D B) :=
    UnitFourier.unitDensity_pos (smallSievePrimeValue D B)
  apply (le_div_iff₀ hδ).mpr
  rw [smallSievePrime_density]
  simpa only [one_div_mul_eq_div] using harmonicDensity_smallPresieve_lower D hB

def smallSieveShifts {k : ℕ} (D B : ℕ) (h : Fin k → ℕ) :
    ∀ p : SmallSievePrime D B, Fin k → ZMod (smallSievePrimeValue D B p) := fun _ i => h i

theorem smallSieveShifts_admissible {k : ℕ} (D B : ℕ) (h : Fin k → ℕ)
    (hadm : ∀ p : ℕ, p.Prime → ∃ b : ZMod p, ∀ i, b + (h i : ZMod p) ≠ 0)
    (p : SmallSievePrime D B) : ∃ b, SmallPrimeGood (smallSieveShifts D B h p) b :=
  hadm _ (smallSievePrime_prime D B p)

theorem smallSieve_density_pos {k : ℕ} (D B : ℕ) (h : Fin k → ℕ)
    (hadm : ∀ p : ℕ, p.Prime → ∃ b : ZMod p, ∀ i, b + (h i : ZMod p) ≠ 0) :
    0 < smallProductDensity (smallSievePrimeValue D B) (smallSieveShifts D B h) :=
  smallProductDensity_pos _ _ (smallSieveShifts_admissible D B h hadm)

theorem smallSieve_density_ge_inv {k : ℕ} (D B : ℕ) (h : Fin k → ℕ)
    (hadm : ∀ p : ℕ, p.Prime → ∃ b : ZMod p, ∀ i, b + (h i : ZMod p) ≠ 0) :
    (smallPresieveModulus D B : ℝ)⁻¹ ≤
      smallProductDensity (smallSievePrimeValue D B) (smallSieveShifts D B h) := by
  have hh := smallProductDensity_ge_inv (smallSievePrimeValue D B) (smallSieveShifts D B h)
    (smallSieveShifts_admissible D B h hadm)
  rwa [smallSievePrime_product] at hh

end Erdos4.FGKMT
