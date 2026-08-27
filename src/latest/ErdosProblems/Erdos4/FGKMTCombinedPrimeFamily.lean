import ErdosProblems.Erdos4.FGKMTSmallPrimeFamily
import ErdosProblems.Erdos4.FGKMTProjectionTail

/-! A disjoint prime family for the small mask and the large rational sieve. -/

namespace Erdos4.FGKMT

instance largeSievePrime_fact (W R : ℕ) (p : SievePrime W R) :
    Fact (sievePrimeValue W R p).Prime := ⟨sievePrimeValue_prime W R p⟩

theorem exception_dvd_harmonicModulus (D B : ℕ) : B ∣ harmonicModulus D B := by
  unfold harmonicModulus
  split_ifs with h
  · exact h
  · exact dvd_mul_left B (primorial D)

theorem smallSievePrime_le (D B : ℕ) (p : SmallSievePrime D B) : smallSievePrimeValue D B p ≤ D :=
  (Nat.mem_primesLE.mp (Finset.mem_erase.mp p.property).2).1

theorem sievePrimeValue_le (W R : ℕ) (p : SievePrime W R) : sievePrimeValue W R p ≤ R :=
  (Nat.mem_primesLE.mp (Finset.mem_filter.mp p.property).1).1

abbrev CombinedSievePrime (D R B : ℕ) := SmallSievePrime D B ⊕ SievePrime (harmonicModulus D B) R

def combinedSievePrimeValue (D R B : ℕ) : CombinedSievePrime D R B → ℕ
  | Sum.inl p => smallSievePrimeValue D B p
  | Sum.inr p => sievePrimeValue (harmonicModulus D B) R p

instance combinedSievePrime_fact (D R B : ℕ) (p : CombinedSievePrime D R B) :
    Fact (combinedSievePrimeValue D R B p).Prime := by
  cases p with
  | inl p => exact ⟨smallSievePrime_prime D B p⟩
  | inr p => exact ⟨sievePrimeValue_prime (harmonicModulus D B) R p⟩

theorem combinedSievePrime_injective (D R B : ℕ) : Function.Injective (combinedSievePrimeValue D R B) := by
  have hlarge (p : SievePrime (harmonicModulus D B) R) : D < sievePrimeValue (harmonicModulus D B) R p :=
    sievePrimeValue_above_precut (fun q hq hqD => small_prime_dvd_harmonicModulus D B hq hqD) p
  intro p q hpq
  cases p with
  | inl p =>
    cases q with
    | inl q => exact congrArg Sum.inl (smallSievePrime_injective D B hpq)
    | inr q =>
      have hpD := smallSievePrime_le D B p
      have hqD := hlarge q
      change smallSievePrimeValue D B p = sievePrimeValue (harmonicModulus D B) R q at hpq
      omega
  | inr p =>
    cases q with
    | inl q =>
      have hqD := smallSievePrime_le D B q
      have hpD := hlarge p
      change sievePrimeValue (harmonicModulus D B) R p = smallSievePrimeValue D B q at hpq
      omega
    | inr q => exact congrArg Sum.inr (sievePrimeValue_injective (harmonicModulus D B) R hpq)

theorem combinedSievePrime_coprime_exception (D R : ℕ) {B : ℕ} (hB : B = 1 ∨ B.Prime)
    (p : CombinedSievePrime D R B) : (combinedSievePrimeValue D R B p).Coprime B := by
  cases p with
  | inl p => exact smallSievePrime_coprime_exception D hB p
  | inr p =>
    exact (sievePrimeValue_coprime (harmonicModulus D B) R p).of_dvd_right
      (exception_dvd_harmonicModulus D B)

theorem combinedSievePrime_le {D R : ℕ} (hDR : D ≤ R) (B : ℕ) (p : CombinedSievePrime D R B) :
    combinedSievePrimeValue D R B p ≤ R := by
  cases p with
  | inl p => exact (smallSievePrime_le D B p).trans hDR
  | inr p => exact sievePrimeValue_le (harmonicModulus D B) R p

def sievePrimeShifts {k : ℕ} (W R : ℕ) (h : Fin k → ℕ) :
    ∀ p : SievePrime W R, Fin k → ZMod (sievePrimeValue W R p) := fun _ i => h i

theorem natCast_shifts_injective {p k : ℕ} [Fact p.Prime] (h : Fin k → ℕ)
    (hinj : Function.Injective h) (hbound : ∀ i, h i < p) :
    Function.Injective (fun i => (h i : ZMod p)) := by
  intro i j hij
  apply hinj
  have hh := congrArg ZMod.val hij
  simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt (hbound i), Nat.mod_eq_of_lt (hbound j)] using hh

theorem sievePrimeShifts_injective {W R D k : ℕ} (h : Fin k → ℕ)
    (hinj : Function.Injective h) (hbound : ∀ i, h i ≤ D)
    (hpre : ∀ p : ℕ, p.Prime → p ≤ D → p ∣ W) (p : SievePrime W R) :
    Function.Injective (sievePrimeShifts W R h p) :=
  natCast_shifts_injective h hinj (fun i => (hbound i).trans_lt (sievePrimeValue_above_precut hpre p))

end Erdos4.FGKMT
