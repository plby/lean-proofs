import ErdosProblems.Erdos421.Buchstab
import ErdosProblems.Erdos421.UniformResidueSieve
import Mathlib.NumberTheory.Primorial

/-! # Prime products and the pointwise upper-sieve inequality -/

namespace Erdos421

def primeProductBelow (z : ℕ) : ℕ := primorial (z - 1)

theorem primeProductBelow_squarefree (z : ℕ) : Squarefree (primeProductBelow z) :=
  squarefree_primorial (z - 1)

theorem prime_dvd_primeProductBelow_iff {p z : ℕ} (hp : p.Prime) :
    p ∣ primeProductBelow z ↔ p < z := by
  rw [primeProductBelow, hp.dvd_primorial_iff]
  have hp2 := hp.two_le
  omega

theorem roughAt_iff_coprime_primeProduct (n z : ℕ) :
    RoughAt n z ↔ Nat.Coprime (primeProductBelow z) n := by
  constructor
  · intro hn
    apply Nat.coprime_of_dvd
    intro p hp hpd
    exact hn p hp ((prime_dvd_primeProductBelow_iff hp).mp hpd)
  · intro hn p hp hpz hpn
    have hpd := (prime_dvd_primeProductBelow_iff hp).mpr hpz
    exact (hp.coprime_iff_not_dvd.mp (hn.coprime_dvd_left hpd)) hpn

noncomputable def roughIndicator (n z : ℕ) : ℝ := by
  classical
  exact if RoughAt n z then 1 else 0

theorem roughIndicator_nonneg (n z : ℕ) : 0 ≤ roughIndicator n z := by
  unfold roughIndicator
  split_ifs <;> norm_num

theorem upper_sieve_pointwise (ρ : ℕ → ℝ) (hρ : BoundingSieve.IsUpperMoebius ρ)
    (n z : ℕ) : roughIndicator n z ≤
      ∑ d ∈ (primeProductBelow z).divisors, if d ∣ n then ρ d else 0 := by
  classical
  let P := primeProductBelow z
  have hP : P ≠ 0 := (primeProductBelow_squarefree z).ne_zero
  have hs := hρ (Nat.gcd P n)
  have hleft : (if Nat.gcd P n = 1 then (1 : ℝ) else 0) = roughIndicator n z := by
    simp only [roughIndicator, roughAt_iff_coprime_primeProduct, Nat.Coprime, P]
  have hdiv : P.divisors.filter (fun d ↦ d ∣ n) = (Nat.gcd P n).divisors := by
    rw [← Nat.divisors_filter_dvd_of_dvd hP (Nat.gcd_dvd_left P n)]
    ext d
    simp only [Finset.mem_filter, Nat.dvd_gcd_iff]
    constructor
    · rintro ⟨hd, hdn⟩
      exact ⟨hd, Nat.dvd_of_mem_divisors hd, hdn⟩
    · rintro ⟨hd, hdP, hdn⟩
      exact ⟨hd, hdn⟩
  rw [hleft, ← hdiv, Finset.sum_filter] at hs
  exact hs

end Erdos421
