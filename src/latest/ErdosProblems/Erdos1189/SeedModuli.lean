/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Turning smaller-prime seed divisors into distinct ordered frame moduli.
Informal source: Sections 5 and 6.3 of Pickhardt and Omniscience Research Agent.
Formal author: OpenAI Codex.
-/

import ErdosProblems.Erdos1189.DigitFrame

namespace Erdos1189

open Finset

def seedModulus {N : ℕ} (seed : PrimeSlot N → ℕ) (s : PrimeSlot N) : ℕ :=
  s.1.1.val ^ (s.1.2.val + 1) * seed s

def SeedsSupportedBelow {N : ℕ} (seed : PrimeSlot N → ℕ) : Prop :=
  ∀ s p, p ∈ (seed s).primeFactors → p < s.1.1.val

lemma seed_coprime {N : ℕ} (hN : N ≠ 0) {seed : PrimeSlot N → ℕ}
    (hdiv : ∀ s, seed s ∣ N) (hsmall : SeedsSupportedBelow seed) (s : PrimeSlot N) :
    s.1.1.val.Coprime (seed s) := by
  have hp := Nat.prime_of_mem_primeFactors s.1.1.2
  apply hp.coprime_iff_not_dvd.mpr
  intro hd
  have hm := hp.mem_primeFactors hd (ne_zero_of_dvd_ne_zero hN (hdiv s))
  exact lt_irrefl _ (hsmall s _ hm)

lemma seedModulus_dvd {N : ℕ} (hN : N ≠ 0) {seed : PrimeSlot N → ℕ}
    (hdiv : ∀ s, seed s ∣ N) (hsmall : SeedsSupportedBelow seed) (s : PrimeSlot N) :
    seedModulus seed s ∣ N := by
  have hp := Nat.prime_of_mem_primeFactors s.1.1.2
  apply ((seed_coprime hN hdiv hsmall s).pow_left _).mul_dvd_of_dvd_of_dvd
  · exact (hp.pow_dvd_iff_le_factorization hN).mpr s.1.2.isLt
  · exact hdiv s

lemma seedModulus_own {N : ℕ} (seed : PrimeSlot N → ℕ) (s : PrimeSlot N) :
    s.1.1.val ^ (s.1.2.val + 1) ∣ seedModulus seed s := dvd_mul_right _ _

lemma seedModulus_factorization {N : ℕ} (hN : N ≠ 0) {seed : PrimeSlot N → ℕ}
    (hdiv : ∀ s, seed s ∣ N) (hsmall : SeedsSupportedBelow seed) (s : PrimeSlot N) :
    (seedModulus seed s).factorization s.1.1.val = s.1.2.val + 1 := by
  have hp := Nat.prime_of_mem_primeFactors s.1.1.2
  have hs0 := ne_zero_of_dvd_ne_zero hN (hdiv s)
  have hnot : ¬ s.1.1.val ∣ seed s := hp.coprime_iff_not_dvd.mp (seed_coprime hN hdiv hsmall s)
  have hf : (seed s).factorization s.1.1.val = 0 :=
    (Nat.factorization_eq_zero_iff _ _).mpr (Or.inr (Or.inl hnot))
  simp only [seedModulus, Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) hs0,
    Finsupp.add_apply, Nat.factorization_pow_self hp, hf, add_zero]

lemma seedModulus_own_prime {N : ℕ} (hN : N ≠ 0) {seed : PrimeSlot N → ℕ}
    (hdiv : ∀ s, seed s ∣ N) (hsmall : SeedsSupportedBelow seed) (s : PrimeSlot N) :
    s.1.1.val ∈ (seedModulus seed s).primeFactors := by
  change s.1.1.val ∈ (seedModulus seed s).factorization.support
  apply Finsupp.mem_support_iff.mpr
  rw [seedModulus_factorization hN hdiv hsmall]
  omega

lemma seedModulus_prime_le {N : ℕ} (hN : N ≠ 0) {seed : PrimeSlot N → ℕ}
    (hdiv : ∀ s, seed s ∣ N) (hsmall : SeedsSupportedBelow seed) (s : PrimeSlot N)
    {p : ℕ} (hp : p ∈ (seedModulus seed s).primeFactors) : p ≤ s.1.1.val := by
  have hpP := Nat.prime_of_mem_primeFactors hp
  have hpd := Nat.dvd_of_mem_primeFactors hp
  rcases hpP.dvd_mul.mp hpd with hpow | hseed
  · exact le_of_eq (Nat.prime_eq_prime_of_dvd_pow hpP
      (Nat.prime_of_mem_primeFactors s.1.1.2) hpow)
  · exact (hsmall s p (hpP.mem_primeFactors hseed
      (ne_zero_of_dvd_ne_zero hN (hdiv s)))).le

lemma primeCoordinate_ext {N : ℕ} {c d : PrimeCoordinate N}
    (hp : c.1.val = d.1.val) (he : c.2.val = d.2.val) : c = d := by
  rcases c with ⟨⟨p, hpN⟩, ⟨e, heN⟩⟩
  rcases d with ⟨⟨q, hqN⟩, ⟨f, hfN⟩⟩
  dsimp at hp he
  subst q
  subst f
  rfl

lemma seedModulus_injective {N : ℕ} (hN : N ≠ 0) {seed : PrimeSlot N → ℕ}
    (hdiv : ∀ s, seed s ∣ N) (hsmall : SeedsSupportedBelow seed)
    (hinj : ∀ c, Function.Injective (fun a => seed ⟨c, a⟩)) :
    Function.Injective (seedModulus seed) := by
  intro s t hst
  have hstp : s.1.1.val ≤ t.1.1.val := seedModulus_prime_le hN hdiv hsmall t
    (hst ▸ seedModulus_own_prime hN hdiv hsmall s)
  have htsp : t.1.1.val ≤ s.1.1.val := seedModulus_prime_le hN hdiv hsmall s
    (hst.symm ▸ seedModulus_own_prime hN hdiv hsmall t)
  have hp : s.1.1.val = t.1.1.val := le_antisymm hstp htsp
  have he : s.1.2.val = t.1.2.val := by
    have hh := congrArg (fun n => n.factorization s.1.1.val) hst
    rw [seedModulus_factorization hN hdiv hsmall s] at hh
    have hfp := congrArg (seedModulus seed t).factorization hp
    have hft := seedModulus_factorization hN hdiv hsmall t
    omega
  have hc : s.1 = t.1 := primeCoordinate_ext hp he
  rcases s with ⟨c, a⟩
  rcases t with ⟨d, b⟩
  dsimp at hc
  subst d
  have hs : seed ⟨c, a⟩ = seed ⟨c, b⟩ := Nat.eq_of_mul_eq_mul_left
    (pow_pos (Nat.prime_of_mem_primeFactors c.1.2).pos _) hst
  have hab := hinj c hs
  subst b
  rfl

def twoDigitRank {N : ℕ} (i : PrimeCoordinate N) : ℕ := 2 * i.1.val + i.2.val

lemma seedModulus_ordered {N : ℕ} (hN : N ≠ 0) {seed : PrimeSlot N → ℕ}
    (hdiv : ∀ s, seed s ∣ N) (hsmall : SeedsSupportedBelow seed)
    (hexp : ∀ p, N.factorization p ≤ 2) :
    ∀ s i, (i.2 : ℕ) < (seedModulus seed s).factorization i.1 →
      i = s.1 ∨ twoDigitRank i < twoDigitRank s.1 := by
  intro s i hi
  have hpMem : i.1.val ∈ (seedModulus seed s).factorization.support :=
    Finsupp.mem_support_iff.mpr (show (seedModulus seed s).factorization i.1.val ≠ 0 by omega)
  have hpLe := seedModulus_prime_le hN hdiv hsmall s hpMem
  by_cases hpEq : i.1.val = s.1.1.val
  · have hfp := congrArg (seedModulus seed s).factorization hpEq
    have hfs := seedModulus_factorization hN hdiv hsmall s
    have hi' : i.2.val < s.1.2.val + 1 := by omega
    by_cases heq : i.2.val = s.1.2.val
    · exact Or.inl (primeCoordinate_ext hpEq heq)
    · right
      dsimp [twoDigitRank]
      omega
  · right
    have hie := i.2.isLt
    have hib := hexp i.1.val
    dsimp [twoDigitRank]
    omega

end Erdos1189
