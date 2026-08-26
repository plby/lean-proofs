/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
The complete seed-divisor criterion for truncated-center frames.
Informal source: Sections 5 and 6 of Pickhardt and Omniscience Research Agent.
Formal author: OpenAI Codex.
-/

import ErdosProblems.Erdos1189.SeedModuli

namespace Erdos1189

open Finset

lemma prime_center_not_seedModulus {N P : ℕ} (hN : N ≠ 0) (hP : P.Prime)
    {seed : PrimeSlot N → ℕ} (hdiv : ∀ s, seed s ∣ N) (hsmall : SeedsSupportedBelow seed)
    (hterm : ∀ s, s.1.1.val = P → 1 < seed s) :
    P ∉ frameModuli (seedModulus seed) := by
  intro hmem
  obtain ⟨s, hs⟩ := mem_frameModuli.mp hmem
  have hsp := seedModulus_own_prime hN hdiv hsmall s
  rw [hs] at hsp
  have hp : s.1.1.val = P := by simpa only [hP.primeFactors, mem_singleton] using hsp
  have hlarge := hterm s hp
  have hpow : P ≤ s.1.1.val ^ (s.1.2.val + 1) := by
    have hbase := (Nat.prime_of_mem_primeFactors s.1.1.2).pos
    exact (le_of_eq hp.symm).trans
      (Nat.le_of_dvd (pow_pos hbase _) (dvd_pow_self _ (Nat.succ_ne_zero _)))
  change s.1.1.val ^ (s.1.2.val + 1) * seed s = P at hs
  have hp0 := hP.pos
  nlinarith

lemma terminal_seed_lcm {N P : ℕ} (hN : N ≠ 0) (hP : P.Prime) (hPN : P ∣ N)
    (hPexp : N.factorization P = 1) {seed : PrimeSlot N → ℕ}
    (hdiv : ∀ s, seed s ∣ N) (hsmall : SeedsSupportedBelow seed)
    (hinj : ∀ c, Function.Injective (fun a => seed ⟨c, a⟩))
    (hterm : ∀ p ∈ N.primeFactors, p ≠ P →
      ∃ s : PrimeSlot N, s.1.1.val = P ∧ p ^ N.factorization p ∣ seed s) :
    N ∣ (terminalTags (frameModuli (seedModulus seed))
      (frameAllocation (seedModulus seed)) P).lcm id := by
  let m := seedModulus seed
  let T := terminalTags (frameModuli m) (frameAllocation m) P
  have hm : Function.Injective m := seedModulus_injective hN hdiv hsmall hinj
  have hmem : ∀ s : PrimeSlot N, s.1.1.val = P → m s ∈ T := by
    intro s hs
    apply mem_filter.mpr
    refine ⟨mem_frameModuli.mpr ⟨s, rfl⟩, ?_⟩
    rw [frameAllocation_apply hm]
    exact hs
  have hTN : T.lcm id ∣ N := by
    apply Finset.lcm_dvd
    intro d hd
    obtain ⟨s, rfl⟩ := mem_frameModuli.mp (mem_filter.mp hd).1
    exact seedModulus_dvd hN hdiv hsmall s
  have hT0 : T.lcm id ≠ 0 := ne_zero_of_dvd_ne_zero hN hTN
  apply (Nat.factorization_le_iff_dvd hN hT0).mp
  intro p
  by_cases hp : p ∈ N.primeFactors
  · apply ((Nat.prime_of_mem_primeFactors hp).pow_dvd_iff_le_factorization hT0).mp
    by_cases hpP : p = P
    · subst p
      have hPmem : P ∈ N.primeFactors := hP.mem_primeFactors hPN hN
      let c : PrimeCoordinate N := ⟨⟨P, hPmem⟩, ⟨0, by rw [hPexp]; decide⟩⟩
      let s : PrimeSlot N := ⟨c, ⟨0, by
        change 0 < P - 1
        have := hP.two_le
        omega⟩⟩
      rw [hPexp, pow_one]
      have hd : P ∣ m s := Nat.dvd_of_mem_primeFactors (seedModulus_own_prime hN hdiv hsmall s)
      exact hd.trans (dvd_lcm (hmem s rfl))
    · obtain ⟨s, hsP, hs⟩ := hterm p hp hpP
      exact hs.trans ((dvd_mul_left _ _).trans (dvd_lcm (hmem s hsP)))
  · have hz : N.factorization p = 0 := Finsupp.notMem_support_iff.mp hp
    rw [hz]
    exact Nat.zero_le _

/-- With all finite seed conditions checked, the construction gives an
irreducible covering set with precisely `F(N)+1` distinct moduli. -/
theorem seed_frame {N P : ℕ} (hN : N ≠ 0) (hP : P.Prime) (hPN : P ∣ N)
    (hPexp : N.factorization P = 1) (hexp : ∀ p, N.factorization p ≤ 2)
    (seed : PrimeSlot N → ℕ) (hdiv : ∀ s, seed s ∣ N) (hsmall : SeedsSupportedBelow seed)
    (hinj : ∀ c, Function.Injective (fun a => seed ⟨c, a⟩))
    (hnonunit : ∀ s, s.1.1.val = P → 1 < seed s)
    (hterm : ∀ p ∈ N.primeFactors, p ≠ P →
      ∃ s : PrimeSlot N, s.1.1.val = P ∧ p ^ N.factorization p ∣ seed s) :
    IsIrreducibleCoveringSet (insert P (frameModuli (seedModulus seed))) ∧
      (insert P (frameModuli (seedModulus seed))).card = simpsonWeight N + 1 := by
  exact truncated_digit_frame hN hP.one_lt hPN (seedModulus seed) twoDigitRank
    (seedModulus_dvd hN hdiv hsmall) (seedModulus_injective hN hdiv hsmall hinj)
    (seedModulus_own seed) (prime_center_not_seedModulus hN hP hdiv hsmall hnonunit)
    hPexp (seedModulus_ordered hN hdiv hsmall hexp)
    (terminal_seed_lcm hN hP hPN hPexp hdiv hsmall hinj hterm)

end Erdos1189
