/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Small-prime exceptions in the squarefree seed supply.
Informal source: the products of subsets of preceding primes and Bertrand's postulate,
as used in Section 6.3 of Pickhardt and Omniscience Research Agent.
Formal author: OpenAI Codex.
-/

import ErdosProblems.Erdos1189.SmallSeeds

namespace Erdos1189

open Finset Filter

lemma squarefree_prod_primes {D : Finset ℕ} (hD : ∀ p ∈ D, p.Prime) :
    Squarefree (∏ p ∈ D, p) := by
  induction D using Finset.induction with
  | empty => simp
  | @insert p D hp ih =>
      have hpP : p.Prime := hD p (mem_insert_self _ _)
      have hDP : ∀ q ∈ D, q.Prime := fun q hq => hD q (mem_insert_of_mem hq)
      rw [prod_insert hp, Nat.squarefree_mul_iff]
      refine ⟨?_, hpP.squarefree, ih hDP⟩
      apply Nat.Coprime.prod_right
      intro q hq
      exact (Nat.coprime_primes hpP (hDP q hq)).mpr (fun heq => hp (heq ▸ hq))

lemma prime_products_injective {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) :
    Set.InjOn (fun D : Finset ℕ => ∏ p ∈ D, p) S.powerset := by
  intro D hD E hE heq
  have hDP := fun p hp => hS p (mem_powerset.mp hD hp)
  have hEP := fun p hp => hS p (mem_powerset.mp hE hp)
  simpa only [Nat.primeFactors_prod hDP, Nat.primeFactors_prod hEP] using
    congrArg Nat.primeFactors heq

lemma many_seeds_at_primeAt (s : ℕ) :
    primeAt s - 1 ≤
      (smallSquarefreeSeeds (primeAt s) (∏ p ∈ Nat.primesLE (primeAt s - 1), p)).card := by
  let S := Nat.primesLE (primeAt s - 1)
  have hSP : ∀ p ∈ S, p.Prime := fun p hp => Nat.prime_of_mem_primesLE hp
  have hpos : 0 < ∏ p ∈ S, p := prod_pos fun p hp => (hSP p hp).pos
  have hsub : S.powerset.image (fun D : Finset ℕ => ∏ p ∈ D, p) ⊆
      smallSquarefreeSeeds (primeAt s) (∏ p ∈ S, p) := by
    intro d hd
    obtain ⟨D, hD, rfl⟩ := mem_image.mp hd
    have hDS : D ⊆ S := mem_powerset.mp hD
    have hDP : ∀ p ∈ D, p.Prime := fun p hp => hSP p (hDS hp)
    have hDPpos : 0 < ∏ p ∈ D, p := prod_pos fun p hp => (hDP p hp).pos
    have hle : (∏ p ∈ D, p) ≤ ∏ p ∈ S, p :=
      Nat.le_of_dvd hpos (prod_dvd_prod_of_subset _ _ _ hDS)
    refine mem_filter.mpr ⟨mem_filter.mpr
      ⟨mem_Ioc.mpr ⟨hDPpos, hle⟩, squarefree_prod_primes hDP⟩, ?_⟩
    rw [Nat.primeFactors_prod hDP]
    intro p hp
    have hh := Nat.le_of_mem_primesLE (hDS hp)
    have hp0 := (primeAt_prime s).pos
    omega
  have hScard : S.card = s := by
    rw [Nat.primesLE_card_eq_primeCounting, Nat.primeCounting_sub_one]
    exact Nat.primeCounting'_nth_eq s
  calc
    primeAt s - 1 ≤ 2 ^ s := primeAt_sub_one_le_two_pow s
    _ = (S.powerset.image (fun D : Finset ℕ => ∏ p ∈ D, p)).card := by
      rw [card_image_of_injOn (prime_products_injective hSP), card_powerset, hScard]
    _ ≤ (smallSquarefreeSeeds (primeAt s) (∏ p ∈ S, p)).card := card_le_card hsub

lemma smallSquarefreeSeeds_mono (q : ℕ) {N M : ℕ} (hNM : N ≤ M) :
    smallSquarefreeSeeds q N ⊆ smallSquarefreeSeeds q M := by
  intro d hd
  obtain ⟨hdSF, hdsmall⟩ := mem_filter.mp hd
  obtain ⟨hdI, hdSF⟩ := mem_filter.mp hdSF
  obtain ⟨hd0, hdN⟩ := mem_Ioc.mp hdI
  exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_Ioc.mpr ⟨hd0, hdN.trans hNM⟩, hdSF⟩, hdsmall⟩

/-- One absolute linear seed-size bound works for every prime, including the exceptions. -/
theorem exists_uniform_seed_constant :
    ∃ C : ℕ, 0 < C ∧ ∀ q : ℕ, q.Prime →
      q - 1 ≤ (smallSquarefreeSeeds q (C * q)).card := by
  obtain ⟨Q, hQ⟩ := eventually_atTop.mp eventually_small_squarefree_seeds
  let R := ∏ p ∈ Nat.primesLE Q, p
  let C := max 16 R
  have hC : 0 < C := lt_of_lt_of_le (by decide : 0 < 16) (le_max_left _ _)
  refine ⟨C, hC, ?_⟩
  intro q hq
  by_cases hqQ : Q ≤ q
  · have hqC : 16 * q ≤ C * q := Nat.mul_le_mul_right q (le_max_left _ _)
    exact (show q - 1 ≤ 3 * q by omega).trans ((hQ q hqQ).trans
      (card_le_card (smallSquarefreeSeeds_mono q hqC)))
  · obtain ⟨s, _, hs⟩ := Nat.exists_lt_card_nth_eq hq
    have hs' : primeAt s = q := hs
    have hsmall := many_seeds_at_primeAt s
    rw [hs'] at hsmall
    apply hsmall.trans (card_le_card (smallSquarefreeSeeds_mono q ?_))
    have hsub : Nat.primesLE (q - 1) ⊆ Nat.primesLE Q := by
      intro p hp
      exact Nat.mem_primesLE.mpr ⟨(Nat.le_of_mem_primesLE hp).trans (by omega),
        Nat.prime_of_mem_primesLE hp⟩
    have hRpos : 0 < R := prod_pos fun p hp => (Nat.prime_of_mem_primesLE hp).pos
    have hR : (∏ p ∈ Nat.primesLE (q - 1), p) ≤ R :=
      Nat.le_of_dvd hRpos (prod_dvd_prod_of_subset _ _ _ hsub)
    exact hR.trans ((le_max_right 16 R).trans (Nat.le_mul_of_pos_right C hq.pos))

end Erdos1189
