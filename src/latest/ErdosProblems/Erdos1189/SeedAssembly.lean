/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Assembling the bounded seed lists for the exact-cardinality frame.
Informal source: Sections 6 and 7 of Pickhardt and Omniscience Research Agent.
Formal author: OpenAI Codex.
-/

import ErdosProblems.Erdos1189.SeedSelection
import ErdosProblems.Erdos1189.SeedFrame

namespace Erdos1189

open Finset

structure SeedFamily (N P B C : ℕ) where
  seed : PrimeSlot N → ℕ
  divisor : ∀ s, seed s ∣ N
  supported : SeedsSupportedBelow seed
  injective : ∀ c, Function.Injective (fun a => seed ⟨c, a⟩)
  terminal_nonunit : ∀ s, s.1.1.val = P → 1 < seed s
  terminal_power : ∀ p ∈ N.primeFactors, p ≠ P →
    ∃ s : PrimeSlot N, s.1.1.val = P ∧ p ^ N.factorization p ∣ seed s
  ordinary_bound : ∀ s, s.1.1.val ≠ P → seed s ≤ C * s.1.1.val
  terminal_bound : ∀ s, s.1.1.val = P → seed s ≤ max (16 * P) (B ^ 2)
  small_squarefree : ∀ q, q.Prime → q < P → ∀ d ∈ squarefreeUpto (q - 1),
    ∃ s : PrimeSlot N, s.1.1.val = q ∧ s.1.2.val = 0 ∧ seed s = d

theorem exists_frame_seed_family {P B C : ℕ} {D : Finset ℕ} (hP : P.Prime)
    (hB : B < P) (hD : D ⊆ Nat.primesLE B) (hC : 0 < C)
    (hcount : ∀ q : ℕ, q.Prime → q - 1 ≤ (smallSquarefreeSeeds q (C * q)).card)
    (hstock : 3 * P ≤ (smallSquarefreeSeeds P (16 * P)).card) :
    Nonempty (SeedFamily (frameInteger P D) P B C) := by
  classical
  let N := frameInteger P D
  have hDP : D ⊆ Nat.primesLE P := fun q hq => Nat.mem_primesLE.mpr
    ⟨(Nat.le_of_mem_primesLE (hD hq)).trans hB.le, Nat.prime_of_mem_primesLE (hD hq)⟩
  have hNpf : N.primeFactors = Nat.primesLE P := frameInteger_primeFactors hDP
  have hPexp : N.factorization P = 1 := frameInteger_terminal_exponent hP hB hD
  have hFex : ∀ q : ℕ, ∃ f : Fin (q - 1) → ℕ, q.Prime →
      Function.Injective f ∧ (∀ i, f i ∈ smallSquarefreeSeeds q (C * q)) ∧
        ∀ d ∈ squarefreeUpto (q - 1), ∃ i, f i = d := by
    intro q
    by_cases hq : q.Prime
    · obtain ⟨f, hf⟩ := exists_small_seed_list hC (hcount q hq)
      exact ⟨f, fun _ => hf⟩
    · exact ⟨fun _ => 1, fun h => (hq h).elim⟩
  choose F hF using hFex
  obtain ⟨T, hTinj, hT, hTpres⟩ := exists_terminal_seed_list hP hB hD hstock
  let G : (q : ℕ) → Fin (q - 1) → ℕ := Function.update F P T
  have hGP : G P = T := by simp [G]
  have hGne : ∀ q, q ≠ P → G q = F q := by intro q hq; simp [G, hq]
  have hGinj : ∀ q, q.Prime → Function.Injective (G q) := by
    intro q hq
    by_cases hqP : q = P
    · subst q
      rw [hGP]
      exact hTinj
    · rw [hGne q hqP]
      exact (hF q hq).1
  have hG : ∀ q, q.Prime → q ≤ P → ∀ a : Fin (q - 1),
      G q a ∣ N ∧ (∀ p ∈ (G q a).primeFactors, p < q) ∧
        (q = P → 1 < G q a) ∧ (q ≠ P → G q a ≤ C * q) ∧
        (q = P → G q a ≤ max (16 * P) (B ^ 2)) := by
    intro q hq hqle a
    by_cases hqP : q = P
    · subst q
      rw [hGP]
      have ht := hT a
      exact ⟨ht.2.2.1, ht.2.2.2, fun _ => ht.1, fun h => (h rfl).elim, fun _ => ht.2.1⟩
    · rw [hGne q hqP]
      obtain ⟨hfa, hsmall⟩ := mem_filter.mp ((hF q hq).2.1 a)
      obtain ⟨hfaI, hfaSF⟩ := mem_filter.mp hfa
      exact ⟨squarefree_seed_dvd_frameInteger hDP hfaSF
        (fun p hp => (hsmall p hp).le.trans hqle), hsmall,
        fun h => (hqP h).elim, fun _ => (mem_Ioc.mp hfaI).2, fun h => (hqP h).elim⟩
  let seed : PrimeSlot N → ℕ := fun s => G s.1.1.val s.2
  have hc : ∀ c : PrimeCoordinate N, c.1.val.Prime ∧ c.1.val ≤ P := by
    intro c
    have hp : c.1.val ∈ Nat.primesLE P :=
      Eq.mp (congrArg (fun S : Finset ℕ => c.1.val ∈ S) hNpf) c.1.2
    exact ⟨Nat.prime_of_mem_primesLE hp, Nat.le_of_mem_primesLE hp⟩
  refine ⟨⟨seed, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro s
    exact (hG _ (hc s.1).1 (hc s.1).2 s.2).1
  · intro s p hp
    exact (hG _ (hc s.1).1 (hc s.1).2 s.2).2.1 p hp
  · intro c
    exact hGinj _ (hc c).1
  · intro s hs
    exact (hG _ (hc s.1).1 (hc s.1).2 s.2).2.2.1 hs
  · intro p hp hpP
    have hp' : p ∈ Nat.primesLE P := hNpf ▸ hp
    obtain ⟨a, ha⟩ := hTpres p hp' hpP
    have hPmem : P ∈ N.primeFactors := hNpf ▸ Nat.mem_primesLE.mpr ⟨le_rfl, hP⟩
    let c : PrimeCoordinate N := ⟨⟨P, hPmem⟩, ⟨0, by rw [hPexp]; decide⟩⟩
    refine ⟨⟨c, a⟩, rfl, ?_⟩
    change p ^ N.factorization p ∣ G P a
    rw [hGP, ha]
  · intro s hs
    exact (hG _ (hc s.1).1 (hc s.1).2 s.2).2.2.2.1 hs
  · intro s hs
    exact (hG _ (hc s.1).1 (hc s.1).2 s.2).2.2.2.2 hs
  · intro q hq hqP d hd
    obtain ⟨a, ha⟩ := (hF q hq).2.2 d hd
    have hqmem : q ∈ N.primeFactors := hNpf ▸ Nat.mem_primesLE.mpr ⟨hqP.le, hq⟩
    have hqe : 0 < N.factorization q := by
      exact Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hqmem)
    let c : PrimeCoordinate N := ⟨⟨q, hqmem⟩, ⟨0, hqe⟩⟩
    refine ⟨⟨c, a⟩, rfl, rfl, ?_⟩
    change G q a = d
    rw [hGne q hqP.ne, ha]

end Erdos1189
