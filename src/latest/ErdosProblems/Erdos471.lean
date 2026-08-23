/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Original license: Apache 2.0. Note: This file has been modified. -/
/-
This is a Lean formalization of a solution to Erdős Problem 471.
https://www.erdosproblems.com/forum/thread/471

Informal authors:
- Luka Mrazović
- Vjekoslav Kovač
- Noga Alon

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos471.md
-/
/-
Copyright 2026 The Lean-Proofs Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import Mathlib
import Wikipedia.VinogradovsTheorem

/-!
# Erdős Problem 471

Starting from a finite set of primes, repeatedly adjoin every prime that is
the sum of three distinct elements already present.  This file formalizes the
exact closure operation and the reduction of the affirmative answer to the
distinct-summand form of Vinogradov's three-primes theorem.
-/

namespace Erdos471

/-- Three natural numbers are pairwise distinct. -/
def PairwiseDistinct3 (a b c : ℕ) : Prop :=
  a ≠ b ∧ a ≠ c ∧ b ≠ c

instance (a b c : ℕ) : Decidable (PairwiseDistinct3 a b c) := by
  unfold PairwiseDistinct3
  infer_instance

/-- The sums of ordered triples of distinct elements of `Q`.  Taking an image
removes the irrelevant ordering and any duplicate sums. -/
def tripleSums (Q : Finset ℕ) : Finset ℕ :=
  ((((Q ×ˢ Q) ×ˢ Q).filter fun t : (ℕ × ℕ) × ℕ ↦
      PairwiseDistinct3 t.1.1 t.1.2 t.2).image fun t ↦
        t.1.1 + t.1.2 + t.2)

/-- The prime-valued sums of three distinct elements of `Q`. -/
def newPrimes (Q : Finset ℕ) : Finset ℕ :=
  (tripleSums Q).filter Nat.Prime

/-- One exact step of the process in Erdős Problem 471. -/
def step (Q : Finset ℕ) : Finset ℕ :=
  Q ∪ newPrimes Q

/-- The generations of the closure process, starting at generation zero. -/
def generation (Q : Finset ℕ) : ℕ → Finset ℕ
  | 0 => Q
  | i + 1 => step (generation Q i)

/-- Every member of a finset is prime. -/
def IsPrimeFinset (Q : Finset ℕ) : Prop :=
  ∀ p ∈ Q, Nat.Prime p

/-- The cardinalities of the generations are unbounded. -/
def HasUnboundedGenerations (Q : Finset ℕ) : Prop :=
  ∀ k : ℕ, ∃ i : ℕ, k ≤ (generation Q i).card

/-- The exact distinct-summand consequence of Vinogradov's three-primes
theorem needed for Erdős Problem 471. -/
def DistinctTernaryGoldbachEventually : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N < n → Odd n →
    ∃ a b c : ℕ,
      Nat.Prime a ∧ Nat.Prime b ∧ Nat.Prime c ∧
        PairwiseDistinct3 a b c ∧ n = a + b + c

theorem mem_tripleSums {Q : Finset ℕ} {p : ℕ} :
    p ∈ tripleSums Q ↔
      ∃ a ∈ Q, ∃ b ∈ Q, ∃ c ∈ Q,
        PairwiseDistinct3 a b c ∧ p = a + b + c := by
  constructor
  · intro hp
    rcases Finset.mem_image.mp hp with ⟨⟨⟨a, b⟩, c⟩, habc, rfl⟩
    rcases Finset.mem_filter.mp habc with ⟨habcQ, hdistinct⟩
    rcases Finset.mem_product.mp habcQ with ⟨habQ, hcQ⟩
    rcases Finset.mem_product.mp habQ with ⟨haQ, hbQ⟩
    exact ⟨a, haQ, b, hbQ, c, hcQ, hdistinct, rfl⟩
  · rintro ⟨a, haQ, b, hbQ, c, hcQ, hdistinct, rfl⟩
    apply Finset.mem_image.mpr
    refine ⟨⟨⟨a, b⟩, c⟩, ?_, rfl⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr
        ⟨Finset.mem_product.mpr ⟨haQ, hbQ⟩, hcQ⟩, hdistinct⟩

theorem mem_newPrimes {Q : Finset ℕ} {p : ℕ} :
    p ∈ newPrimes Q ↔
      Nat.Prime p ∧
        ∃ a ∈ Q, ∃ b ∈ Q, ∃ c ∈ Q,
          PairwiseDistinct3 a b c ∧ p = a + b + c := by
  rw [newPrimes, Finset.mem_filter, mem_tripleSums]
  constructor
  · rintro ⟨hsum, hp⟩
    exact ⟨hp, hsum⟩
  · rintro ⟨hp, hsum⟩
    exact ⟨hsum, hp⟩

/-- Membership in a successor generation is exactly membership in the old
generation or being a prime sum of three distinct old elements. -/
theorem mem_step {Q : Finset ℕ} {p : ℕ} :
    p ∈ step Q ↔
      p ∈ Q ∨
        Nat.Prime p ∧
          ∃ a ∈ Q, ∃ b ∈ Q, ∃ c ∈ Q,
            PairwiseDistinct3 a b c ∧ p = a + b + c := by
  rw [step, Finset.mem_union, mem_newPrimes]

theorem subset_step (Q : Finset ℕ) : Q ⊆ step Q := by
  exact Finset.subset_union_left

theorem generation_subset_succ (Q : Finset ℕ) (i : ℕ) :
    generation Q i ⊆ generation Q (i + 1) := by
  simpa only [generation] using subset_step (generation Q i)

/-- Once an element occurs, it persists at every later generation. -/
theorem generation_mono (Q : Finset ℕ) {i j : ℕ} (hij : i ≤ j) :
    generation Q i ⊆ generation Q j := by
  induction j, hij using Nat.le_induction with
  | base => exact Finset.Subset.rfl
  | succ j _ ih => exact ih.trans (generation_subset_succ Q j)

theorem isPrimeFinset_step {Q : Finset ℕ} (hQ : IsPrimeFinset Q) :
    IsPrimeFinset (step Q) := by
  intro p hp
  rcases (mem_step.mp hp) with hpQ | hpnew
  · exact hQ p hpQ
  · exact hpnew.1

theorem isPrimeFinset_generation {Q : Finset ℕ} (hQ : IsPrimeFinset Q) :
    ∀ i : ℕ, IsPrimeFinset (generation Q i)
  | 0 => hQ
  | i + 1 => isPrimeFinset_step (isPrimeFinset_generation hQ i)

theorem isPrimeFinset_primesLE (N : ℕ) :
    IsPrimeFinset (Nat.primesLE N) := by
  intro p hp
  exact (Nat.mem_primesLE.mp hp).2

/-- Assuming the precise distinct Vinogradov input, a finite initial segment
of the primes eventually generates every prime. -/
theorem exists_primeFinset_all_primes_reachable
    (hV : DistinctTernaryGoldbachEventually) :
    ∃ Q : Finset ℕ,
      IsPrimeFinset Q ∧
        ∀ p : ℕ, Nat.Prime p → ∃ i : ℕ, p ∈ generation Q i := by
  rcases hV with ⟨NV, hV⟩
  let N := max NV 2
  let Q := Nat.primesLE N
  refine ⟨Q, isPrimeFinset_primesLE N, ?_⟩
  intro p hp
  induction p using Nat.strong_induction_on with
  | h p ih =>
      by_cases hpN : p ≤ N
      · refine ⟨0, ?_⟩
        exact Nat.mem_primesLE.mpr ⟨hpN, hp⟩
      · have hNp : N < p := Nat.lt_of_not_ge hpN
        have hNVp : NV < p := lt_of_le_of_lt (le_max_left NV 2) hNp
        have hp_ne_two : p ≠ 2 := by omega
        have hp_odd : Odd p := hp.odd_of_ne_two hp_ne_two
        rcases hV p hNVp hp_odd with
          ⟨a, b, c, ha, hb, hc, hdistinct, hp_sum⟩
        have ha_lt : a < p := by
          have hbpos := hb.pos
          have hcpos := hc.pos
          omega
        have hb_lt : b < p := by
          have hapos := ha.pos
          have hcpos := hc.pos
          omega
        have hc_lt : c < p := by
          have hapos := ha.pos
          have hbpos := hb.pos
          omega
        obtain ⟨ia, hia⟩ := ih a ha_lt ha
        obtain ⟨ib, hib⟩ := ih b hb_lt hb
        obtain ⟨ic, hic⟩ := ih c hc_lt hc
        let j := max ia (max ib ic)
        have hia' : a ∈ generation Q j :=
          generation_mono Q (le_max_left ia (max ib ic)) hia
        have hib' : b ∈ generation Q j :=
          generation_mono Q ((le_max_left ib ic).trans (le_max_right ia (max ib ic))) hib
        have hic' : c ∈ generation Q j :=
          generation_mono Q ((le_max_right ib ic).trans (le_max_right ia (max ib ic))) hic
        refine ⟨j + 1, ?_⟩
        rw [generation]
        apply mem_step.mpr
        exact Or.inr ⟨hp, a, hia', b, hib', c, hic', hdistinct, hp_sum⟩

/-- A finite collection of individually reachable numbers can be synchronized
at one generation. -/
theorem finite_subset_eventually_mem {Q F : Finset ℕ}
    (hreach : ∀ p ∈ F, ∃ i : ℕ, p ∈ generation Q i) :
    ∃ j : ℕ, F ⊆ generation Q j := by
  induction F using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert p F hp ih =>
      obtain ⟨i, hi⟩ := hreach p (by simp)
      obtain ⟨j, hj⟩ := ih (fun q hq ↦ hreach q (Finset.mem_insert_of_mem hq))
      refine ⟨max i j, ?_⟩
      intro q hq
      rw [Finset.mem_insert] at hq
      rcases hq with rfl | hq
      · exact generation_mono Q (le_max_left i j) hi
      · exact generation_mono Q (le_max_right i j) (hj hq)

/-- The complete elementary reduction from distinct ternary Vinogradov to
the affirmative answer to Erdős Problem 471. -/
theorem erdos471_of_distinctTernaryGoldbachEventually
    (hV : DistinctTernaryGoldbachEventually) :
    ∃ Q : Finset ℕ, IsPrimeFinset Q ∧ HasUnboundedGenerations Q := by
  classical
  obtain ⟨Q, hQprime, hreach⟩ :=
    exists_primeFinset_all_primes_reachable hV
  refine ⟨Q, hQprime, ?_⟩
  intro k
  obtain ⟨F, hFprime, hFcard⟩ :=
    Nat.infinite_setOfPred_prime.exists_subset_card_eq k
  obtain ⟨j, hFj⟩ := finite_subset_eventually_mem (Q := Q) (F := F) (by
    intro p hp
    exact hreach p (hFprime hp))
  refine ⟨j, ?_⟩
  simpa [hFcard] using Finset.card_le_card hFj

/-- Vinogradov's theorem supplies the distinct-prime representation required
by the closure process. -/
theorem distinctTernaryGoldbachEventually : DistinctTernaryGoldbachEventually := by
  obtain ⟨N, hN⟩ := VinogradovsTheorem.vinogradovs_theorem
  refine ⟨N, ?_⟩
  intro n hn hodd
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc, hsum⟩ := hN n hn hodd
  exact ⟨a, b, c, ha, hb, hc, ⟨hab, hac, hbc⟩, hsum⟩

/-- Erdős Problem 471 has an affirmative answer: a finite set of primes can
be chosen whose generations have arbitrarily large cardinality. -/
theorem erdos471 :
    ∃ Q : Finset ℕ, IsPrimeFinset Q ∧ HasUnboundedGenerations Q :=
  erdos471_of_distinctTernaryGoldbachEventually
    distinctTernaryGoldbachEventually

#print axioms erdos471

end Erdos471
