/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, ChatGPT
-/

import Mathlib

/-!
# A cofinal sequence of prime moduli

This file collects the elementary interface for restricting assertions on
natural numbers to a canonical sequence of prime moduli.  We use Mathlib's
`n`th prime.  Its strict monotonicity makes the sequence cofinal, so every
eventual assertion at `Filter.atTop` remains eventual after restriction to
this sequence.
-/

open Filter

namespace Erdos543.PrimeSequence

/-- The canonical growing sequence of prime moduli. -/
noncomputable def primeSeq (n : ℕ) : ℕ := Nat.nth Nat.Prime n

lemma primeSeq_prime (n : ℕ) : Nat.Prime (primeSeq n) := by
  exact Nat.prime_nth_prime n

lemma primeSeq_two_le (n : ℕ) : 2 ≤ primeSeq n :=
  (primeSeq_prime n).two_le

lemma primeSeq_one_lt (n : ℕ) : 1 < primeSeq n :=
  (primeSeq_prime n).one_lt

lemma primeSeq_pos (n : ℕ) : 0 < primeSeq n :=
  (primeSeq_prime n).pos

lemma primeSeq_ne_zero (n : ℕ) : primeSeq n ≠ 0 :=
  (primeSeq_pos n).ne'

instance primeSeqNeZero (n : ℕ) : NeZero (primeSeq n) :=
  ⟨primeSeq_ne_zero n⟩

instance primeSeqFactPrime (n : ℕ) : Fact (Nat.Prime (primeSeq n)) :=
  ⟨primeSeq_prime n⟩

lemma primeSeq_strictMono : StrictMono primeSeq := by
  exact Nat.nth_strictMono Nat.infinite_setOfPred_prime

lemma primeSeq_mono : Monotone primeSeq :=
  primeSeq_strictMono.monotone

/-- A simple quantitative lower bound for the `n`th prime. -/
lemma add_two_le_primeSeq (n : ℕ) : n + 2 ≤ primeSeq n := by
  induction n with
  | zero => simpa using primeSeq_two_le 0
  | succ n ih =>
      exact Nat.succ_le_of_lt (ih.trans_lt (primeSeq_strictMono (Nat.lt_succ_self n)))

lemma self_le_primeSeq (n : ℕ) : n ≤ primeSeq n :=
  le_trans (Nat.le_add_right n 2) (add_two_le_primeSeq n)

/-- The prime sequence is cofinal in the natural numbers. -/
lemma tendsto_primeSeq_atTop : Tendsto primeSeq atTop atTop :=
  primeSeq_strictMono.tendsto_atTop

/-- Pull an arbitrary eventual assertion back to the prime sequence. -/
lemma eventually_primeSeq {P : ℕ → Prop} (hP : ∀ᶠ n in atTop, P n) :
    ∀ᶠ i in atTop, P (primeSeq i) :=
  tendsto_primeSeq_atTop.eventually hP

/-- Restrict an arbitrary limit along natural numbers to the prime sequence. -/
lemma tendsto_comp_primeSeq {α : Type*} {l : Filter α} {f : ℕ → α}
    (hf : Tendsto f atTop l) :
    Tendsto (fun i ↦ f (primeSeq i)) atTop l :=
  hf.comp tendsto_primeSeq_atTop

/-- Restrict a little-oh estimate along natural numbers to prime moduli. -/
lemma isLittleO_comp_primeSeq {𝕜 E F : Type*}
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E] [NormedSpace 𝕜 F]
    {f : ℕ → E} {g : ℕ → F} (hfg : f =o[atTop] g) :
    (fun i ↦ f (primeSeq i)) =o[atTop] (fun i ↦ g (primeSeq i)) :=
  hfg.comp_tendsto tendsto_primeSeq_atTop

/-- There is a prime at least as large as every prescribed threshold. -/
lemma exists_prime_ge (N : ℕ) : ∃ p : ℕ, N ≤ p ∧ Nat.Prime p :=
  Nat.exists_infinite_primes N

/-- There is a prime strictly larger than every prescribed threshold. -/
lemma exists_prime_gt (N : ℕ) : ∃ p : ℕ, N < p ∧ Nat.Prime p := by
  obtain ⟨p, hpN, hp⟩ := Nat.exists_infinite_primes (N + 1)
  exact ⟨p, lt_of_lt_of_le (Nat.lt_succ_self N) hpN, hp⟩

/-- An eventual property of natural numbers is realized by an arbitrarily
large prime. -/
lemma exists_large_prime_of_eventually {P : ℕ → Prop}
    (hP : ∀ᶠ n in atTop, P n) (N : ℕ) :
    ∃ p : ℕ, N ≤ p ∧ Nat.Prime p ∧ P p := by
  obtain ⟨M, hM⟩ := (eventually_atTop.1 hP)
  obtain ⟨p, hp, hprime⟩ := Nat.exists_infinite_primes (max N M)
  exact ⟨p, (le_max_left N M).trans hp, hprime,
    hM p ((le_max_right N M).trans hp)⟩

lemma card_zmod_primeSeq (n : ℕ) :
    Fintype.card (ZMod (primeSeq n)) = primeSeq n := by
  exact ZMod.card (primeSeq n)

lemma log_primeSeq_pos (n : ℕ) :
    0 < Real.log (primeSeq n : ℝ) :=
  (primeSeq_prime n).log_pos

lemma log_primeSeq_ne_zero (n : ℕ) :
    Real.log (primeSeq n : ℝ) ≠ 0 :=
  (log_primeSeq_pos n).ne'

/-- The real-valued prime sequence tends to infinity. -/
lemma tendsto_primeSeq_cast_atTop :
    Tendsto (fun n ↦ (primeSeq n : ℝ)) atTop atTop :=
  tendsto_natCast_atTop_atTop.comp tendsto_primeSeq_atTop

/-- The logarithm of the prime sequence tends to infinity. -/
lemma tendsto_log_primeSeq_atTop :
    Tendsto (fun n ↦ Real.log (primeSeq n : ℝ)) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_primeSeq_cast_atTop

/-- The iterated logarithm of the prime sequence tends to infinity. -/
lemma tendsto_log_log_primeSeq_atTop :
    Tendsto (fun n ↦ Real.log (Real.log (primeSeq n : ℝ))) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_log_primeSeq_atTop

lemma eventually_log_log_primeSeq_pos :
    ∀ᶠ n : ℕ in atTop, 0 < Real.log (Real.log (primeSeq n : ℝ)) :=
  tendsto_log_log_primeSeq_atTop.eventually (eventually_gt_atTop 0)

/-- A pointwise lower bound useful for transferring estimates indexed by
the sequence number to estimates indexed by the prime itself. -/
lemma log_natCast_le_log_primeSeq (n : ℕ) :
    Real.log (n : ℝ) ≤ Real.log (primeSeq n : ℝ) := by
  by_cases hn : n = 0
  · subst n
    simpa using (log_primeSeq_pos 0).le
  · exact Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hn)
      (by exact_mod_cast self_le_primeSeq n)

lemma log_add_two_le_log_primeSeq (n : ℕ) :
    Real.log (n + 2 : ℝ) ≤ Real.log (primeSeq n : ℝ) := by
  exact Real.log_le_log (by positivity)
    (by exact_mod_cast add_two_le_primeSeq n)

/-- The literal `o(log log N)` ratio remains convergent to zero after
restriction to the prime sequence. -/
lemma tendsto_logLog_ratio_comp_primeSeq (g : ℕ → ℝ)
    (hg : Tendsto (fun N ↦ g N / Real.log (Real.log (N : ℝ))) atTop (nhds 0)) :
    Tendsto
      (fun n ↦ g (primeSeq n) /
        Real.log (Real.log (primeSeq n : ℝ)))
      atTop (nhds 0) :=
  hg.comp tendsto_primeSeq_atTop

end Erdos543.PrimeSequence
