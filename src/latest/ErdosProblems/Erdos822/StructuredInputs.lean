/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import ErdosProblems.Erdos822.Core

/-!
# The outer prime layer in the GIL construction

For a finite set `B x` of cofactors, the paper forms inputs `n = m * p`
with `p` prime and `x / (2m) < p ≤ x / m`.  The difficult analytic work is
to choose `B`; this file formalizes the exact finite outer layer and its
elementary bounds.
-/

namespace Erdos822

open scoped BigOperators Finset

/-- Primes in the paper's half-open interval `(x / (2m), x / m]`. -/
def outerPrimes (x m : ℕ) : Finset ℕ :=
  (Finset.Ioc (x / (2 * m)) (x / m)).filter Nat.Prime

/-- The outer layer obtained by adjoining one prime to each cofactor in
`B x`. -/
def outerInputs (B : ℕ → Finset ℕ) (x : ℕ) : Finset ℕ :=
  (B x).biUnion fun m ↦ (outerPrimes x m).image fun p ↦ m * p

@[simp]
theorem mem_outerPrimes_iff {x m p : ℕ} :
    p ∈ outerPrimes x m ↔
      x / (2 * m) < p ∧ p ≤ x / m ∧ p.Prime := by
  simp [outerPrimes, and_assoc]

theorem mem_outerInputs_iff {B : ℕ → Finset ℕ} {x n : ℕ} :
    n ∈ outerInputs B x ↔
      ∃ m ∈ B x, ∃ p ∈ outerPrimes x m, m * p = n := by
  simp [outerInputs]

/-- Every input in the outer layer is at most the scale `x`. -/
theorem outerInputs_bounded (B : ℕ → Finset ℕ) (x : ℕ) :
    ∀ n ∈ outerInputs B x, n ≤ x := by
  intro n hn
  rw [mem_outerInputs_iff] at hn
  obtain ⟨m, _, p, hp, rfl⟩ := hn
  have hp_le : p ≤ x / m := (mem_outerPrimes_iff.mp hp).2.1
  by_cases hm : m = 0
  · simp [hm]
  have hmpos : 0 < m := Nat.pos_of_ne_zero hm
  have hmul : p * m ≤ x := (Nat.le_div_iff_mul_le hmpos).mp hp_le
  simpa [Nat.mul_comm] using hmul

/-- If the outer prime is larger than the cofactor, it is a genuinely new
prime factor.  This is the elementary hypothesis needed to use
`shiftedTotient_mul_prime`. -/
theorem not_dvd_of_mem_outerPrimes_of_lt {x m p : ℕ}
    (hp : p ∈ outerPrimes x m) (hmpos : 0 < m) (hmp : m < p) : ¬ p ∣ m := by
  intro hdiv
  have hpprime : p.Prime := (mem_outerPrimes_iff.mp hp).2.2
  have hpm : p ≤ m := Nat.le_of_dvd hmpos hdiv
  exact (not_le_of_gt hmp) hpm

/-- On the new-prime part of the outer layer the shifted totient is the
linear form used in equation (5.2) of GIL. -/
theorem shiftedTotient_outer_linear {x m p : ℕ}
    (hp : p ∈ outerPrimes x m) (hmpos : 0 < m) (hmp : m < p) :
    shiftedTotient (m * p) =
      (m + Nat.totient m) * p - Nat.totient m := by
  exact shiftedTotient_mul_prime (mem_outerPrimes_iff.mp hp).2.2
    (not_dvd_of_mem_outerPrimes_of_lt hp hmpos hmp)

/-- A product with a prime factor larger than its cofactor has a unique
such presentation.  This is the finite arithmetic form of the paper's
statement that the outer prime is the largest prime factor of `n`. -/
theorem eq_of_mul_eq_mul_of_large_primes {m m' p p' : ℕ}
    (hp : p.Prime) (hp' : p'.Prime)
    (hmpos : 0 < m) (hm'pos : 0 < m')
    (hmp : m < p) (hm'p' : m' < p')
    (hprod : m * p = m' * p') :
    m = m' ∧ p = p' := by
  have hp_pos : 0 < p := hp.pos
  have hp'_pos : 0 < p' := hp'.pos
  by_cases hpp : p = p'
  · subst p'
    constructor
    · exact Nat.eq_of_mul_eq_mul_right hp_pos hprod
    · rfl
  have horder : p < p' ∨ p' < p := lt_or_gt_of_ne hpp
  exfalso
  rcases horder with hlt | hlt
  · have hdiv : p' ∣ m * p := by
      refine ⟨m', ?_⟩
      simpa [Nat.mul_comm] using hprod
    rcases hp'.dvd_mul.mp hdiv with hpm | hppdiv
    · have hp'm : p' ≤ m := Nat.le_of_dvd hmpos hpm
      omega
    · have hp'p : p' ≤ p := Nat.le_of_dvd hp_pos hppdiv
      omega
  · have hdiv : p ∣ m' * p' := by
      refine ⟨m, ?_⟩
      simpa [Nat.mul_comm] using hprod.symm
    rcases hp.dvd_mul.mp hdiv with hpm | hppdiv
    · have hpm' : p ≤ m' := Nat.le_of_dvd hm'pos hpm
      omega
    · have hpp' : p ≤ p' := Nat.le_of_dvd hp'_pos hppdiv
      omega

/-- When every outer prime is larger than its cofactor, the outer products
are collision-free already before applying `shiftedTotient`.  Hence the
cardinality of the outer layer is exactly the sum of the prime-interval
cardinalities. -/
theorem outerInputs_card_eq_sum_outerPrimes_card
    (B : ℕ → Finset ℕ) (x : ℕ)
    (hpos : ∀ m ∈ B x, 0 < m)
    (hlarge : ∀ m ∈ B x, ∀ p ∈ outerPrimes x m, m < p) :
    (outerInputs B x).card =
      ∑ m ∈ B x, (outerPrimes x m).card := by
  classical
  let pairs : Finset (Sigma fun _ : ℕ => ℕ) :=
    (B x).sigma fun m => outerPrimes x m
  let prod : Sigma (fun _ : ℕ => ℕ) → ℕ := fun mp => mp.1 * mp.2
  have hrepr : outerInputs B x = pairs.image prod := by
    ext n
    simp [outerInputs, pairs, prod]
    grind
  have hinj : Set.InjOn prod pairs := by
    intro a ha b hb hab
    rcases a with ⟨m, p⟩
    rcases b with ⟨m', p'⟩
    have ha' : m ∈ B x ∧ p ∈ outerPrimes x m := by
      simpa [pairs] using ha
    have hb' : m' ∈ B x ∧ p' ∈ outerPrimes x m' := by
      simpa [pairs] using hb
    have hab' : m * p = m' * p' := by
      simpa [prod] using hab
    have hp : p.Prime := (mem_outerPrimes_iff.mp ha'.2).2.2
    have hp' : p'.Prime := (mem_outerPrimes_iff.mp hb'.2).2.2
    have huniq := eq_of_mul_eq_mul_of_large_primes hp hp'
      (hpos m ha'.1) (hpos m' hb'.1)
      (hlarge m ha'.1 p ha'.2) (hlarge m' hb'.1 p' hb'.2) hab'
    rcases huniq with ⟨rfl, rfl⟩
    rfl
  rw [hrepr, Finset.card_image_of_injOn hinj]
  exact Finset.card_sigma (B x) (fun m => outerPrimes x m)

end Erdos822
