/-

This is a Lean solution to a MISFORMALIZATION of Erdős Problem 56.
https://www.erdosproblems.com/56

The statement is from the Formal Conjectures project at
https://github.com/google-deepmind/formal-conjectures/blob/f33f5ddb49f6077e34025917965bcd1bbd920d73/FormalConjectures/ErdosProblems/56.lean#L109-L117

The (dis)proof was found by Aristotle from Harmonic.

The issue is that the condition N ≥ p_k was missing (from both the
human statement and the formalization).

The proof is verified by Lean.  The following version numbers were
used:

Lean Toolchain version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7 (v4.24.0)

-/

import Mathlib

namespace Erdos56x

/--
Say a set of natural numbers is `k`-weakly divisible if any `k+1` elements
of `A` are not relatively prime.
-/
def WeaklyDivisible (k : ℕ) (A : Finset ℕ) : Prop :=
    ∀ s ∈ A.powersetCard (k + 1), ¬ Set.Pairwise s Nat.Coprime

/--
`MaxWeaklyDivisible N k` is the size of the largest k-weakly divisible subset of `{1,..., N}`
-/
noncomputable def MaxWeaklyDivisible (N k : ℕ) : ℕ :=
  sSup { n : ℕ |
    ∃ A : Finset ℕ,
      A ⊆ Finset.Icc 1 N ∧
      WeaklyDivisible k A ∧
      A.card = n }

/--
`FirstPrimesMultiples N k` is the set of numbers in `{1,..., N}` that are
a multiple of one of the first `k` primes.
-/
noncomputable def FirstPrimesMultiples (N k : ℕ) : Finset ℕ :=
    (Finset.Icc 1 N).filter fun i => ∃ j < k, (j.nth Nat.Prime ∣ i)

/--
Suppose $A \subseteq \{1,\dots,N\}$ is such that there are no $k+1$ elements of $A$ which are
relatively prime. An example is the set of all multiples of the first $k$ primes.
Is this the largest such set?
-/
theorem misformalized_erdos_56 : (∀ᵉ (N ≥ 2) (k > 0), (MaxWeaklyDivisible N k = (FirstPrimesMultiples N k).card)) ↔
    False := by
  bound;
  · contrapose! a;
    refine' ⟨ 2, by norm_num, 2, by norm_num, _ ⟩;
    unfold MaxWeaklyDivisible FirstPrimesMultiples;
    refine' ne_of_gt ( lt_of_lt_of_le _ <| le_csSup _ <| show 2 ∈ _ from _ );
    · rw [ Finset.Icc_eq_cons_Ioc ] <;> norm_num;
      rw [ Finset.filter_insert, Finset.filter_singleton ] ; norm_num;
      split_ifs <;> simp_all +decide [ Nat.Prime.ne_one ];
    · exact ⟨ _, fun n hn => hn.choose_spec.2.2 ▸ Finset.card_le_card hn.choose_spec.1 ⟩;
    · simp +decide [ WeaklyDivisible ];
  · norm_num +zetaDelta at *
