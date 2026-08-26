import ErdosProblems.Erdos421.Greedy
import ErdosProblems.Erdos421.Witnesses
import ErdosProblems.Erdos421.Forest

/-!
# Witnesses for the actual rejected gaps

The construction and the abstract cancellation lemmas together give the
canonical witnesses described in Lemma 3.1 of Sneiderman's selected note.
-/

namespace Erdos421

/-- Every actual rejection has a full later interval, a longer earlier block,
and an earlier block lying wholly in the old prefix or wholly in the new gap. -/
theorem rejected_witness (k : ℕ) (hk : Rejected k) :
    ∃ (E : Finset ℕ) (m n : ℕ),
      prime k < m ∧ m ≤ n ∧ n < prime (k + 1) ∧
      (∀ e ∈ E, e < m) ∧ E.prod id = (Finset.Icc m n).prod id ∧
      n - m + 1 < E.card ∧
      (IsBlock (stage k) E ∨
        ∃ a b, prime k < a ∧ a ≤ b ∧ b < m ∧ E = Finset.Icc a b) := by
  obtain ⟨E, m, n, hpm, hmn, hnq, hE, hsep, hprod, hcard⟩ :=
    canonical_rejection (stage_collisionFree k) (stage_bounds k) (prime_mem_stage k)
      (prime_prime k) (prime_prime (k + 1)) (prime_strictMono (Nat.lt_succ_self k)) hk
  refine ⟨E, m, n, hpm, hmn, hnq, hsep, hprod, hcard, ?_⟩
  rcases earlier_block_location (prime_prime k) (prime_mem_stage k)
      (prime_succ_le_two_mul k) hpm hnq hE hsep hprod with hEA | hnew
  · exact Or.inl (hE.restrict Finset.subset_union_left hEA)
  · exact Or.inr hnew

/-- Boundary primes in an earlier witness give precisely the edge alternatives
used in the forest argument. -/
theorem witness_boundary_alternatives {E : Finset ℕ} {m n i : ℕ}
    (hp : prime i ∈ E) (hq : prime (i + 1) ∈ E)
    (hsep : ∀ e ∈ E, e < m)
    (hprod : E.prod id = (Finset.Icc m n).prod id) :
    (∃ j : ℕ, 2 ≤ j ∧ m ≤ j * prime i ∧ j * prime (i + 1) ≤ n) ∨
      (prime i) ^ 2 ≤ n * (prime (i + 1) - prime i) + prime i * (n - m + 1) := by
  apply parent_child_alternatives (prime_prime i) (prime_prime (i + 1))
    (prime_strictMono (Nat.lt_succ_self i)) (hsep _ hq)
  · rw [← hprod]
    exact Finset.dvd_prod_of_mem id hp
  · rw [← hprod]
    exact Finset.dvd_prod_of_mem id hq

end Erdos421
