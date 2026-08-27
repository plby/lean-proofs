import ErdosProblems.Erdos4.TiltedBlocks

/-! A product with small factors has a divisor in a controlled intermediate range. -/

open scoped BigOperators

namespace Erdos4.Tilted

theorem exists_subset_prod_window (S : Finset ℕ) {R : ℕ} (hR : 1 ≤ R)
    (hsmall : ∀ p ∈ S, p ≤ R) (hprod : R < ∏ p ∈ S, p) :
    ∃ T ⊆ S, R < ∏ p ∈ T, p ∧ (∏ p ∈ T, p) ≤ R * R := by
  classical
  induction S using Finset.induction_on with
  | empty => simp only [Finset.prod_empty] at hprod; omega
  | @insert p S hp ih =>
    by_cases htail : R < ∏ q ∈ S, q
    · obtain ⟨T, hT, hRT, hTR⟩ := ih (fun q hq => hsmall q (Finset.mem_insert_of_mem hq)) htail
      exact ⟨T, hT.trans (Finset.subset_insert _ _), hRT, hTR⟩
    · refine ⟨insert p S, Finset.Subset.refl _, hprod, ?_⟩
      rw [Finset.prod_insert hp]
      exact Nat.mul_le_mul (hsmall p (Finset.mem_insert_self _ _)) (le_of_not_gt htail)

theorem prime_product_squarefree (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    Squarefree (∏ p ∈ S, p) := by
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro p hp q hq hpq
    exact Nat.coprime_iff_isRelPrime.mp ((Nat.coprime_primes (hS p hp) (hS q hq)).mpr hpq)
  · intro p hp
    exact (hS p hp).squarefree

theorem prime_product_dvd_iff {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime)
    {n : ℕ} (hn : n ≠ 0) : (∏ p ∈ S, p) ∣ n ↔ S ⊆ n.primeFactors := by
  have hs := prime_product_squarefree S hS
  have hh := Nat.prod_primeFactors_dvd_iff (n := ∏ p ∈ S, p) hn
  rwa [Nat.prod_primeFactors_of_squarefree hs, Nat.primeFactors_prod hS] at hh

theorem large_prod_has_witness {S H : Finset ℕ} (hHS : H ⊆ S) {R X : ℕ}
    (hR : 1 ≤ R) (hRX : R * R ≤ X) (hprod : X < ∏ p ∈ H, p) :
    (∃ p ∈ S, R < p ∧ p ∈ H) ∨
      ∃ T ∈ S.powerset, T ⊆ H ∧ R < ∏ p ∈ T, p ∧ (∏ p ∈ T, p) ≤ X := by
  classical
  by_cases hlarge : ∃ p ∈ H, R < p
  · obtain ⟨p, hp, hRp⟩ := hlarge
    exact Or.inl ⟨p, hHS hp, hRp, hp⟩
  · have hsmall : ∀ p ∈ H, p ≤ R := by
      intro p hp
      by_contra h
      exact hlarge ⟨p, hp, lt_of_not_ge h⟩
    have hRR : R ≤ R * R := by nlinarith
    obtain ⟨T, hTH, hRT, hTR⟩ := exists_subset_prod_window H hR hsmall
      ((hRR.trans hRX).trans_lt hprod)
    exact Or.inr ⟨T, Finset.mem_powerset.mpr (hTH.trans hHS), hTH, hRT, hTR.trans hRX⟩

end Erdos4.Tilted
