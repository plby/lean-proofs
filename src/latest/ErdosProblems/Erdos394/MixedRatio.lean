import ErdosProblems.Erdos394.CosetGap

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# A rational-line obstruction for mixed CRT root pairs

The product below packages the elementary observation used to control short
vectors in pair-correlation lattices: if each prime divisor of a squarefree
modulus chooses one of finitely many slopes, then either the vector lies on one
of those rational lines or it cannot be too short.
-/

open Nat Finset

namespace Erdos394

/-- All label pairs below `K`, except the identically zero pair. -/
def nonzeroLabelPairs (K : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range K) ×ˢ (Finset.range K)).erase (0, 0)

/-- Product of all absolute cross-differences `|A*l-B*j|` for labels below K. -/
def ratioDifferenceProduct (K j l : ℕ) : ℕ :=
  ∏ ab ∈ nonzeroLabelPairs K, Nat.dist (ab.1 * l) (ab.2 * j)

/-- A squarefree modulus whose every prime factor divides one of the cross
Differences divides their total product. -/
theorem squarefree_dvd_ratioDifferenceProduct {q K j l : ℕ} (hq : Squarefree q)
    (hlocal : ∀ p : ℕ, p.Prime → p ∣ q →
      ∃ A < K, ∃ B < K, (A ≠ 0 ∨ B ≠ 0) ∧
        p ∣ Nat.dist (A * l) (B * j)) :
    q ∣ ratioDifferenceProduct K j l := by
  rw [← Nat.prod_primeFactors_of_squarefree hq]
  apply Finset.prod_dvd_of_isRelPrime
  · simpa only [UniqueFactorizationMonoid.primeFactors_eq_natPrimeFactors]
      using (UniqueFactorizationMonoid.pairwise_primeFactors_isRelPrime (a := q))
  · intro p hpq
    have hp : p.Prime := Nat.prime_of_mem_primeFactors hpq
    have hpd : p ∣ q := Nat.dvd_of_mem_primeFactors hpq
    obtain ⟨A, hAK, B, hBK, hAB, hpdiv⟩ := hlocal p hp hpd
    apply hpdiv.trans
    unfold ratioDifferenceProduct
    exact Finset.dvd_prod_of_mem (s := nonzeroLabelPairs K) (a := (A, B))
      (fun ab : ℕ × ℕ ↦ Nat.dist (ab.1 * l) (ab.2 * j))
      (by
        simp only [nonzeroLabelPairs, Finset.mem_erase, ne_eq,
          Prod.mk.injEq, Finset.mem_product, Finset.mem_range]
        refine ⟨?_, hAK, hBK⟩
        rintro ⟨hA, hB⟩
        exact hAB.elim (fun ha ↦ ha hA) (fun hb ↦ hb hB))

/-- Each cross-difference is bounded by `K*M` when both coordinates are at
most `M` and both labels are below `K`. -/
theorem ratioDifference_le {K M j l A B : ℕ} (hj : j ≤ M) (hl : l ≤ M)
    (hAK : A < K) (hBK : B < K) :
    Nat.dist (A * l) (B * j) ≤ K * M := by
  have hAl : A * l ≤ K * M := by nlinarith
  have hBj : B * j ≤ K * M := by nlinarith
  rw [Nat.dist_eq_max_sub_min]
  omega

/-- The product of cross-differences has the elementary height bound
`(K*M)^(K^2)`. -/
theorem ratioDifferenceProduct_le {K M j l : ℕ} (hK : 0 < K) (hM : 0 < M)
    (hj : j ≤ M) (hl : l ≤ M) :
    ratioDifferenceProduct K j l ≤ (K * M) ^ (K * K) := by
  unfold ratioDifferenceProduct
  calc
    (∏ ab ∈ nonzeroLabelPairs K, Nat.dist (ab.1 * l) (ab.2 * j))
        ≤ (K * M) ^ (nonzeroLabelPairs K).card := by
          apply Finset.prod_le_pow_card
          intro ab hab
          simp only [nonzeroLabelPairs, Finset.mem_erase, Finset.mem_product,
            Finset.mem_range] at hab
          exact ratioDifference_le hj hl hab.2.1 hab.2.2
    _ ≤ (K * M) ^ (K * K) := by
      apply Nat.pow_le_pow_right (mul_pos hK hM)
      calc
        (nonzeroLabelPairs K).card
            ≤ ((Finset.range K) ×ˢ (Finset.range K)).card := Finset.card_erase_le
        _ = K * K := by simp

/-- If the squarefree modulus is larger than the height bound, local slope
compatibility forces one exact rational slope over the integers. -/
theorem exists_exact_ratio_of_large_squarefree {q K M j l : ℕ}
    (hq : Squarefree q) (hK : 0 < K) (hM : 0 < M)
    (hj : j ≤ M) (hl : l ≤ M)
    (hlocal : ∀ p : ℕ, p.Prime → p ∣ q →
      ∃ A < K, ∃ B < K, (A ≠ 0 ∨ B ≠ 0) ∧
        p ∣ Nat.dist (A * l) (B * j))
    (hlarge : (K * M) ^ (K * K) < q) :
    ∃ A < K, ∃ B < K, (A ≠ 0 ∨ B ≠ 0) ∧ A * l = B * j := by
  by_contra h
  push Not at h
  have hprod_pos : 0 < ratioDifferenceProduct K j l := by
    apply Finset.prod_pos
    intro ab hab
    simp only [nonzeroLabelPairs, Finset.mem_erase, Finset.mem_product,
      Finset.mem_range] at hab
    have habnz : ab.1 ≠ 0 ∨ ab.2 ≠ 0 := by
      by_contra hz
      push Not at hz
      apply hab.1
      ext <;> simp_all
    have hne : ab.1 * l ≠ ab.2 * j :=
      h ab.1 hab.2.1 ab.2 hab.2.2 habnz
    exact Nat.dist_pos_of_ne hne
  have hqdvd : q ∣ ratioDifferenceProduct K j l :=
    squarefree_dvd_ratioDifferenceProduct hq hlocal
  have hqle : q ≤ ratioDifferenceProduct K j l := Nat.le_of_dvd hprod_pos hqdvd
  have hprod_le : ratioDifferenceProduct K j l ≤ (K * M) ^ (K * K) :=
    ratioDifferenceProduct_le hK hM hj hl
  omega

end Erdos394
