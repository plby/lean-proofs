import ErdosProblems.Erdos394.MixedRatio

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Signed rational-line obstruction for pair lattices

A geometry-of-numbers argument uses signed lattice vectors, so the natural-
coordinate obstruction F-006 is extended here to integer coordinates.  The
only change is a harmless factor two in the height bound.
-/

open Nat Finset

namespace Erdos394

/-- Product of all absolute signed cross-differences for labels below `K`. -/
def intRatioDifferenceProduct (K : ℕ) (j l : ℤ) : ℕ :=
  ∏ ab ∈ nonzeroLabelPairs K,
    Int.natAbs ((ab.1 : ℤ) * l - (ab.2 : ℤ) * j)

/-- Local signed slope compatibility at every prime factor implies divisibility
of the total signed cross-difference product. -/
theorem squarefree_dvd_intRatioDifferenceProduct {q K : ℕ} {j l : ℤ}
    (hq : Squarefree q)
    (hlocal : ∀ p : ℕ, p.Prime → p ∣ q →
      ∃ A < K, ∃ B < K, (A ≠ 0 ∨ B ≠ 0) ∧
        p ∣ Int.natAbs ((A : ℤ) * l - (B : ℤ) * j)) :
    q ∣ intRatioDifferenceProduct K j l := by
  rw [← Nat.prod_primeFactors_of_squarefree hq]
  apply Finset.prod_dvd_of_isRelPrime
  · simpa only [UniqueFactorizationMonoid.primeFactors_eq_natPrimeFactors]
      using (UniqueFactorizationMonoid.pairwise_primeFactors_isRelPrime (a := q))
  · intro p hpq
    have hp : p.Prime := Nat.prime_of_mem_primeFactors hpq
    have hpd : p ∣ q := Nat.dvd_of_mem_primeFactors hpq
    obtain ⟨A, hAK, B, hBK, hAB, hpdiv⟩ := hlocal p hp hpd
    apply hpdiv.trans
    unfold intRatioDifferenceProduct
    exact Finset.dvd_prod_of_mem (s := nonzeroLabelPairs K) (a := (A, B))
      (fun ab : ℕ × ℕ ↦
        Int.natAbs ((ab.1 : ℤ) * l - (ab.2 : ℤ) * j))
      (by
        simp only [nonzeroLabelPairs, Finset.mem_erase, ne_eq,
          Prod.mk.injEq, Finset.mem_product, Finset.mem_range]
        refine ⟨?_, hAK, hBK⟩
        rintro ⟨hA, hB⟩
        exact hAB.elim (fun ha ↦ ha hA) (fun hb ↦ hb hB))

/-- A signed cross-difference is at most `2*K*M` when both coordinates have
absolute value at most `M`. -/
theorem intRatioDifference_le {K M A B : ℕ} {j l : ℤ}
    (hj : j.natAbs ≤ M) (hl : l.natAbs ≤ M)
    (hAK : A < K) (hBK : B < K) :
    Int.natAbs ((A : ℤ) * l - (B : ℤ) * j) ≤ 2 * K * M := by
  calc
    Int.natAbs ((A : ℤ) * l - (B : ℤ) * j) ≤
        Int.natAbs ((A : ℤ) * l) + Int.natAbs ((B : ℤ) * j) :=
      Int.natAbs_sub_le _ _
    _ = A * l.natAbs + B * j.natAbs := by
      simp [Int.natAbs_mul]
    _ ≤ 2 * K * M := by nlinarith

/-- Signed height bound for the full product. -/
theorem intRatioDifferenceProduct_le {K M : ℕ} {j l : ℤ}
    (hK : 0 < K) (hM : 0 < M) (hj : j.natAbs ≤ M) (hl : l.natAbs ≤ M) :
    intRatioDifferenceProduct K j l ≤ (2 * K * M) ^ (K * K) := by
  unfold intRatioDifferenceProduct
  calc
    (∏ ab ∈ nonzeroLabelPairs K,
      Int.natAbs ((ab.1 : ℤ) * l - (ab.2 : ℤ) * j)) ≤
        (2 * K * M) ^ (nonzeroLabelPairs K).card := by
      apply Finset.prod_le_pow_card
      intro ab hab
      simp only [nonzeroLabelPairs, Finset.mem_erase, Finset.mem_product,
        Finset.mem_range] at hab
      exact intRatioDifference_le hj hl hab.2.1 hab.2.2
    _ ≤ (2 * K * M) ^ (K * K) := by
      apply Nat.pow_le_pow_right (by positivity)
      calc
        (nonzeroLabelPairs K).card ≤
            ((Finset.range K) ×ˢ (Finset.range K)).card :=
          Finset.card_erase_le
        _ = K * K := by simp

/-- Below the signed height threshold, every compatible lattice vector lies
on one of the finitely many exact rational lines. -/
theorem exists_exact_int_ratio_of_large_squarefree {q K M : ℕ} {j l : ℤ}
    (hq : Squarefree q) (hK : 0 < K) (hM : 0 < M)
    (hj : j.natAbs ≤ M) (hl : l.natAbs ≤ M)
    (hlocal : ∀ p : ℕ, p.Prime → p ∣ q →
      ∃ A < K, ∃ B < K, (A ≠ 0 ∨ B ≠ 0) ∧
        p ∣ Int.natAbs ((A : ℤ) * l - (B : ℤ) * j))
    (hlarge : (2 * K * M) ^ (K * K) < q) :
    ∃ A < K, ∃ B < K, (A ≠ 0 ∨ B ≠ 0) ∧
      (A : ℤ) * l = (B : ℤ) * j := by
  by_contra h
  push Not at h
  have hprod_pos : 0 < intRatioDifferenceProduct K j l := by
    apply Finset.prod_pos
    intro ab hab
    simp only [nonzeroLabelPairs, Finset.mem_erase, Finset.mem_product,
      Finset.mem_range] at hab
    have habnz : ab.1 ≠ 0 ∨ ab.2 ≠ 0 := by
      by_contra hz
      push Not at hz
      apply hab.1
      ext <;> simp_all
    have hne : (ab.1 : ℤ) * l ≠ (ab.2 : ℤ) * j :=
      h ab.1 hab.2.1 ab.2 hab.2.2 habnz
    exact Int.natAbs_sub_pos_iff.mpr hne
  have hqdvd : q ∣ intRatioDifferenceProduct K j l :=
    squarefree_dvd_intRatioDifferenceProduct hq hlocal
  have hqle : q ≤ intRatioDifferenceProduct K j l :=
    Nat.le_of_dvd hprod_pos hqdvd
  have hprod_le := intRatioDifferenceProduct_le hK hM hj hl
  omega

end Erdos394
