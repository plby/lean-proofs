import ErdosProblems.Erdos394.MixedRatioInt
import ErdosProblems.Erdos394.PrimeSubset

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Product-root form of the signed non-rational height obstruction

If every remaining prime is at least a fixed `K²`-th power, their product
forces one factor of that root scale into the height for each prime.
-/

open Nat Finset

namespace Erdos394

/-- A signed compatible vector off all small rational lines forces the direct
height inequality `q ≤ (2 K M)^(K²)`. -/
theorem nonrational_int_modulus_le_height {q K : ℕ} {j l : ℤ}
    (hq : Squarefree q) (hK : 1 < K)
    (hlocal : ∀ p : ℕ, p.Prime → p ∣ q →
      ∃ A < K, ∃ B < K, (A ≠ 0 ∨ B ≠ 0) ∧
        p ∣ Int.natAbs ((A : ℤ) * l - (B : ℤ) * j))
    (hnorat : ∀ A < K, ∀ B < K, (A ≠ 0 ∨ B ≠ 0) →
      (A : ℤ) * l ≠ (B : ℤ) * j) :
    q ≤ (2 * K * max j.natAbs l.natAbs) ^ (K * K) := by
  let M := max j.natAbs l.natAbs
  have hM : 0 < M := by
    by_contra hzero
    have hj0 : j = 0 := by
      apply Int.natAbs_eq_zero.mp
      exact Nat.eq_zero_of_not_pos (fun h ↦ hzero (lt_of_lt_of_le h (le_max_left _ _)))
    have hl0 : l = 0 := by
      apply Int.natAbs_eq_zero.mp
      exact Nat.eq_zero_of_not_pos (fun h ↦ hzero (lt_of_lt_of_le h (le_max_right _ _)))
    have hcontra := hnorat 1 hK 0 (by omega) (Or.inl (by omega))
    simp [hj0, hl0] at hcontra
  change q ≤ (2 * K * M) ^ (K * K)
  by_contra hnot
  have hlarge : (2 * K * M) ^ (K * K) < q := by omega
  obtain ⟨A, hAK, B, hBK, hAB, heq⟩ :=
    exists_exact_int_ratio_of_large_squarefree hq (by omega) hM
      (le_max_left _ _) (le_max_right _ _) hlocal hlarge
  exact hnorat A hAK B hBK hAB heq

/-- If each prime in `P` is at least `Z^(K²)`, a non-rational compatible
vector has height at least `Z^|P|/(2K)`, in denominator-free form. -/
theorem primeProduct_root_le_two_mul_height
    (P : Finset ℕ) {K Z : ℕ} {j l : ℤ}
    (hprime : ∀ p ∈ P, p.Prime) (hK : 1 < K)
    (hlarge : ∀ p ∈ P, Z ^ (K * K) ≤ p)
    (hlocal : ∀ p ∈ P,
      ∃ A < K, ∃ B < K, (A ≠ 0 ∨ B ≠ 0) ∧
        p ∣ Int.natAbs ((A : ℤ) * l - (B : ℤ) * j))
    (hnorat : ∀ A < K, ∀ B < K, (A ≠ 0 ∨ B ≠ 0) →
      (A : ℤ) * l ≠ (B : ℤ) * j) :
    Z ^ P.card ≤ 2 * K * max j.natAbs l.natAbs := by
  let q := primeProduct P
  have hsq : Squarefree q := squarefree_primeProduct P hprime
  have hqheight : q ≤
      (2 * K * max j.natAbs l.natAbs) ^ (K * K) := by
    apply nonrational_int_modulus_le_height hsq hK
    · intro p hp hpd
      have hpP : p ∈ P := by
        have hpdiv : p ∣ ∏ r ∈ P, r := by simpa [q, primeProduct] using hpd
        obtain ⟨r, hr, hpr⟩ :=
          (_root_.Prime.dvd_finsetProd_iff hp.prime (fun r : ℕ ↦ r)).mp hpdiv
        have heq : p = r :=
          (Nat.prime_dvd_prime_iff_eq hp (hprime r hr)).mp hpr
        exact heq ▸ hr
      exact hlocal p hpP
    · exact hnorat
  have hrootq : (Z ^ P.card) ^ (K * K) ≤ q := by
    calc
      (Z ^ P.card) ^ (K * K) = (Z ^ (K * K)) ^ P.card := by
        simp only [← pow_mul]
        rw [Nat.mul_comm P.card (K * K)]
      _ = ∏ _p ∈ P, Z ^ (K * K) := by simp
      _ ≤ ∏ p ∈ P, p := by
        apply Finset.prod_le_prod
        · intro p hp
          omega
        · exact hlarge
      _ = q := rfl
  have hpowers : (Z ^ P.card) ^ (K * K) ≤
      (2 * K * max j.natAbs l.natAbs) ^ (K * K) :=
    hrootq.trans hqheight
  exact (Nat.pow_le_pow_iff_left (by nlinarith [hK] : K * K ≠ 0)).mp hpowers

end Erdos394
