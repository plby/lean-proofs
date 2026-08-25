import ErdosProblems.Erdos964.AffinePreSieve
import ErdosProblems.Erdos964.Admissibility

/-!
# The affine normalization in Section 3 of GGPY

After one progression restriction, all leading coefficients have the same
prime divisors, the constants avoid those primes, and every determinant
prime is among them. This is the paper's Hypothesis A, proved from the
original local admissibility conditions.
-/

namespace Erdos964

open scoped BigOperators

def affineNormalizationModulus (A B : Fin 3 → ℕ) : ℕ :=
  (∏ i, A i) * ∏ ij ∈ (Finset.univ : Finset (Fin 3 × Fin 3)).filter
    (fun ij => ij.1 ≠ ij.2), Nat.dist (A ij.1 * B ij.2) (A ij.2 * B ij.1)

theorem affineNormalizationModulus_pos (A B : Fin 3 → ℕ)
    (hA : ∀ i, 0 < A i) (hne : ∀ i j, i ≠ j → A i * B j ≠ A j * B i) :
    0 < affineNormalizationModulus A B := by
  unfold affineNormalizationModulus
  apply Nat.mul_pos (Finset.prod_pos (fun i _ => hA i))
  apply Finset.prod_pos
  intro ij hij
  exact Nat.dist_pos_of_ne (hne ij.1 ij.2 (Finset.mem_filter.mp hij).2)

theorem affine_leading_dvd_normalization (A B : Fin 3 → ℕ) (i : Fin 3) :
    A i ∣ affineNormalizationModulus A B := by
  exact (Finset.dvd_prod_of_mem A (Finset.mem_univ i)).trans (dvd_mul_right _ _)

theorem affine_determinant_dvd_normalization (A B : Fin 3 → ℕ) (i j : Fin 3) (hij : i ≠ j) :
    Nat.dist (A i * B j) (A j * B i) ∣ affineNormalizationModulus A B := by
  apply dvd_mul_of_dvd_right
  exact Finset.dvd_prod_of_mem _ (Finset.mem_filter.mpr ⟨Finset.mem_univ (i, j), hij⟩)

theorem affine_progression_determinant (a b c d M v : ℕ) :
    Nat.dist ((a * M) * (c * v + d)) ((c * M) * (a * v + b)) =
      M * Nat.dist (a * d) (c * b) := by
  have hleft : (a * M) * (c * v + d) = M * (a * c * v + a * d) := by ring
  have hright : (c * M) * (a * v + b) = M * (a * c * v + c * b) := by ring
  rw [hleft, hright, Nat.dist_mul_left, Nat.dist_add_add_left]

theorem exists_affine_avoiding_modulus (A B : Fin 3 → ℕ) (M : ℕ) (hM : 0 < M)
    (hadm : ∀ p, p.Prime → ∃ n : ℕ, ∀ i, ¬ p ∣ A i * n + B i) :
    ∃ v : ℕ, ∀ i, (A i * v + B i).Coprime M := by
  obtain ⟨v, _, hv⟩ := exists_affine_preSieveResidue A B M.primeFactors hadm
    (fun _ hp => Nat.prime_of_mem_primeFactors hp)
  refine ⟨v, ?_⟩
  intro i
  by_contra hnot
  obtain ⟨p, hp, hpv, hpM⟩ := Nat.Prime.not_coprime_iff_dvd.mp hnot
  have hpmem : p ∈ M.primeFactors := (Nat.mem_primeFactors_of_ne_zero hM.ne').mpr ⟨hp, hpM⟩
  have hprad : p ∣ ∏ q ∈ M.primeFactors, q := Finset.dvd_prod_of_mem _ hpmem
  exact (hp.coprime_iff_not_dvd.mp ((hv i).coprime_dvd_right hprad).symm) hpv

theorem normalized_leading_prime_support (A B : Fin 3 → ℕ) (i : Fin 3) (p : ℕ)
    (hp : p.Prime) :
    p ∣ A i * affineNormalizationModulus A B ↔ p ∣ affineNormalizationModulus A B := by
  constructor
  · intro h
    rcases hp.dvd_mul.mp h with hAi | hM
    · exact hAi.trans (affine_leading_dvd_normalization A B i)
    · exact hM
  · exact fun h => dvd_mul_of_dvd_right h _

theorem normalized_determinant_prime_support (A B : Fin 3 → ℕ) (v : ℕ)
    (i j : Fin 3) (hij : i ≠ j) (p : ℕ) (hp : p.Prime)
    (hpd : p ∣ Nat.dist
      ((A i * affineNormalizationModulus A B) * (A j * v + B j))
      ((A j * affineNormalizationModulus A B) * (A i * v + B i))) :
    p ∣ affineNormalizationModulus A B := by
  rw [affine_progression_determinant] at hpd
  rcases hp.dvd_mul.mp hpd with hM | hdet
  · exact hM
  · exact hdet.trans (affine_determinant_dvd_normalization A B i j hij)

theorem normalized_affine_form_coprime (A B : Fin 3 → ℕ) (v : ℕ)
    (hv : ∀ i, (A i * v + B i).Coprime (affineNormalizationModulus A B)) (i : Fin 3) :
    (A i * affineNormalizationModulus A B).Coprime (A i * v + B i) := by
  exact (((hv i).coprime_dvd_right (affine_leading_dvd_normalization A B i)).mul_right
    (hv i)).symm

theorem affine_progression_nonproportional (A B : Fin 3 → ℕ) (M v : ℕ) (hM : 0 < M)
    (hne : ∀ i j, i ≠ j → A i * B j ≠ A j * B i) :
    ∀ i j, i ≠ j → (A i * M) * (A j * v + B j) ≠ (A j * M) * (A i * v + B i) := by
  intro i j hij heq
  have hpos : 0 < Nat.dist ((A i * M) * (A j * v + B j))
      ((A j * M) * (A i * v + B i)) := by
    rw [affine_progression_determinant]
    exact Nat.mul_pos hM (Nat.dist_pos_of_ne (hne i j hij))
  rw [heq, Nat.dist_self] at hpos
  exact (Nat.lt_irrefl 0) hpos

theorem affine_progression_admissible (A B : Fin 3 → ℕ) (M v : ℕ)
    (hv : ∀ i, (A i * v + B i).Coprime M)
    (hadm : ∀ p, p.Prime → ∃ n : ℕ, ∀ i, ¬ p ∣ A i * n + B i) :
    ∀ p, p.Prime → ∃ n : ℕ, ∀ i, ¬ p ∣ (A i * M) * n + (A i * v + B i) := by
  intro p hp
  by_cases hpM : p ∣ M
  · refine ⟨0, ?_⟩
    intro i hdiv
    simp only [mul_zero, zero_add] at hdiv
    exact (hp.coprime_iff_not_dvd.mp ((hv i).coprime_dvd_right hpM).symm) hdiv
  · obtain ⟨t, ht⟩ := hadm p hp
    obtain ⟨n, hn⟩ := exists_affine_modEq M v t p hp.pos
      (hp.coprime_iff_not_dvd.mpr hpM).symm
    refine ⟨n, ?_⟩
    intro i hdiv
    have hid : (A i * M) * n + (A i * v + B i) = A i * (M * n + v) + B i := by ring
    rw [hid] at hdiv
    have hform := (hn.mul_left (A i)).add_right (B i)
    exact ht i (Nat.modEq_zero_iff_dvd.mp
      (hform.symm.trans (Nat.modEq_zero_iff_dvd.mpr hdiv)))

/-- The local normalization required by the original scalar GGPY sieve,
with both the common prime support and admissibility proved. -/
theorem exists_affine_prime_normalization (A B : Fin 3 → ℕ)
    (hA : ∀ i, 0 < A i) (hne : ∀ i j, i ≠ j → A i * B j ≠ A j * B i)
    (hadm : ∀ p, p.Prime → ∃ n : ℕ, ∀ i, ¬ p ∣ A i * n + B i) :
    ∃ M v : ℕ, 0 < M ∧
      (∀ i, (A i * v + B i).Coprime M) ∧
      (∀ i p, p.Prime → (p ∣ A i * M ↔ p ∣ M)) ∧
      (∀ i j, i ≠ j → ∀ p, p.Prime →
        p ∣ Nat.dist ((A i * M) * (A j * v + B j)) ((A j * M) * (A i * v + B i)) →
          p ∣ M) ∧
      (∀ p, p.Prime → ∃ n : ℕ, ∀ i, ¬ p ∣ (A i * M) * n + (A i * v + B i)) := by
  let M := affineNormalizationModulus A B
  have hM : 0 < M := affineNormalizationModulus_pos A B hA hne
  obtain ⟨v, hv⟩ := exists_affine_avoiding_modulus A B M hM hadm
  exact ⟨M, v, hM, hv, normalized_leading_prime_support A B,
    normalized_determinant_prime_support A B v, affine_progression_admissible A B M v hv hadm⟩

end Erdos964
