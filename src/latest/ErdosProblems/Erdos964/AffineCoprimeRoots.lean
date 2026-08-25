import ErdosProblems.Erdos964.AffineSquarefreeRoots

/-!
# Root classes coprime to the distinguished affine value

The semiprime second sum first counts root classes in which the
distinguished affine value is coprime to the squarefree divisor.
At each good prime exactly two of the three roots remain.
-/

namespace Erdos964

def affineCoprimeProductRoots (A B : Fin 3 → ℕ) (j : Fin 3) (d : ℕ) : Finset ℕ :=
  (affineProductRoots A B d).filter (fun n => d.Coprime (A j * n + B j))

theorem affineCoprimeProductRoots_prime_eq_erase (A B : Fin 3 → ℕ) (j : Fin 3)
    (p : ℕ) (hp : p.Prime) (hA : (A j).Coprime p) :
    affineCoprimeProductRoots A B j p =
      (affineProductRoots A B p).erase (affineRoot (A j) (B j) p) := by
  let : NeZero p := ⟨hp.ne_zero⟩
  have hrootlt : affineRoot (A j) (B j) p < p := ZMod.val_lt _
  ext n
  simp only [affineCoprimeProductRoots, Finset.mem_filter, Finset.mem_erase]
  constructor
  · rintro ⟨hn, hcop⟩
    refine ⟨?_, hn⟩
    intro heq
    exact hp.coprime_iff_not_dvd.mp hcop
      (heq ▸ affineRoot_dvd (A j) (B j) p hp.pos hA)
  · rintro ⟨hne, hn⟩
    refine ⟨hn, hp.coprime_iff_not_dvd.mpr ?_⟩
    intro hdiv
    have hmod := (modEq_affineRoot_iff (A j) (B j) p n hp.pos hA).mpr hdiv
    have hnlt := Finset.mem_range.mp (Finset.mem_filter.mp hn).1
    apply hne
    simpa only [Nat.ModEq, Nat.mod_eq_of_lt hnlt, Nat.mod_eq_of_lt hrootlt] using hmod

theorem affineCoprimeProductRoots_prime_card (A B : Fin 3 → ℕ) (j : Fin 3)
    (p : ℕ) (hp : p.Prime) (hA : ∀ i, (A i).Coprime p)
    (hdet : ∀ i k, i ≠ k → ¬ p ∣ Nat.dist (A i * B k) (A k * B i)) :
    (affineCoprimeProductRoots A B j p).card = 2 := by
  have hmem : affineRoot (A j) (B j) p ∈ affineProductRoots A B p := by
    rw [affineProductRoots_eq_image A B p hp hA]
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩
  rw [affineCoprimeProductRoots_prime_eq_erase A B j p hp (hA j),
    Finset.card_erase_of_mem hmem, affineProductRoots_card A B p hp hA hdet]

theorem normalized_affineCoprimeProductRoots_prime_card (A B : Fin 3 → ℕ)
    (v p : ℕ) (j : Fin 3) (hp : p.Prime)
    (hpM : ¬ p ∣ affineNormalizationModulus A B) :
    (affineCoprimeProductRoots (fun i => A i * affineNormalizationModulus A B)
      (fun i => A i * v + B i) j p).card = 2 := by
  apply affineCoprimeProductRoots_prime_card _ _ j p hp
  · intro i
    apply Nat.Coprime.symm
    apply hp.coprime_iff_not_dvd.mpr
    intro h
    exact hpM ((normalized_leading_prime_support A B i p hp).mp h)
  · intro i k hik h
    exact hpM (normalized_determinant_prime_support A B v i k hik p hp h)

end Erdos964
