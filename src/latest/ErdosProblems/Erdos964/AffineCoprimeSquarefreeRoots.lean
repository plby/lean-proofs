import ErdosProblems.Erdos964.AffineCoprimeRoots
import ErdosProblems.Erdos964.AffineScalarCounting
import ErdosProblems.Erdos964.SquarefreeLocalRoots

/-!
# The squarefree root multiplicity for the second sum

CRT combines the two remaining roots at each prime. Thus the classes
coprime to the distinguished affine value have multiplicity `2^ω(d)`.
-/

namespace Erdos964

open scoped BigOperators

theorem mod_mem_affineCoprimeProductRoots_iff (A B : Fin 3 → ℕ) (j : Fin 3)
    (d n : ℕ) (hd : 0 < d) :
    n % d ∈ affineCoprimeProductRoots A B j d ↔
      d ∣ ∏ i, (A i * n + B i) ∧ d.Coprime (A j * n + B j) := by
  have hmod : n % d ≡ n [MOD d] := by simp [Nat.ModEq]
  have hform := (hmod.mul_left (A j)).add_right (B j)
  have hcop : d.Coprime (A j * (n % d) + B j) ↔ d.Coprime (A j * n + B j) := by
    change Nat.gcd d (A j * (n % d) + B j) = 1 ↔ Nat.gcd d (A j * n + B j) = 1
    rw [Nat.gcd_comm d (A j * (n % d) + B j), Nat.gcd_comm d (A j * n + B j),
      hform.gcd_eq]
  rw [affineCoprimeProductRoots, Finset.mem_filter,
    mod_mem_affineProductRoots_iff A B d n hd, hcop]

theorem affineCoprimeProductRoots_eq_local (A B : Fin 3 → ℕ) (j : Fin 3)
    (d : ℕ) (hd : Squarefree d) :
    affineCoprimeProductRoots A B j d =
      squarefreeLocalRoots d (affineCoprimeProductRoots A B j) := by
  ext n
  conv_lhs =>
    rw [affineCoprimeProductRoots, Finset.mem_filter, affineProductRoots,
      Finset.mem_filter, Finset.mem_range]
  conv_rhs => rw [squarefreeLocalRoots, Finset.mem_filter, Finset.mem_range]
  by_cases hn : n < d
  · simp only [hn, true_and]
    rw [squarefree_dvd_iff_primeFactors d _ hd, squarefree_coprime_iff_primeFactors d _ hd]
    constructor
    · rintro ⟨hdiv, hcop⟩ p hp
      exact (mod_mem_affineCoprimeProductRoots_iff A B j p n
        (Nat.prime_of_mem_primeFactors hp).pos).mpr ⟨hdiv p hp, hcop p hp⟩
    · intro h
      constructor
      · intro p hp
        exact ((mod_mem_affineCoprimeProductRoots_iff A B j p n
          (Nat.prime_of_mem_primeFactors hp).pos).mp (h p hp)).1
      · intro p hp
        exact ((mod_mem_affineCoprimeProductRoots_iff A B j p n
          (Nat.prime_of_mem_primeFactors hp).pos).mp (h p hp)).2
  · simp [hn]

theorem affineCoprimeProductRoots_card_squarefree (A B : Fin 3 → ℕ) (j : Fin 3)
    (d : ℕ) (hd : Squarefree d) :
    (affineCoprimeProductRoots A B j d).card =
      ∏ p ∈ d.primeFactors, (affineCoprimeProductRoots A B j p).card := by
  rw [affineCoprimeProductRoots_eq_local A B j d hd]
  apply squarefreeLocalRoots_card d hd
  intro p _ n hn
  exact (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).1

theorem normalized_affineCoprimeProductRoots_card_squarefree (A B : Fin 3 → ℕ)
    (v d : ℕ) (j : Fin 3) (hd : Squarefree d)
    (hdM : d.Coprime (affineNormalizationModulus A B)) :
    (affineCoprimeProductRoots (fun i => A i * affineNormalizationModulus A B)
      (fun i => A i * v + B i) j d).card = 2 ^ d.primeFactors.card := by
  rw [affineCoprimeProductRoots_card_squarefree _ _ j d hd]
  have hlocal (p : ℕ) (hp : p ∈ d.primeFactors) :
      (affineCoprimeProductRoots (fun i => A i * affineNormalizationModulus A B)
        (fun i => A i * v + B i) j p).card = 2 := by
    have hpprime := Nat.prime_of_mem_primeFactors hp
    apply normalized_affineCoprimeProductRoots_prime_card A B v p j hpprime
    exact hpprime.coprime_iff_not_dvd.mp (hdM.coprime_dvd_left (Nat.dvd_of_mem_primeFactors hp))
  rw [Finset.prod_congr rfl hlocal]
  simp

end Erdos964
