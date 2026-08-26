import ErdosProblems.Erdos520.BonamiModel

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Finset MeasureTheory
open scoped BigOperators

namespace Erdos
namespace Problem520

/-!
# Second moment of the smooth contribution

The `r = 1` case of the finite-cube inequality already gives the standard
second-moment estimate for a smooth sum.  This is the probabilistic part of
the paper's treatment of the `y₀`-smooth remainder; the separate
smooth-number cardinality estimate is analytic number theory.
-/

theorem Ψ_zeroPrimeCutoff (omega : Omega) (z : ℕ) :
    Ψ omega z 0 = if 1 ≤ z then 1 else 0 := by
  have hprimes : (1 : ℕ).primesBelow = ∅ := by
    ext p
    simp only [Nat.mem_primesBelow, Finset.notMem_empty, iff_false]
    rintro ⟨hp, hprime⟩
    have hone := hprime.one_lt
    omega
  have hsets : squarefreeSmoothSets z 0 =
      if 1 ≤ z then {∅} else ∅ := by
    unfold squarefreeSmoothSets
    by_cases hz : 1 ≤ z
    · simp [freshProduct, hprimes, hz]
    · have hz0 : z = 0 := by omega
      subst z
      simp [freshProduct, hprimes]
  rw [Ψ_eq_sum_squarefreeSmoothSets, hsets]
  split <;> simp [freshCharacter]

theorem freshPrimes_zero_left (y : ℕ) :
    freshPrimes 0 y = (y + 1).primesBelow := by
  ext p
  simp only [mem_freshPrimes, Nat.mem_primesBelow]
  constructor
  · rintro ⟨hp, _hp0, hpy⟩
    exact ⟨by omega, hp⟩
  · rintro ⟨hpy, hp⟩
    exact ⟨hp, hp.pos, by omega⟩

theorem frozenFreshWalshExpansion_zero_left
    (old omega : Omega) (z y : ℕ) :
    frozenFreshWalshExpansion old z 0 y omega = Ψ omega z y := by
  rw [Ψ_eq_freshWalshExpansion omega z (Nat.zero_le y)]
  unfold frozenFreshWalshExpansion freshWalshExpansion freshCoefficient
  apply Finset.sum_congr rfl
  intro S _hS
  rw [Ψ_zeroPrimeCutoff old, Ψ_zeroPrimeCutoff omega]

theorem freshCoefficient_zero_energy (old : Omega) (z y : ℕ) :
    (∑ A ∈ (freshPrimes 0 y).powerset,
        freshCoefficient old z 0 A ^ 2) =
      (squarefreeSmoothSets z y).card := by
  rw [freshPrimes_zero_left]
  unfold squarefreeSmoothSets
  rw [Finset.card_filter]
  push_cast
  apply Finset.sum_congr rfl
  intro A hA
  have hprime : ∀ p ∈ A, p.Prime := by
    intro p hp
    exact Nat.prime_of_mem_primesBelow
      (Finset.mem_powerset.mp hA hp)
  have hprodPos : 0 < freshProduct A := freshProduct_pos_of_primes hprime
  unfold freshCoefficient
  rw [Ψ_zeroPrimeCutoff]
  have hdiv : 1 ≤ z / freshProduct A ↔ freshProduct A ≤ z := by
    rw [Nat.le_div_iff_mul_le hprodPos]
    simp
  by_cases hle : freshProduct A ≤ z
  · simp [hdiv.mpr hle, hle]
  · simp [hdiv, hle]

/-- Smooth-sum second moment bounded by the number of squarefree smooth
integers represented by `squarefreeSmoothSets`. -/
theorem integral_sq_Ψ_le_card_squarefreeSmoothSets
    (z y : ℕ) :
    (∫ omega, |Ψ omega z y| ^ 2 ∂μ) ≤
      (squarefreeSmoothSets z y).card := by
  let old : Omega := fun _ => false
  have hbonami := frozenFreshWalshExpansion_bonami_integral
    1 (by norm_num) old z 0 y
  norm_num at hbonami
  rw [freshCoefficient_zero_energy old z y] at hbonami
  simpa only [frozenFreshWalshExpansion_zero_left, sq_abs] using! hbonami

theorem card_squarefreeSmoothSets_le_smoothNumbersUpTo (z y : ℕ) :
    (squarefreeSmoothSets z y).card ≤
      (Nat.smoothNumbersUpTo z (y + 1)).card := by
  apply Finset.card_le_card_of_injOn freshProduct
  · intro S hS
    rw [Finset.mem_coe, Nat.mem_smoothNumbersUpTo]
    have hmem := mem_squarefreeSmoothSets.mp hS
    have hprime : ∀ p ∈ S, p.Prime := by
      intro p hp
      exact Nat.prime_of_mem_primesBelow (hmem.1 hp)
    refine ⟨hmem.2, Nat.mem_smoothNumbers_of_primeFactors_subset ?_ ?_⟩
    · exact (freshProduct_pos_of_primes hprime).ne'
    · rw [freshProduct_primeFactors hprime]
      exact hmem.1.trans (Finset.filter_subset _ _)
  · intro S hS T hT hEq
    have hmemS := mem_squarefreeSmoothSets.mp hS
    have hmemT := mem_squarefreeSmoothSets.mp hT
    have hprimeS : ∀ p ∈ S, p.Prime := by
      intro p hp
      exact Nat.prime_of_mem_primesBelow (hmemS.1 hp)
    have hprimeT : ∀ p ∈ T, p.Prime := by
      intro p hp
      exact Nat.prime_of_mem_primesBelow (hmemT.1 hp)
    calc
      S = (freshProduct S).primeFactors :=
        (freshProduct_primeFactors hprimeS).symm
      _ = (freshProduct T).primeFactors := congrArg Nat.primeFactors hEq
      _ = T := freshProduct_primeFactors hprimeT

/-- Usual smooth-number form of the second-moment estimate. -/
theorem integral_sq_Ψ_le_smoothNumbersUpTo_card (z y : ℕ) :
    (∫ omega, |Ψ omega z y| ^ 2 ∂μ) ≤
      (Nat.smoothNumbersUpTo z (y + 1)).card := by
  exact (integral_sq_Ψ_le_card_squarefreeSmoothSets z y).trans
    (by exact_mod_cast card_squarefreeSmoothSets_le_smoothNumbersUpTo z y)

end Problem520
end Erdos
