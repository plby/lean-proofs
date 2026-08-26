/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierPinnedCombinedLocal
import ErdosProblems.Erdos4b.ResidualPrimeFiberMertens

/-!
# The exact residual cofactor product in the local coverage comparison

The prime two contributes one half. Every remaining comparison factor
is exactly the local correction already used in the residual-fibre sieve.
-/

namespace Erdos4b

noncomputable section

open scoped BigOperators

theorem one_sub_residualPrimeDensity_eq {p : ℕ} (hp : p.Prime) :
    1 - residualPrimeDensity p = ((p : ℝ) - 2) / ((p : ℝ) - 1) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  rw [residualPrimeDensity_eq_inv_pred hp, Nat.cast_sub hp.one_lt.le, Nat.cast_one]
  apply (eq_div_iff (by linarith : (p : ℝ) - 1 ≠ 0)).mpr
  rw [sub_mul, one_mul, inv_mul_cancel₀ (by linarith : (p : ℝ) - 1 ≠ 0)]
  ring

theorem prod_pinnedResidualLocalComparison_eq_half_mul_cofactor
    (m : ℕ) {Y : ℕ} (hY : 2 ≤ Y) :
    (∏ p ∈ boundedFourierPrimes Y, pinnedResidualLocalComparison m p) =
      (1 / 2 : ℝ) * residualCofactorLocalProduct Y m := by
  classical
  have hnat : (∏ p ∈ boundedFourierPrimes Y, pinnedResidualLocalComparison m p) =
      ∏ p ∈ Nat.primesLE Y, pinnedResidualLocalComparison m p :=
    Finset.prod_subtype_of_mem (fun p ↦ pinnedResidualLocalComparison m p)
      (fun p hp ↦ (Nat.mem_primesLE.mp hp).2)
  have htwo : 2 ∈ Nat.primesLE Y := Nat.mem_primesLE.mpr ⟨hY, Nat.prime_two⟩
  rw [hnat, ← Finset.mul_prod_erase _ _ htwo]
  have htwoFactor : pinnedResidualLocalComparison m 2 = (1 / 2 : ℝ) := by
    simp only [pinnedResidualLocalComparison, if_true]
  rw [htwoFactor]
  apply congrArg (fun t : ℝ ↦ (1 / 2) * t)
  have hsub : residualCofactorSievePrimes Y m ⊆ (Nat.primesLE Y).erase 2 := by
    intro p hp
    obtain ⟨hpS, hpm⟩ := Finset.mem_filter.mp hp
    obtain ⟨hp2, hpY, hpPrime⟩ := Erdos851.mem_sievePrimes.mp hpS
    exact Finset.mem_erase.mpr ⟨by omega, Nat.mem_primesLE.mpr ⟨hpY, hpPrime⟩⟩
  calc
    _ = ∏ p ∈ residualCofactorSievePrimes Y m, pinnedResidualLocalComparison m p := by
      symm
      apply Finset.prod_subset hsub
      intro p hp hn
      obtain ⟨hp2, hpY⟩ := Finset.mem_erase.mp hp
      obtain ⟨hpY', hpPrime⟩ := Nat.mem_primesLE.mp hpY
      have hpm : ¬p ∣ m := by
        intro hd
        apply hn
        exact Finset.mem_filter.mpr ⟨Erdos851.mem_sievePrimes.mpr
          ⟨by have := hpPrime.two_le; omega, hpY', hpPrime⟩, hd⟩
      simp only [pinnedResidualLocalComparison, if_neg hp2, if_neg hpm]
    _ = _ := by
      unfold residualCofactorLocalProduct
      apply Finset.prod_congr rfl
      intro p hp
      obtain ⟨hpS, hpm⟩ := Finset.mem_filter.mp hp
      obtain ⟨hp2, hpY, hpPrime⟩ := Erdos851.mem_sievePrimes.mp hpS
      rw [pinnedResidualLocalComparison, if_neg (by omega), if_pos hpm,
        one_sub_residualPrimeDensity_eq hpPrime]

end

end Erdos4b
