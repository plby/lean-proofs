/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos387.Section6Bridge
import ErdosProblems.Erdos387.SieveInstantiation
import ErdosProblems.Erdos387.UnconditionalCover

/-!
# Unconditional refined BNPZ cover

The public covering construction removes prime divisors at most `k`.  BNPZ
also refine its progression modulo the product of the primes in `(k, 2k)`.
This file carries out that finite CRT refinement and proves the literal
`BPZSection6InputRefined` interface without any additional hypothesis.
-/

namespace Erdos387

open scoped BigOperators

namespace CoverBPZ

/-- The extra squarefree factor used to refine the public progression. -/
def refinementPrimeProduct (k : ℕ) : ℕ :=
  sievePrimeProduct k (2 * k)

theorem refinementPrimeProduct_pos (k : ℕ) :
    0 < refinementPrimeProduct k := by
  exact sievePrimeProduct_pos k (2 * k)

theorem prime_dvd_refinementPrimeProduct {k q : ℕ}
    (hq : q.Prime) (hkq : k < q) (hq2k : q < 2 * k) :
    q ∣ refinementPrimeProduct k := by
  rw [refinementPrimeProduct, sievePrimeProduct]
  exact Finset.dvd_prod_of_mem id
    (mem_sievePrimes.mpr ⟨hq, hkq, hq2k⟩)

/-- The natural CRT representative which is in the public class modulo
`N_k` and is congruent to `k` modulo every prime in `(k, 2k)`. -/
noncomputable def refinementResidue {B K : ℕ}
    (S : BPZSection6Input B K) : ℕ :=
  progressionLocalResidue S (dvd_refl (refinementPrimeProduct S.k)) S.k

theorem refinementResidue_mod_Nk {B K : ℕ}
    (S : BPZSection6Input B K) :
    refinementResidue S ≡ progressionResidue S [MOD Nk_formula S.k] := by
  exact progressionLocalResidue_mod_Nk S
    (dvd_refl (refinementPrimeProduct S.k)) S.k

theorem refinementResidue_mod_primeProduct {B K : ℕ}
    (S : BPZSection6Input B K) :
    refinementResidue S ≡ S.k [MOD refinementPrimeProduct S.k] := by
  exact progressionLocalResidue_mod_local S
    (dvd_refl (refinementPrimeProduct S.k)) S.k

/-- Refine a Section 6 input by the finite CRT condition
`n ≡ k (mod ∏_{k<p<2k} p)`. -/
noncomputable def BPZSection6Input.refine {B K : ℕ}
    (S : BPZSection6Input B K) : BPZSection6InputRefined B K where
  toBPZSection6Input := S
  M := Nk_formula S.k * refinementPrimeProduct S.k
  γ := refinementResidue S
  M_pos := Nat.mul_pos (Nk_formula_pos S.k)
    (refinementPrimeProduct_pos S.k)
  Nk_dvd_M := dvd_mul_right _ _
  primes_dvd_M := by
    intro q hq hkq hq2k
    exact dvd_mul_of_dvd_right
      (prime_dvd_refinementPrimeProduct hq hkq hq2k) _
  refined := by
    intro n hn hM
    have hn0 : 0 ≤ n := by
      have hk0 : (0 : ℤ) ≤ S.k := by positivity
      omega
    have hnCast : (n.toNat : ℤ) = n := Int.toNat_of_nonneg hn0
    have hkn : S.k < n.toNat := by
      exact_mod_cast (show (S.k : ℤ) < (n.toNat : ℤ) by simpa [hnCast])
    have hmodM : n.toNat ≡ refinementResidue S
        [MOD Nk_formula S.k * refinementPrimeProduct S.k] := by
      apply Int.natCast_modEq_iff.mp
      have hz : n ≡ (refinementResidue S : ℤ)
          [ZMOD (Nk_formula S.k * refinementPrimeProduct S.k : ℕ)] :=
        (Int.modEq_iff_dvd.mpr hM).symm
      simpa [hnCast] using hz
    have hmodNk : n.toNat ≡ progressionResidue S
        [MOD Nk_formula S.k] :=
      (hmodM.of_mul_right (refinementPrimeProduct S.k)).trans
        (refinementResidue_mod_Nk S)
    have hprogNat : (Nk_formula S.k : ℤ) ∣
        (n.toNat : ℤ) - S.α :=
      (progression_dvd_iff_modEq S).mpr hmodNk
    have hprog : (Nk_formula S.k : ℤ) ∣ n - S.α := by
      simpa [hnCast] using hprogNat
    have hdata := S.progression n hn hprog
    refine ⟨?_, ?_⟩
    · intro p hp hp2k
      by_cases hpk : p ≤ S.k
      · exact hdata.2.1 p hp hpk
      · have hkp : S.k < p := Nat.lt_of_not_ge hpk
        have hmodProduct : n.toNat ≡ S.k
            [MOD refinementPrimeProduct S.k] :=
          (hmodM.of_mul_left (Nk_formula S.k)).trans
            (refinementResidue_mod_primeProduct S)
        have hpProduct : p ∣ refinementPrimeProduct S.k :=
          prime_dvd_refinementPrimeProduct hp hkp hp2k
        have hmodp : n.toNat ≡ S.k [MOD p] :=
          hmodProduct.of_dvd hpProduct
        have hnmod : n.toNat % p = S.k :=
          Nat.mod_eq_of_modEq hmodp hkp
        have hnotNat : ¬p ∣ n.toNat.choose S.k := by
          intro hpChoose
          obtain ⟨i, hi, hei⟩ :=
            (prime_dvd_choose_iff_exists_mod_eq hp hkp hkn.le).mp hpChoose
          omega
        intro hpChoose
        apply hnotNat
        exact_mod_cast hpChoose
    · intro i j hij
      have hpair := S.coverQuotients_pairwise_coprime hkn hprogNat
        i.val i.isLt j.val j.isLt (fun h => hij (Fin.ext h))
      simpa [BPZSection6Input.toCoverFactorization,
        BPZSection6Input.gNat, i.isLt, j.isLt] using hpair

/-- The fully unconditional refined input, with arbitrarily large `k`. -/
theorem unconditional_fixed_B_cover_section6_input_refined
    (B K : ℕ) (hB : 3 ≤ B) :
    ∃ _S : BPZSection6InputRefined B K, True := by
  obtain ⟨S, -⟩ := unconditional_fixed_B_cover_section6_input B K hB
  exact ⟨S.refine, trivial⟩

end CoverBPZ

end Erdos387
