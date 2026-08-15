/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos387.CoverAlgebra
import ErdosProblems.Erdos387.CoverBPZConditional

/-!
# Bridge from the public BPZ cover to the divisor-analysis interface

This file converts `BPZSection6Input` into the elementary
`CoverFactorization` consumed by the final Erdős 387 reduction.
-/

namespace Erdos387

open scoped BigOperators

namespace CoverBPZ.BPZSection6Input

/-- Extend the finite family of covering denominators by `1` outside its
natural range. -/
def gNat {B K : ℕ} (S : CoverBPZ.BPZSection6Input B K) (i : ℕ) : ℕ :=
  if hi : i < S.k then S.g ⟨i, hi⟩ else 1

theorem gNat_eq {B K : ℕ} (S : CoverBPZ.BPZSection6Input B K)
    {i : ℕ} (hi : i < S.k) : S.gNat i = S.g ⟨i, hi⟩ := by
  simp [gNat, hi]

/-- Every natural member of the certified progression yields exactly the
factorization data used by `choose_eq_prod_coverQuotients`. -/
noncomputable def toCoverFactorization {B K n : ℕ}
    (S : CoverBPZ.BPZSection6Input B K) (hn : S.k < n)
    (hprog : (CoverBPZ.Nk_formula S.k : ℤ) ∣ (n : ℤ) - S.α) :
    CoverFactorization n S.k where
  g := S.gNat
  divides_term := by
    intro i hi
    have hdata := S.progression (n : ℤ) (by exact_mod_cast hn) hprog
    have hdivZ := hdata.1 ⟨i, hi⟩
    have hin : i ≤ n := (Nat.le_of_lt hi).trans hn.le
    have hcastSub : ((n - i : ℕ) : ℤ) = (n : ℤ) - (i : ℤ) := by
      exact Nat.cast_sub hin
    have hdivZ' : (S.g ⟨i, hi⟩ : ℤ) ∣ ((n - i : ℕ) : ℤ) := by
      rwa [hcastSub]
    rw [S.gNat_eq hi]
    exact_mod_cast hdivZ'
  product_eq_factorial := by
    rw [← Fin.prod_univ_eq_prod_range S.gNat S.k]
    simpa [gNat] using S.g_prod_factorial

theorem coverQuotient_ge_B {B K n : ℕ}
    (S : CoverBPZ.BPZSection6Input B K) (hn : S.k < n)
    (hprog : (CoverBPZ.Nk_formula S.k : ℤ) ∣ (n : ℤ) - S.α)
    {i : ℕ} (hi : i < S.k) :
    B ≤ (S.toCoverFactorization hn hprog).g i := by
  change B ≤ S.gNat i
  rw [S.gNat_eq hi]
  exact S.g_ge_B ⟨i, hi⟩

/-- The public certificate's small-prime exclusion is exactly the exclusion
needed for each residual factor in `CoverFactorization`. -/
theorem no_prime_le_k_dvd_coverQuotient {B K n : ℕ}
    (S : CoverBPZ.BPZSection6Input B K) (hn : S.k < n)
    (hprog : (CoverBPZ.Nk_formula S.k : ℤ) ∣ (n : ℤ) - S.α)
    {i p : ℕ} (hi : i < S.k) (hp : p.Prime) (hpk : p ≤ S.k) :
    ¬p ∣ (n - i) / (S.toCoverFactorization hn hprog).g i := by
  have hdata := S.progression (n : ℤ) (by exact_mod_cast hn) hprog
  have hsmall := hdata.2.2 ⟨i, hi⟩ p hp hpk
  change ¬p ∣ (n - i) / S.gNat i
  simpa [S.gNat_eq hi] using hsmall

/-- No prime at most `k` divides the binomial coefficient on the certified
progression. -/
theorem no_prime_le_k_dvd_choose {B K n : ℕ}
    (S : CoverBPZ.BPZSection6Input B K) (hn : S.k < n)
    (hprog : (CoverBPZ.Nk_formula S.k : ℤ) ∣ (n : ℤ) - S.α)
    {p : ℕ} (hp : p.Prime) (hpk : p ≤ S.k) :
    ¬p ∣ n.choose S.k := by
  intro hpChoose
  have hprod :
      p ∣ ∏ i ∈ Finset.range S.k,
        (n - i) / (S.toCoverFactorization hn hprog).g i := by
    rwa [← choose_eq_prod_coverQuotients
      (S.toCoverFactorization hn hprog)]
  obtain ⟨i, hi, hpi⟩ :=
    (hp.prime.dvd_finsetProd_iff
      (fun i => (n - i) / (S.toCoverFactorization hn hprog).g i)).mp hprod
  exact S.no_prime_le_k_dvd_coverQuotient hn hprog
    (Finset.mem_range.mp hi) hp hpk hpi

/-- Residual factors belonging to distinct shifts are pairwise coprime. -/
theorem coverQuotients_pairwise_coprime {B K n : ℕ}
    (S : CoverBPZ.BPZSection6Input B K) (hn : S.k < n)
    (hprog : (CoverBPZ.Nk_formula S.k : ℤ) ∣ (n : ℤ) - S.α) :
    ∀ i < S.k, ∀ j < S.k, i ≠ j →
      Nat.Coprime
        ((n - i) / (S.toCoverFactorization hn hprog).g i)
        ((n - j) / (S.toCoverFactorization hn hprog).g j) := by
  apply Erdos387.coverQuotients_pairwise_coprime
    (S.toCoverFactorization hn hprog) hn.le
  intro i hi p hp hpdiv
  have hnlt : ¬p < S.k := by
    intro hpk
    exact S.no_prime_le_k_dvd_coverQuotient hn hprog hi hp hpk.le hpdiv
  omega

/-- Each individual residual is at most `n / B`, the easy part of the
divisor-interval exclusion. -/
theorem coverQuotient_le_div {B K n : ℕ}
    (S : CoverBPZ.BPZSection6Input B K) (hB : 0 < B) (hn : S.k < n)
    (hprog : (CoverBPZ.Nk_formula S.k : ℤ) ∣ (n : ℤ) - S.α)
    {i : ℕ} (hi : i < S.k) :
    (n - i) / (S.toCoverFactorization hn hprog).g i ≤ n / B := by
  exact Erdos387.coverQuotient_le_div
    (S.toCoverFactorization hn hprog) hB
    (S.coverQuotient_ge_B hn hprog hi) hi

end CoverBPZ.BPZSection6Input

end Erdos387
