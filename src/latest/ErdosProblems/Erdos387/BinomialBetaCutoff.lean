/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos387.BinomialEulerProduct
import ErdosProblems.Erdos387.GeneralBetaMainTerm

/-!
# The binomial density on variable-beta cutoff prefixes

This is the analytic adapter between the endpoint-independent dimension
bound for `k/p` and the cutoff-prefix hypothesis of `GeneralBetaMainTerm`.
With beta `100*k`, a dimension-`k` cutoff loss fits inside the effective
dimension two tail already formalized for the beta sieve.
-/

namespace Erdos387.BinomialBetaCutoff

open scoped BigOperators
open Erdos387
open Erdos851
open Erdos851.FiniteCombinatorialSieve
open Erdos851.BetaSieveFundamental
open Erdos387.GeneralBetaChainRatio
open Erdos387.GeneralBetaCutoff
open Erdos387.GeneralBetaInflation
open Erdos387.BinomialEulerProduct

private theorem two_mul_lt_prime_of_sub_one_lt
    {k p : ℕ} (hk : 2 ≤ k) (hp : p.Prime) (h : 2 * k - 1 < p) :
    2 * k < p := by
  have hle : 2 * k ≤ p := by omega
  rcases hle.eq_or_lt with heq | hlt
  · rcases hp.eq_two_or_odd with hp2 | hpodd
    · omega
    · exact (Nat.not_even_iff_odd.mpr (Nat.odd_iff.mpr hpodd))
        (heq ▸ even_two_mul k) |>.elim
  · exact hlt

private theorem getLast_le_of_pairwise_desc :
    ∀ {l : List ℕ} (hn : l ≠ []),
      l.Pairwise (fun p q ↦ q < p) →
      ∀ p ∈ l, l.getLast hn ≤ p := by
  intro l hn hdesc
  induction l with
  | nil => contradiction
  | cons a l ih =>
      cases l with
      | nil => simp
      | cons b l =>
          intro p hp
          simp only [List.mem_cons] at hp
          rcases hp with rfl | hp
          · have htail := (List.pairwise_cons.mp hdesc).1
                ((b :: l).getLast (by simp)) (List.getLast_mem (by simp))
            simpa using htail.le
          · have htaildesc := (List.pairwise_cons.mp hdesc).2
            simpa using ih (by simp) htaildesc p (by simpa using hp)

/-- A finite decreasing prime prefix costs at most its smallest local factor
times the inverse Euler product above that smallest prime. -/
private theorem inverse_buchstabProduct_le_two_mul_inverseLocalEulerProduct
    {k : ℕ} {Q : List ℕ} {q y : ℕ}
    (hk : 1 ≤ k) (hQnodup : Q.Nodup) (hqmem : q ∈ Q)
    (hqmin : ∀ p ∈ Q, q ≤ p)
    (hQprime : ∀ p ∈ Q, p.Prime)
    (hQupper : ∀ p ∈ Q, p ≤ y)
    (hqlarge : 2 * k < q) :
    (buchstabProduct (fun p ↦ binomialSieveNu k p) Q)⁻¹ ≤
      2 * inverseLocalEulerProduct (fun p ↦ binomialSieveNu k p) q y := by
  classical
  let F := Q.toFinset
  let T := insert q (Erdos851.sievePrimes q y)
  let invFactor : ℕ → ℝ := fun p ↦ (1 - binomialSieveNu k p)⁻¹
  have hFsub : F ⊆ T := by
    intro p hp
    have hpQ : p ∈ Q := List.mem_toFinset.mp hp
    by_cases hpq : p = q
    · simp [T, hpq]
    · have hqp : q < p := lt_of_le_of_ne (hqmin p hpQ) (Ne.symm hpq)
      have hpS : p ∈ Erdos851.sievePrimes q y := Erdos851.mem_sievePrimes.mpr
        ⟨hqp, hQupper p hpQ, hQprime p hpQ⟩
      simp [T, hpS]
  have hlocal (p : ℕ) (hpPrime : p.Prime) (hkp : k < p) :
      0 ≤ binomialSieveNu k p ∧ binomialSieveNu k p < 1 := by
    rw [binomialSieveNu_prime hpPrime]
    constructor
    · positivity
    · rw [div_lt_one (by exact_mod_cast hpPrime.pos)]
      exact_mod_cast hkp
  have hF0 : ∀ p ∈ F, 0 ≤ invFactor p := by
    intro p hp
    have hpQ : p ∈ Q := List.mem_toFinset.mp hp
    have hkp : k < p := by
      have := hqmin p hpQ
      omega
    exact inv_nonneg.mpr (sub_nonneg.mpr (hlocal p (hQprime p hpQ) hkp).2.le)
  have hTone : ∀ p ∈ T, p ∉ F → 1 ≤ invFactor p := by
    intro p hpT _hpF
    have hpCases : p = q ∨ p ∈ Erdos851.sievePrimes q y := by
      simpa [T] using hpT
    have hpPrime : p.Prime := by
      rcases hpCases with rfl | hpS
      · exact hQprime p hqmem
      · exact (Erdos851.mem_sievePrimes.mp hpS).2.2
    have hkp : k < p := by
      rcases hpCases with rfl | hpS
      · omega
      · have := (Erdos851.mem_sievePrimes.mp hpS).1
        omega
    have hgp := hlocal p hpPrime hkp
    exact (one_le_inv₀ (sub_pos.mpr hgp.2)).2 (by linarith)
  have hprod : (∏ p ∈ F, invFactor p) ≤ ∏ p ∈ T, invFactor p :=
    Finset.prod_le_prod_of_subset_of_one_le hFsub hF0 hTone
  have hqfactor : invFactor q ≤ 2 := by
    have hqPrime := hQprime q hqmem
    have hqR : (0 : ℝ) < q := by exact_mod_cast hqPrime.pos
    have hfrac : (k : ℝ) / q < 1 / 2 := by
      rw [div_lt_iff₀ hqR]
      have : (2 : ℝ) * k < q := by exact_mod_cast hqlarge
      linarith
    dsimp [invFactor]
    rw [binomialSieveNu_prime hqPrime]
    apply (inv_le_comm₀ (by linarith : 0 < 1 - (k : ℝ) / q)
      (by norm_num : (0 : ℝ) < 2)).2
    linarith
  calc
    (buchstabProduct (fun p ↦ binomialSieveNu k p) Q)⁻¹ =
        ∏ p ∈ F, invFactor p := by
      unfold buchstabProduct invFactor F
      rw [← List.prod_toFinset
        (fun p ↦ 1 - binomialSieveNu k p) hQnodup]
      rw [← Finset.prod_inv_distrib]
    _ ≤ ∏ p ∈ T, invFactor p := hprod
    _ = invFactor q *
        inverseLocalEulerProduct (fun p ↦ binomialSieveNu k p) q y := by
      simp [T, invFactor, inverseLocalEulerProduct,
        Erdos851.mem_sievePrimes, mul_comm]
    _ ≤ 2 * inverseLocalEulerProduct
        (fun p ↦ binomialSieveNu k p) q y := by
      apply mul_le_mul_of_nonneg_right hqfactor
      unfold inverseLocalEulerProduct
      apply Finset.prod_nonneg
      intro p hp
      have hp' := Erdos851.mem_sievePrimes.mp hp
      have hkp : k < p := by omega
      exact inv_nonneg.mpr (sub_nonneg.mpr
        (hlocal p hp'.2.2 hkp).2.le)

/-- The explicit cutoff-prefix estimate consumed by
`finiteMainTerms_bounds_of_generalBetaCutoffs`. -/
theorem binomial_hundred_mul_betaCutoffPrefix_inverse_bound
    {k : ℕ} (hk : 2 ≤ k) {C : ℝ} (hC : 1 ≤ C)
    (hdimension : ∀ z y : ℕ, 2 * k ≤ z → z ≤ y →
      inverseLocalEulerProduct (fun p ↦ binomialSieveNu k p) z y ≤
        C * (Real.log (y : ℝ) / Real.log (z : ℝ)) ^ k)
    {z y r : ℕ} (hz : 2 * k - 1 ≤ z) (hzy : z ≤ y) :
    (buchstabProduct (fun p ↦ binomialSieveNu k p)
        (betaCutoffPrefix (100 * k) z y r))⁻¹ ≤
      (2 * C) * Real.rpow betaRatio (2 * r) := by
  classical
  let Q := betaCutoffPrefix (100 * k) z y r
  change (buchstabProduct (fun p ↦ binomialSieveNu k p) Q)⁻¹ ≤
    (2 * C) * Real.rpow betaRatio (2 * r)
  by_cases hQ : Q = []
  · rw [hQ]
    simp only [buchstabProduct, List.map_nil, List.prod_nil, inv_one]
    have hrpow : 1 ≤ Real.rpow betaRatio (2 * r) :=
      Real.one_le_rpow (by norm_num [betaRatio]) (by positivity)
    calc
      (1 : ℝ) ≤ 2 * C := by nlinarith
      _ ≤ (2 * C) * Real.rpow betaRatio (2 * r) := by
        simpa only [mul_one] using
          (mul_le_mul_of_nonneg_left hrpow (by positivity : 0 ≤ (2 : ℝ) * C))
  · let q := Q.getLast hQ
    have hqQ : q ∈ Q := List.getLast_mem hQ
    have hQsub : Q.Sublist (descendingSievePrimes z y) := by
      exact (betaCutoffPrefix_isPrefix (100 * k) z y r (by omega)).sublist
    have hqS := Erdos851.mem_sievePrimes.mp
      (mem_descendingSievePrimes.mp (hQsub.subset hqQ))
    have hqlarge : 2 * k < q :=
      two_mul_lt_prime_of_sub_one_lt hk hqS.2.2 (hz.trans_lt hqS.1)
    have hQdesc : Q.Pairwise (fun p q ↦ q < p) :=
      (descendingSievePrimes_pairwise z y).sublist hQsub
    have hqmin : ∀ p ∈ Q, q ≤ p :=
      getLast_le_of_pairwise_desc hQ hQdesc
    have hqEligible : betaEligible (100 * k) y r q := by
      have hqCut : q ∈ betaCutoffPrefix (100 * k) z y r := by
        simpa [Q] using hqQ
      have hqBoth : 1 < q ∧ betaEligible (100 * k) y r q := by
        simpa [GeneralBetaCutoff.betaCutoffPrefix] using
          (List.mem_filter.mp hqCut).2
      exact hqBoth.2
    have hcpos : (0 : ℝ) < inflation ((100 * k + 1 : ℕ) : ℝ) := by
      apply inflation_pos
      exact_mod_cast (show 2 < 100 * k + 1 by omega)
    have hcut : Real.log (y : ℝ) / Real.log (q : ℝ) ≤
        inflation ((100 * k + 1 : ℕ) : ℝ) ^ r := by
      change Real.log (y : ℝ) / Real.log (q : ℝ) <
        inflation ((((100 * k : ℕ) : ℝ) + 1)) ^ (r - 1) at hqEligible
      have hbaseEq : inflation ((((100 * k : ℕ) : ℝ) + 1)) =
          inflation ((100 * k + 1 : ℕ) : ℝ) := by norm_num
      rw [hbaseEq] at hqEligible
      exact hqEligible.le.trans
        (pow_le_pow_right₀ (inflation_one_le (by
          exact_mod_cast (show 2 < 100 * k + 1 by omega))) (by omega))
    have hbase := inverse_buchstabProduct_le_two_mul_inverseLocalEulerProduct
      (by omega) (hQsub.nodup (descendingSievePrimes_nodup z y)) hqQ hqmin
      (fun p hp ↦ (Erdos851.mem_sievePrimes.mp
        (mem_descendingSievePrimes.mp (hQsub.subset hp))).2.2)
      (fun p hp ↦ (Erdos851.mem_sievePrimes.mp
        (mem_descendingSievePrimes.mp (hQsub.subset hp))).2.1)
      hqlarge
    have hratio0 : 0 ≤ Real.log (y : ℝ) / Real.log (q : ℝ) := by
      exact div_nonneg
        (Real.log_nonneg (by exact_mod_cast (show 1 ≤ y by omega)))
        (Real.log_pos (by exact_mod_cast hqS.2.2.one_lt)).le
    have hpowcut :
        (Real.log (y : ℝ) / Real.log (q : ℝ)) ^ k ≤
          (inflation ((100 * k + 1 : ℕ) : ℝ) ^ r) ^ k :=
      pow_le_pow_left₀ hratio0 hcut k
    have hinfl := hundred_mul_beta_inflation_rpow_dimension_depth_le
      (k := k) (r := r) (by omega)
    calc
      (buchstabProduct (fun p ↦ binomialSieveNu k p) Q)⁻¹ ≤
          2 * inverseLocalEulerProduct
            (fun p ↦ binomialSieveNu k p) q y := hbase
      _ ≤ 2 * (C * (Real.log (y : ℝ) / Real.log (q : ℝ)) ^ k) := by
        gcongr
        exact hdimension q y hqlarge.le hqS.2.1
      _ ≤ 2 * (C *
          (inflation ((100 * k + 1 : ℕ) : ℝ) ^ r) ^ k) := by
        gcongr
      _ = (2 * C) * Real.rpow
          (inflation ((100 * k + 1 : ℕ) : ℝ)) ((k : ℝ) * r) := by
        have hrpow : Real.rpow (inflation ((100 * k + 1 : ℕ) : ℝ))
            (((k * r : ℕ) : ℝ)) =
            inflation ((100 * k + 1 : ℕ) : ℝ) ^ (k * r) :=
          Real.rpow_natCast _ _
        rw [show (k : ℝ) * (r : ℝ) = ((k * r : ℕ) : ℝ) by norm_num,
          hrpow, pow_mul]
        ring
      _ ≤ (2 * C) * Real.rpow betaRatio ((2 : ℝ) * r) := by
        exact mul_le_mul_of_nonneg_left hinfl (by positivity)
      _ = (2 * C) * Real.rpow betaRatio (2 * r) := by norm_num

/-- There is a cutoff constant, depending only on `k`, which supplies all
depth-product hypotheses for beta `100*k`. -/
theorem exists_binomial_hundred_mul_cutoff_bound (k : ℕ) (hk : 2 ≤ k) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ z y r : ℕ, 2 * k - 1 ≤ z → z ≤ y →
      (buchstabProduct (fun p ↦ binomialSieveNu k p)
        (betaCutoffPrefix (100 * k) z y r))⁻¹ ≤
          A * Real.rpow betaRatio (2 * r) := by
  obtain ⟨C, hC, hdimension⟩ := exists_binomial_dimension_bound k (by omega)
  refine ⟨2 * C, by nlinarith, ?_⟩
  intro z y r hz hzy
  exact binomial_hundred_mul_betaCutoffPrefix_inverse_bound
    hk hC hdimension hz hzy

/-- Fully instantiated lower and upper Rosser main-term windows.  The sole
remaining numerical condition says that the forced starting depth is large
enough compared with the fixed constant `A(k)`; it is independent of both
Euler-product endpoints. -/
theorem exists_binomial_hundred_mul_mainTerm_bounds
    (k : ℕ) (hk : 2 ≤ k) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ z y S : ℕ,
      2 * k - 1 ≤ z → z ≤ y → 100 * k + 1 ≤ S →
      Real.log A ≤ 4 * (S - 100 * k : ℕ) / 99 →
      let P := (descendingSievePrimes z y).reverse
      let eta := (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100 * k)
      (1 - eta) * finiteEulerProduct
          (fun p ↦ binomialSieveNu k p) P ≤
          lowerMainTerm (rosserStoppingPredicate (100 * k) (y ^ S))
            (fun p ↦ binomialSieveNu k p) P ∧
        upperMainTerm (rosserStoppingPredicate (100 * k) (y ^ S))
            (fun p ↦ binomialSieveNu k p) P ≤
          (1 + eta) * finiteEulerProduct
            (fun p ↦ binomialSieveNu k p) P := by
  obtain ⟨A, hA, hcutoff⟩ := exists_binomial_hundred_mul_cutoff_bound k hk
  refine ⟨A, hA, ?_⟩
  intro z y S hz hzy hS hlog
  have hy : 1 < y := by omega
  apply Erdos387.GeneralBetaMainTerm.finiteMainTerms_bounds_of_generalBetaCutoffs
    (g := fun p ↦ binomialSieveNu k p) (beta := 100 * k)
    (z := z) (y := y) (S := S) (A := A)
  · omega
  · exact hS
  · exact hy
  · intro p
    by_cases hp0 : p = 0
    · subst p
      simp [binomialSieveNu, ArithmeticFunction.prodPrimeFactors]
    · rw [binomialSieveNu,
        ArithmeticFunction.prodPrimeFactors_apply hp0]
      apply Finset.prod_nonneg
      intro q hq
      positivity
  · intro p hp
    have hp' := Erdos851.mem_sievePrimes.mp
      (mem_descendingSievePrimes.mp hp)
    rw [binomialSieveNu_prime hp'.2.2]
    rw [div_lt_one (by exact_mod_cast hp'.2.2.pos)]
    exact_mod_cast (show k < p by omega)
  · exact hA
  · intro r _hr _hstart
    exact hcutoff z y r hz hzy
  · intro r hstart _hr
    have hcast : ((S - 100 * k : ℕ) : ℝ) ≤ r := by exact_mod_cast hstart
    calc
      Real.log A ≤ 4 * (S - 100 * k : ℕ) / 99 := hlog
      _ ≤ 4 * r / 99 := by gcongr

/-- The logarithmic start condition is automatic beyond one fixed depth
`T₀(k)`.  This form has no analytic hypothesis left at the point of use. -/
theorem exists_binomial_hundred_mul_mainTerm_bounds_eventually_depth
    (k : ℕ) (hk : 2 ≤ k) :
    ∃ A : ℝ, ∃ T₀ : ℕ, 1 ≤ A ∧ 100 * k + 1 ≤ T₀ ∧
      ∀ z y S : ℕ,
        2 * k - 1 ≤ z → z ≤ y → T₀ ≤ S →
        let P := (descendingSievePrimes z y).reverse
        let eta := (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100 * k)
        (1 - eta) * finiteEulerProduct
            (fun p ↦ binomialSieveNu k p) P ≤
            lowerMainTerm (rosserStoppingPredicate (100 * k) (y ^ S))
              (fun p ↦ binomialSieveNu k p) P ∧
          upperMainTerm (rosserStoppingPredicate (100 * k) (y ^ S))
              (fun p ↦ binomialSieveNu k p) P ≤
            (1 + eta) * finiteEulerProduct
              (fun p ↦ binomialSieveNu k p) P := by
  obtain ⟨A, hA, hmain⟩ := exists_binomial_hundred_mul_mainTerm_bounds k hk
  obtain ⟨n, hn⟩ := exists_nat_ge ((99 / 4 : ℝ) * Real.log A + 1)
  refine ⟨A, 100 * k + n, hA, ?_, ?_⟩
  · have hlog0 : 0 ≤ Real.log A := Real.log_nonneg hA
    have hn1R : (1 : ℝ) ≤ n := by nlinarith
    have hn1 : 1 ≤ n := by exact_mod_cast hn1R
    omega
  · intro z y S hz hzy hS
    have hT : 100 * k + 1 ≤ S := by
      have hlog0 : 0 ≤ Real.log A := Real.log_nonneg hA
      have hn1R : (1 : ℝ) ≤ n := by nlinarith
      have hn1 : 1 ≤ n := by exact_mod_cast hn1R
      omega
    have hdiff : n ≤ S - 100 * k := by omega
    have hnR : (n : ℝ) ≤ ((S - 100 * k : ℕ) : ℝ) := by
      exact_mod_cast hdiff
    have hlog : Real.log A ≤ 4 * (S - 100 * k : ℕ) / 99 := by
      calc
        Real.log A ≤ 4 * (n : ℝ) / 99 := by nlinarith
        _ ≤ 4 * (S - 100 * k : ℕ) / 99 := by gcongr
    exact hmain z y S hz hzy hT hlog

end Erdos387.BinomialBetaCutoff
