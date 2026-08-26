/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos946.DimensionEightBeta
import ErdosProblems.Erdos946.DimensionSixteenSharp
import ErdosProblems.Erdos387.BinomialEulerProductSharp
import ErdosProblems.Erdos387.SieveInstantiation
import ErdosProblems.Erdos387.GeneralBetaCutoff

/-!
# A beta-200 fundamental-lemma window in dimension sixteen

At beta `200`, one depth of the dimension-seventeen Euler-product majorant
is bounded by nine powers of the beta-100 comparison ratio.  Consequently
the numerical tail already proved in `DimensionEightBeta` applies without
change.  This file packages that observation for the sixteen-form version
of the Heath--Brown construction used in Erdős 946.
-/

namespace Erdos946.DimensionSixteenBeta

open Erdos851
open Erdos387
open Erdos851.FiniteCombinatorialSieve
open Erdos851.BetaSieveFundamental
open Erdos387.GeneralBetaChainRatio
open Erdos387.GeneralBetaCutoff
open Erdos387.BinomialEulerProductSharp
open List

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

/-- A decreasing prime prefix costs at most its smallest local factor and
the full inverse Euler product above that prime. -/
private theorem inverse_buchstabProduct_le_two_mul_inverseLocalEulerProduct
    {Q : List ℕ} {q y : ℕ}
    (hQnodup : Q.Nodup) (hqmem : q ∈ Q)
    (hqmin : ∀ p ∈ Q, q ≤ p)
    (hQprime : ∀ p ∈ Q, p.Prime)
    (hQupper : ∀ p ∈ Q, p ≤ y)
    (hqlarge : 32 < q) :
    (buchstabProduct (fun p ↦ binomialSieveNu 16 p) Q)⁻¹ ≤
      2 * inverseLocalEulerProduct (fun p ↦ binomialSieveNu 16 p) q y := by
  classical
  let F := Q.toFinset
  let T := insert q (Erdos851.sievePrimes q y)
  let invFactor : ℕ → ℝ := fun p ↦ (1 - binomialSieveNu 16 p)⁻¹
  have hlocal (p : ℕ) (hpPrime : p.Prime) (hkp : 16 < p) :
      0 ≤ binomialSieveNu 16 p ∧ binomialSieveNu 16 p < 1 := by
    rw [binomialSieveNu_prime hpPrime]
    constructor
    · positivity
    · rw [div_lt_one (by exact_mod_cast hpPrime.pos)]
      exact_mod_cast hkp
  have hFsub : F ⊆ T := by
    intro p hp
    have hpQ : p ∈ Q := List.mem_toFinset.mp hp
    by_cases hpq : p = q
    · simp [T, hpq]
    · have hqp : q < p := lt_of_le_of_ne (hqmin p hpQ) (Ne.symm hpq)
      have hpS : p ∈ Erdos851.sievePrimes q y := Erdos851.mem_sievePrimes.mpr
        ⟨hqp, hQupper p hpQ, hQprime p hpQ⟩
      simp [T, hpS]
  have hF0 : ∀ p ∈ F, 0 ≤ invFactor p := by
    intro p hp
    have hpQ : p ∈ Q := List.mem_toFinset.mp hp
    have hpq := hqmin p hpQ
    have hkp : 16 < p := by omega
    exact inv_nonneg.mpr (sub_nonneg.mpr
      (hlocal p (hQprime p hpQ) hkp).2.le)
  have hTone : ∀ p ∈ T, p ∉ F → 1 ≤ invFactor p := by
    intro p hpT _hpF
    have hpCases : p = q ∨ p ∈ Erdos851.sievePrimes q y := by
      simpa [T] using hpT
    have hpPrime : p.Prime := by
      rcases hpCases with rfl | hpS
      · exact hQprime p hqmem
      · exact (Erdos851.mem_sievePrimes.mp hpS).2.2
    have hkp : 16 < p := by
      rcases hpCases with rfl | hpS
      · omega
      · have := (Erdos851.mem_sievePrimes.mp hpS).1
        omega
    have hgp := hlocal p hpPrime hkp
    have hdenpos : 0 < 1 - binomialSieveNu 16 p := sub_pos.mpr hgp.2
    have hdenle : 1 - binomialSieveNu 16 p ≤ 1 := by linarith
    exact (one_le_inv₀ hdenpos).2 hdenle
  have hprod : (∏ p ∈ F, invFactor p) ≤ ∏ p ∈ T, invFactor p :=
    Finset.prod_le_prod_of_subset_of_one_le hFsub hF0 hTone
  have hqfactor : invFactor q ≤ 2 := by
    have hqPrime := hQprime q hqmem
    have hqR : (0 : ℝ) < q := by exact_mod_cast hqPrime.pos
    have hfrac : (16 : ℝ) / q < 1 / 2 := by
      rw [div_lt_iff₀ hqR]
      have hqR32 : (32 : ℝ) < q := by exact_mod_cast hqlarge
      linarith
    dsimp [invFactor]
    rw [binomialSieveNu_prime hqPrime]
    apply (inv_le_comm₀ (by linarith : 0 < 1 - (16 : ℝ) / q)
      (by norm_num : (0 : ℝ) < 2)).2
    linarith
  calc
    (buchstabProduct (fun p ↦ binomialSieveNu 16 p) Q)⁻¹ =
        ∏ p ∈ F, invFactor p := by
      unfold buchstabProduct invFactor F
      rw [← List.prod_toFinset
        (fun p ↦ 1 - binomialSieveNu 16 p) hQnodup]
      rw [← Finset.prod_inv_distrib]
    _ ≤ ∏ p ∈ T, invFactor p := hprod
    _ = invFactor q *
        inverseLocalEulerProduct (fun p ↦ binomialSieveNu 16 p) q y := by
      simp [T, invFactor, inverseLocalEulerProduct,
        Erdos851.mem_sievePrimes, mul_comm]
    _ ≤ 2 * inverseLocalEulerProduct
        (fun p ↦ binomialSieveNu 16 p) q y := by
      apply mul_le_mul_of_nonneg_right hqfactor
      unfold inverseLocalEulerProduct
      apply Finset.prod_nonneg
      intro p hp
      have hp' := Erdos851.mem_sievePrimes.mp hp
      exact inv_nonneg.mpr (sub_nonneg.mpr
        (hlocal p hp'.2.2 (by omega)).2.le)

/-- The exact rational comparison which is responsible for choosing beta
`200`: seventeen powers of `(201/199)` fit under nine powers of `(101/99)`. -/
theorem inflation_twoHundred_pow_seventeen_le_betaRatio_pow_nine :
    Real.rpow (inflation (201 : ℝ)) (17 : ℝ) ≤
      Real.rpow betaRatio (9 : ℝ) := by
  calc
    Real.rpow (inflation (201 : ℝ)) (17 : ℝ) =
        inflation (201 : ℝ) ^ (17 : ℕ) := Real.rpow_natCast _ _
    _ ≤ betaRatio ^ (9 : ℕ) := by norm_num [inflation, betaRatio]
    _ = Real.rpow betaRatio (9 : ℝ) := (Real.rpow_natCast _ _).symm

theorem inflation_twoHundred_dimension_depth_le (r : ℕ) :
    Real.rpow (inflation (201 : ℝ)) ((17 : ℝ) * r) ≤
      Real.rpow betaRatio ((9 : ℝ) * r) := by
  have hpos : 0 ≤ inflation (201 : ℝ) := (inflation_pos (by norm_num)).le
  calc
    Real.rpow (inflation (201 : ℝ)) ((17 : ℝ) * r) =
        (Real.rpow (inflation (201 : ℝ)) (17 : ℝ)) ^ r :=
      Real.rpow_mul_natCast hpos (17 : ℝ) r
    _ ≤ (Real.rpow betaRatio (9 : ℝ)) ^ r :=
      pow_le_pow_left₀ (Real.rpow_nonneg hpos _)
        inflation_twoHundred_pow_seventeen_le_betaRatio_pow_nine r
    _ = Real.rpow betaRatio ((9 : ℝ) * r) :=
      (Real.rpow_mul_natCast (by norm_num [betaRatio]) (9 : ℝ) r).symm

/-- Product-ratio estimate on the beta-200 cutoff prefix. -/
theorem sixteen_betaCutoffPrefix_inverse_bound
    {C : ℝ} (hC : 1 ≤ C) {z₀ : ℕ}
    (hdimension : ∀ z y : ℕ, z₀ ≤ z → z ≤ y →
      inverseLocalEulerProduct (fun p ↦ binomialSieveNu 16 p) z y ≤
        C * (Real.log (y : ℝ) / Real.log (z : ℝ)) ^ 17)
    {z y r : ℕ} (hz₀ : z₀ ≤ z) (hz : 271 ≤ z) (hzy : z ≤ y) :
    (buchstabProduct (fun p ↦ binomialSieveNu 16 p)
        (betaCutoffPrefix 200 z y r))⁻¹ ≤
      (2 * C) * Real.rpow betaRatio ((9 : ℝ) * r) := by
  classical
  let Q := betaCutoffPrefix 200 z y r
  change (buchstabProduct (fun p ↦ binomialSieveNu 16 p) Q)⁻¹ ≤ _
  by_cases hQ : Q = []
  · rw [hQ]
    simp only [buchstabProduct, List.map_nil, List.prod_nil, inv_one]
    have hrpow : 1 ≤ Real.rpow betaRatio ((9 : ℝ) * r) :=
      Real.one_le_rpow (by norm_num [betaRatio]) (by positivity)
    calc
      (1 : ℝ) ≤ 2 * C := by nlinarith
      _ ≤ (2 * C) * Real.rpow betaRatio ((9 : ℝ) * r) := by
        simpa only [mul_one] using
          mul_le_mul_of_nonneg_left hrpow (by positivity : 0 ≤ (2 : ℝ) * C)
  · let q := Q.getLast hQ
    have hqQ : q ∈ Q := List.getLast_mem hQ
    have hQsub : Q.Sublist (descendingSievePrimes z y) :=
      (betaCutoffPrefix_isPrefix 200 z y r (by omega)).sublist
    have hqS := Erdos851.mem_sievePrimes.mp
      (mem_descendingSievePrimes.mp (hQsub.subset hqQ))
    have hqlarge : 32 < q := by
      have hle : 32 ≤ q := by omega
      rcases hle.eq_or_lt with heq | hlt
      · have := hqS.2.2
        rw [← heq] at this
        norm_num at this
      · exact hlt
    have hQdesc : Q.Pairwise (fun p q ↦ q < p) :=
      (descendingSievePrimes_pairwise z y).sublist hQsub
    have hqmin : ∀ p ∈ Q, q ≤ p :=
      getLast_le_of_pairwise_desc hQ hQdesc
    have hqEligible : betaEligible 200 y r q := by
      have hqCut : q ∈ betaCutoffPrefix 200 z y r := by simpa [Q] using hqQ
      simp only [Erdos387.GeneralBetaCutoff.betaCutoffPrefix,
        List.mem_filter, decide_eq_true_eq] at hqCut
      exact hqCut.2.2
    have hcut : Real.log (y : ℝ) / Real.log (q : ℝ) ≤
        inflation (201 : ℝ) ^ r := by
      unfold Erdos387.GeneralBetaCutoff.betaEligible at hqEligible
      have hqEligible' : Real.log (y : ℝ) / Real.log (q : ℝ) <
          inflation (201 : ℝ) ^ (r - 1) := by
        norm_num at hqEligible ⊢
        exact hqEligible
      exact hqEligible'.le.trans
        (pow_le_pow_right₀ (inflation_one_le (by norm_num)) (by omega))
    have hbase := inverse_buchstabProduct_le_two_mul_inverseLocalEulerProduct
      (Q := Q) (q := q) (y := y)
      (hQsub.nodup (descendingSievePrimes_nodup z y)) hqQ hqmin
      (fun p hp ↦ (Erdos851.mem_sievePrimes.mp
        (mem_descendingSievePrimes.mp (hQsub.subset hp))).2.2)
      (fun p hp ↦ (Erdos851.mem_sievePrimes.mp
        (mem_descendingSievePrimes.mp (hQsub.subset hp))).2.1)
      hqlarge
    have hratio0 : 0 ≤ Real.log (y : ℝ) / Real.log (q : ℝ) :=
      div_nonneg
        (Real.log_nonneg (by exact_mod_cast (show 1 ≤ y by omega)))
        (Real.log_pos (by exact_mod_cast hqS.2.2.one_lt)).le
    have hpowcut :
        (Real.log (y : ℝ) / Real.log (q : ℝ)) ^ 17 ≤
          (inflation (201 : ℝ) ^ r) ^ 17 :=
      pow_le_pow_left₀ hratio0 hcut 17
    calc
      (buchstabProduct (fun p ↦ binomialSieveNu 16 p) Q)⁻¹ ≤
          2 * inverseLocalEulerProduct
            (fun p ↦ binomialSieveNu 16 p) q y := hbase
      _ ≤ 2 * (C * (Real.log (y : ℝ) / Real.log (q : ℝ)) ^ 17) := by
        gcongr
        exact hdimension q y (hz₀.trans (Nat.le_of_lt hqS.1)) hqS.2.1
      _ ≤ 2 * (C * (inflation (201 : ℝ) ^ r) ^ 17) := by gcongr
      _ = (2 * C) * Real.rpow (inflation (201 : ℝ)) ((17 : ℝ) * r) := by
        have hrpow : Real.rpow (inflation (201 : ℝ)) ((17 : ℝ) * r) =
            inflation (201 : ℝ) ^ (17 * r : ℕ) := by
          convert Real.rpow_natCast (inflation (201 : ℝ)) (17 * r) using 1 <;>
            norm_num
        rw [hrpow]
        rw [Nat.mul_comm, pow_mul]
        ring
      _ ≤ (2 * C) * Real.rpow betaRatio ((9 : ℝ) * r) := by
        gcongr
        exact inflation_twoHundred_dimension_depth_le r

/-- The beta-200 lower and upper main-term window for the density `16/p`.
The only size hypothesis is the explicit logarithmic condition on `2*C`. -/
theorem finiteMainTerms_bounds_twoHundred_sixteen
    {C : ℝ} (hC : 1 ≤ C) {z₀ : ℕ}
    (hdimension : ∀ z y : ℕ, z₀ ≤ z → z ≤ y →
      inverseLocalEulerProduct (fun p ↦ binomialSieveNu 16 p) z y ≤
        C * (Real.log (y : ℝ) / Real.log (z : ℝ)) ^ 17)
    {z y S : ℕ} (hz₀ : z₀ ≤ z) (hz : 271 ≤ z) (hzy : z ≤ y)
    (hS : 201 ≤ S)
    (hlog : Real.log (2 * C) ≤ 9 * (S - 200 : ℕ) / 99) :
    let P := (descendingSievePrimes z y).reverse
    let eta := 10 * (2 * C) * (9 / 10 : ℝ) ^ (S - 200)
    (1 - eta) * finiteEulerProduct
        (fun p ↦ binomialSieveNu 16 p) P ≤
        lowerMainTerm (rosserStoppingPredicate 200 (y ^ S))
          (fun p ↦ binomialSieveNu 16 p) P ∧
      upperMainTerm (rosserStoppingPredicate 200 (y ^ S))
          (fun p ↦ binomialSieveNu 16 p) P ≤
        (1 + eta) * finiteEulerProduct
          (fun p ↦ binomialSieveNu 16 p) P := by
  classical
  dsimp only
  let P := (descendingSievePrimes z y).reverse
  let stop : List ℕ → Prop := rosserStoppingPredicate 200 (y ^ S)
  letI : DecidablePred stop := Classical.decPred stop
  have hstop : (fun s : List ℕ => decide (stop s.reverse)) =
      descendingRosserStop 200 (y ^ S) := by
    funext s
    unfold descendingRosserStop descendingRosserStoppingPredicate
    exact decide_eq_decide.mpr Iff.rfl
  apply Erdos946.DimensionEightBeta.finiteMainTerms_bounds_of_prefixProductRatio_eight
    stop (fun p ↦ binomialSieveNu 16 p) P
    (fun r => betaCutoffPrefix 200 z y r)
    (fun r => betaCutoffPrefix 200 z y r)
    (A := 2 * C) (κ := 9) (start := S - 200)
  · intro p
    by_cases hp0 : p = 0
    · subst p
      simp [binomialSieveNu, ArithmeticFunction.prodPrimeFactors]
    · rw [binomialSieveNu, ArithmeticFunction.prodPrimeFactors_apply hp0]
      apply Finset.prod_nonneg
      intro q hq
      positivity
  · intro p hp
    have hp' := Erdos851.mem_sievePrimes.mp
      (mem_descendingSievePrimes.mp (by simpa [P] using hp))
    rw [binomialSieveNu_prime hp'.2.2]
    rw [div_lt_one (by exact_mod_cast hp'.2.2.pos)]
    exact_mod_cast (show 16 < p by omega)
  · simp [P, descendingSievePrimes_nodup]
  · intro r hr
    simpa [P] using betaCutoffPrefix_isPrefix 200 z y r (by omega)
  · intro r hr
    simpa [P] using betaCutoffPrefix_isPrefix 200 z y r (by omega)
  · intro r hr t ht hlen
    rw [hstop] at ht
    have ht' : t ∈ upperFailureTerms (descendingRosserStop 200 (y ^ S))
        P.length [] (descendingSievePrimes z y) := by simpa [P] using ht
    simpa [P] using upperFailureTerm_chain_sublist_betaCutoffPrefix
      ht' (by norm_num) hS hlen
  · intro r hr t ht hlen
    rw [hstop] at ht
    have ht' : t ∈ lowerFailureTerms (descendingRosserStop 200 (y ^ S))
        P.length [] (descendingSievePrimes z y) := by simpa [P] using ht
    simpa [P] using lowerFailureTerm_chain_sublist_betaCutoffPrefix
      ht' (by norm_num) hS hlen
  · intro t ht
    rw [hstop] at ht
    have ht' : t ∈ upperFailureTerms (descendingRosserStop 200 (y ^ S))
        P.length [] (descendingSievePrimes z y) := by simpa [P] using ht
    exact upperFailureTerm_start_depth (by omega) ht'
  · intro t ht
    rw [hstop] at ht
    have ht' : t ∈ lowerFailureTerms (descendingRosserStop 200 (y ^ S))
        P.length [] (descendingSievePrimes z y) := by simpa [P] using ht
    exact lowerFailureTerm_start_depth (by omega) ht'
  · nlinarith
  · norm_num
  · norm_num
  · intro r hr hstart
    simpa [P] using sixteen_betaCutoffPrefix_inverse_bound hC hdimension hz₀ hz hzy
  · intro r hr hstart
    simpa [P] using sixteen_betaCutoffPrefix_inverse_bound hC hdimension hz₀ hz hzy
  · intro r hstart hr
    have hcast : ((S - 200 : ℕ) : ℝ) ≤ r := by exact_mod_cast hstart
    calc
      Real.log (2 * C) ≤ 9 * (S - 200 : ℕ) / 99 := hlog
      _ ≤ 9 * r / 99 := by gcongr

end Erdos946.DimensionSixteenBeta
