/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.ResidualPrimeFiberSieve
import ErdosProblems.Erdos851.ConcreteBetaCardinality
import ErdosProblems.Erdos851.FiniteBetaProductRatio
import ErdosProblems.Erdos851.FiniteSieveApplication

/-!
# The dimension-one beta sieve for residual prime fibres

This file specializes the finite Rosser--Iwaniec machinery to the local
density `1 / (p - 1)` on the primes not dividing the fixed cofactor.  The
prime list is genuinely smaller than a primorial list, so the cutoff-prefix
geometry is proved for that filtered list rather than hidden behind a
zero-density convention.
-/

namespace Erdos4b

noncomputable section

open scoped BigOperators
open Erdos851.FiniteCombinatorialSieve
open Erdos851.BetaSieveFundamental
open Erdos851.FiniteSieveApplication

/-- Increasing list of the genuine residual sieving primes. -/
def ascendingResidualSievePrimes (y m : ℕ) : List ℕ :=
  (residualSievePrimes y m).sort fun a b ↦ a ≤ b

/-- The same list in the decreasing convention used by recursive Rosser
weights. -/
def descendingResidualSievePrimes (y m : ℕ) : List ℕ :=
  (ascendingResidualSievePrimes y m).reverse

@[simp] theorem mem_ascendingResidualSievePrimes {y m r : ℕ} :
    r ∈ ascendingResidualSievePrimes y m ↔
      r ∈ residualSievePrimes y m := by
  simp [ascendingResidualSievePrimes]

@[simp] theorem mem_descendingResidualSievePrimes {y m r : ℕ} :
    r ∈ descendingResidualSievePrimes y m ↔
      r ∈ residualSievePrimes y m := by
  simp [descendingResidualSievePrimes]

theorem ascendingResidualSievePrimes_nodup (y m : ℕ) :
    (ascendingResidualSievePrimes y m).Nodup := by
  exact Finset.sort_nodup _ _

theorem descendingResidualSievePrimes_nodup (y m : ℕ) :
    (descendingResidualSievePrimes y m).Nodup := by
  simp [descendingResidualSievePrimes,
    ascendingResidualSievePrimes_nodup]

private theorem pairwise_lt_of_pairwise_le_nodup :
    ∀ l : List ℕ, l.Pairwise (· ≤ ·) → l.Nodup →
      l.Pairwise (· < ·) := by
  intro l hle hnodup
  induction l with
  | nil => simp
  | cons a l ih =>
      simp only [List.pairwise_cons] at hle ⊢
      simp only [List.nodup_cons] at hnodup
      refine ⟨?_, ih hle.2 hnodup.2⟩
      intro b hb
      exact lt_of_le_of_ne (hle.1 b hb)
        (Ne.symm fun hab ↦ hnodup.1 (hab ▸ hb))

theorem descendingResidualSievePrimes_pairwise (y m : ℕ) :
    (descendingResidualSievePrimes y m).Pairwise fun p q ↦ q < p := by
  rw [descendingResidualSievePrimes, List.pairwise_reverse]
  exact pairwise_lt_of_pairwise_le_nodup
    (ascendingResidualSievePrimes y m)
    (Finset.pairwise_sort _ _)
    (ascendingResidualSievePrimes_nodup y m)

theorem residualSievePrime_prime {y m r : ℕ}
    (hr : r ∈ residualSievePrimes y m) : r.Prime :=
  (Nat.mem_primesLE.mp (Finset.mem_filter.mp hr).1).2

theorem residualSievePrime_le {y m r : ℕ}
    (hr : r ∈ residualSievePrimes y m) : r ≤ y :=
  (Nat.mem_primesLE.mp (Finset.mem_filter.mp hr).1).1

theorem residualSievePrime_gt_two_of_even {y m r : ℕ}
    (hmEven : Even m) (hr : r ∈ residualSievePrimes y m) : 2 < r := by
  have hrPrime := residualSievePrime_prime hr
  have hrNotM := (Finset.mem_filter.mp hr).2
  have hrNeTwo : r ≠ 2 := by
    intro hre
    subst r
    exact hrNotM hmEven.two_dvd
  have := hrPrime.two_le
  omega

theorem ascendingResidualSievePrimes_prod (y m : ℕ) :
    (ascendingResidualSievePrimes y m).prod =
      residualSieveProduct y m := by
  unfold ascendingResidualSievePrimes residualSieveProduct
  symm
  simpa using List.prod_toFinset id (Finset.sort_nodup
    (residualSievePrimes y m) fun a b : ℕ ↦ a ≤ b)

theorem descendingResidualSievePrimes_prod (y m : ℕ) :
    (descendingResidualSievePrimes y m).prod =
      residualSieveProduct y m := by
  rw [descendingResidualSievePrimes, List.prod_reverse,
    ascendingResidualSievePrimes_prod]

/-- The main Euler product for one residual fibre. -/
def residualPrimeLocalEulerProduct (y m : ℕ) : ℝ :=
  ∏ r ∈ residualSievePrimes y m, (1 - residualPrimeDensity r)

theorem buchstabProduct_descendingResidualSievePrimes (y m : ℕ) :
    Erdos851.buchstabProduct residualPrimeDensity
        (descendingResidualSievePrimes y m) =
      residualPrimeLocalEulerProduct y m := by
  unfold Erdos851.buchstabProduct residualPrimeLocalEulerProduct
    descendingResidualSievePrimes ascendingResidualSievePrimes
  rw [List.map_reverse, List.prod_reverse]
  symm
  simpa using List.prod_toFinset (fun r ↦ 1 - residualPrimeDensity r)
    (Finset.sort_nodup (residualSievePrimes y m)
      fun a b : ℕ ↦ a ≤ b)

theorem residualPrimeLocalEulerProduct_pos
    {y m : ℕ} (hmEven : Even m) :
    0 < residualPrimeLocalEulerProduct y m := by
  unfold residualPrimeLocalEulerProduct
  apply Finset.prod_pos
  intro r hr
  exact sub_pos.mpr (residualPrimeDensity_lt_one
    (residualSievePrime_prime hr)
    (residualSievePrime_gt_two_of_even hmEven hr))

/-- Depth-`r` prefix on the filtered decreasing residual-prime list. -/
noncomputable def residualBetaCutoffPrefix
    (y m r : ℕ) : List ℕ := by
  classical
  exact (descendingResidualSievePrimes y m).filter fun p ↦
    decide (1 < p ∧ betaEligible y r p)

private theorem filter_isPrefix_of_pairwise_upward
    {alpha : Type*} {R : alpha → alpha → Prop}
    (keep : alpha → Bool)
    (hup : ∀ {a b}, R a b → keep b = true → keep a = true) :
    ∀ {l : List alpha}, l.Pairwise R → l.filter keep <+: l := by
  intro l hl
  induction l with
  | nil => simp
  | cons a l ih =>
      simp only [List.pairwise_cons] at hl
      cases ha : keep a
      · have hnone : l.filter keep = [] := by
          apply List.eq_nil_iff_forall_not_mem.mpr
          intro b hb
          simp only [List.mem_filter] at hb
          have hab := hup (hl.1 b hb.1) hb.2
          simp [ha] at hab
        simp [ha, hnone]
      · simp only [List.filter_cons, ha, ↓reduceIte]
        obtain ⟨rest, hrest⟩ := ih hl.2
        exact ⟨rest, by simp [hrest]⟩

theorem residualBetaCutoffPrefix_isPrefix
    (y m r : ℕ) (hy : 1 ≤ y) :
    residualBetaCutoffPrefix y m r <+:
      descendingResidualSievePrimes y m := by
  classical
  apply filter_isPrefix_of_pairwise_upward
    (fun p ↦ decide (1 < p ∧ betaEligible y r p))
    (fun {p q} hqp hq ↦ by
      simp only [decide_eq_true_eq] at hq ⊢
      exact ⟨hq.1.trans hqp,
        betaEligible_of_lt hy hq.1 hqp hq.2⟩)
    (descendingResidualSievePrimes_pairwise y m)

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

private theorem chain_sublist_residualBetaCutoffPrefix_of_terminal
    {y m r : ℕ} {chain : List ℕ}
    (hy : 1 ≤ y)
    (hsub : chain.Sublist (descendingResidualSievePrimes y m))
    (hnonempty : chain ≠ [])
    (hterminal : Real.log (y : ℝ) /
        Real.log (chain.getD (chain.length - 1) 2 : ℝ) <
      betaRatio ^ (r - 1)) :
    chain.Sublist (residualBetaCutoffPrefix y m r) := by
  classical
  have hdesc : chain.Pairwise (fun p q ↦ q < p) :=
    (descendingResidualSievePrimes_pairwise y m).sublist hsub
  let q := chain.getLast hnonempty
  have hlenpos : 0 < chain.length := by
    apply Nat.pos_of_ne_zero
    intro hz
    exact hnonempty (List.length_eq_zero_iff.mp hz)
  have hqmem : q ∈ chain := List.getLast_mem hnonempty
  have hqLarge : 1 < q :=
    (residualSievePrime_prime
      (mem_descendingResidualSievePrimes.mp (hsub.subset hqmem))).one_lt
  have hget : chain.getD (chain.length - 1) 2 = q := by
    calc
      chain.getD (chain.length - 1) 2 = chain[chain.length - 1] := by
        simp [List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem (by omega : chain.length - 1 < chain.length)]
      _ = q := (List.getLast_eq_getElem hnonempty).symm
  have hqEligible : betaEligible y r q := by
    unfold betaEligible
    rw [hget] at hterminal
    exact hterminal
  have hall : ∀ p ∈ chain, 1 < p ∧ betaEligible y r p := by
    intro p hp
    have hpLarge : 1 < p :=
      (residualSievePrime_prime
        (mem_descendingResidualSievePrimes.mp (hsub.subset hp))).one_lt
    refine ⟨hpLarge, ?_⟩
    have hqp := getLast_le_of_pairwise_desc hnonempty hdesc p hp
    rcases hqp.eq_or_lt with heq | hlt
    · exact heq ▸ hqEligible
    · exact betaEligible_of_lt hy hqLarge hlt hqEligible
  have hfiltered : chain.filter
      (fun p ↦ decide (1 < p ∧ betaEligible y r p)) = chain :=
    List.filter_eq_self.mpr fun p hp ↦ by simp [hall p hp]
  have hf := hsub.filter
    (fun p ↦ decide (1 < p ∧ betaEligible y r p))
  simpa only [hfiltered, residualBetaCutoffPrefix] using hf

/-- Every upper first-failure chain lies in the residual cutoff prefix at
its depth. -/
theorem upperFailureTerm_chain_sublist_residualBetaCutoffPrefix
    {y m S fuel r : ℕ} {t : List ℕ × List ℕ}
    (ht : t ∈ upperFailureTerms (descendingRosserStop 100 (y ^ S))
      fuel [] (descendingResidualSievePrimes y m))
    (hS : 101 ≤ S) (hlen : t.1.length = r) :
    t.1.Sublist (residualBetaCutoffPrefix y m r) := by
  have hsub := upperFailureTerms_chain_sublist
    (descendingRosserStop 100 (y ^ S)) fuel []
      (descendingResidualSievePrimes y m) ht
  have hlarge : ∀ p ∈ descendingResidualSievePrimes y m, 1 < p := by
    intro p hp
    exact (residualSievePrime_prime
      (mem_descendingResidualSievePrimes.mp hp)).one_lt
  have hupper : ∀ p ∈ descendingResidualSievePrimes y m, p ≤ y := by
    intro p hp
    exact residualSievePrime_le
      (mem_descendingResidualSievePrimes.mp hp)
  have hcut := upperFailureTerm_log_ratio_lt_betaRatio_pow ht hlarge
    hupper (descendingResidualSievePrimes_pairwise y m) hS
  have hnonempty : t.1 ≠ [] := by
    obtain ⟨k, hk⟩ := upperFailureTerms_chain_length_odd
      (descendingRosserStop 100 (y ^ S)) fuel []
        (descendingResidualSievePrimes y m) ht
    intro hempty
    rw [hempty] at hk
    simp at hk
  have hy : 1 ≤ y := by
    have hlastmem := List.getLast_mem hnonempty
    exact (hlarge _ (hsub.subset hlastmem)).le.trans
      (hupper _ (hsub.subset hlastmem))
  apply chain_sublist_residualBetaCutoffPrefix_of_terminal
    hy hsub hnonempty
  simpa [hlen] using hcut

/-- Lower first-failure chains satisfy the same filtered cutoff. -/
theorem lowerFailureTerm_chain_sublist_residualBetaCutoffPrefix
    {y m S fuel r : ℕ} {t : List ℕ × List ℕ}
    (ht : t ∈ lowerFailureTerms (descendingRosserStop 100 (y ^ S))
      fuel [] (descendingResidualSievePrimes y m))
    (hS : 101 ≤ S) (hlen : t.1.length = r) :
    t.1.Sublist (residualBetaCutoffPrefix y m r) := by
  have hsub := lowerFailureTerms_chain_sublist
    (descendingRosserStop 100 (y ^ S)) fuel []
      (descendingResidualSievePrimes y m) ht
  have hlarge : ∀ p ∈ descendingResidualSievePrimes y m, 1 < p := by
    intro p hp
    exact (residualSievePrime_prime
      (mem_descendingResidualSievePrimes.mp hp)).one_lt
  have hupper : ∀ p ∈ descendingResidualSievePrimes y m, p ≤ y := by
    intro p hp
    exact residualSievePrime_le
      (mem_descendingResidualSievePrimes.mp hp)
  have hcut := lowerFailureTerm_log_ratio_lt_betaRatio_pow ht hlarge
    hupper (descendingResidualSievePrimes_pairwise y m) hS
  have hnonempty : t.1 ≠ [] := by
    obtain ⟨_init, _last, _before, hchain, _hrem⟩ :=
      ((failureTerms_structure (descendingRosserStop 100 (y ^ S))
        fuel [] (descendingResidualSievePrimes y m)).2 t ht).2
    rw [hchain]
    simp
  have hy : 1 ≤ y := by
    have hlastmem := List.getLast_mem hnonempty
    exact (hlarge _ (hsub.subset hlastmem)).le.trans
      (hupper _ (hsub.subset hlastmem))
  apply chain_sublist_residualBetaCutoffPrefix_of_terminal
    hy hsub hnonempty
  simpa [hlen] using hcut

/-- The stopping failure forces every upper residual boundary term to start
at depth `S - 100`. -/
theorem upperResidualFailureTerm_start_depth
    {y m S fuel : ℕ} {t : List ℕ × List ℕ}
    (hy : 1 < y)
    (ht : t ∈ upperFailureTerms (descendingRosserStop 100 (y ^ S))
      fuel [] (descendingResidualSievePrimes y m)) :
    S - 100 ≤ t.1.length := by
  have hfail : ¬ rosserStoppingPredicate 100 (y ^ S) t.1.reverse :=
    upperFailureTerms_not_descendingRosserStoppingPredicate ht
  have hupper : ∀ p ∈ t.1.reverse, p ≤ y := by
    intro p hp
    have hpChain : p ∈ t.1 := by simpa using hp
    have hsub := upperFailureTerms_chain_sublist
      (descendingRosserStop 100 (y ^ S)) fuel []
        (descendingResidualSievePrimes y m) ht
    exact residualSievePrime_le
      (mem_descendingResidualSievePrimes.mp (hsub.subset hpChain))
  have hdepth :=
    Erdos851.RosserBoundaryEstimate.stopping_failure_forces_depth
      hy rfl hupper hfail
  simp only [List.length_reverse] at hdepth
  omega

/-- Lower residual boundary terms have the same starting depth. -/
theorem lowerResidualFailureTerm_start_depth
    {y m S fuel : ℕ} {t : List ℕ × List ℕ}
    (hy : 1 < y)
    (ht : t ∈ lowerFailureTerms (descendingRosserStop 100 (y ^ S))
      fuel [] (descendingResidualSievePrimes y m)) :
    S - 100 ≤ t.1.length := by
  have hfail : ¬ rosserStoppingPredicate 100 (y ^ S) t.1.reverse :=
    lowerFailureTerms_not_descendingRosserStoppingPredicate ht
  have hupper : ∀ p ∈ t.1.reverse, p ≤ y := by
    intro p hp
    have hpChain : p ∈ t.1 := by simpa using hp
    have hsub := lowerFailureTerms_chain_sublist
      (descendingRosserStop 100 (y ^ S)) fuel []
        (descendingResidualSievePrimes y m) ht
    exact residualSievePrime_le
      (mem_descendingResidualSievePrimes.mp (hsub.subset hpChain))
  have hdepth :=
    Erdos851.RosserBoundaryEstimate.stopping_failure_forces_depth
      hy rfl hupper hfail
  simp only [List.length_reverse] at hdepth
  omega

private theorem inverse_buchstabProduct_le_three_mul_inverseLocalEulerProduct
    {g : ℕ → ℝ} {Q : List ℕ} {q y : ℕ}
    (hQnodup : Q.Nodup) (hqmem : q ∈ Q)
    (hqmin : ∀ p ∈ Q, q ≤ p)
    (hQprime : ∀ p ∈ Q, p.Prime)
    (hQupper : ∀ p ∈ Q, p ≤ y)
    (hq2 : 2 < q)
    (hg : ∀ p, p.Prime → 2 < p → 0 ≤ g p ∧ g p < 1)
    (hqfactor : (1 - g q)⁻¹ ≤ 3) :
    (Erdos851.buchstabProduct g Q)⁻¹ ≤
      3 * Erdos851.inverseLocalEulerProduct g q y := by
  classical
  let F := Q.toFinset
  let T := insert q (Erdos851.sievePrimes q y)
  let invFactor : ℕ → ℝ := fun p ↦ (1 - g p)⁻¹
  have hFsub : F ⊆ T := by
    intro p hp
    have hpQ : p ∈ Q := List.mem_toFinset.mp hp
    by_cases hpq : p = q
    · simp [T, hpq]
    · have hqp : q < p :=
        lt_of_le_of_ne (hqmin p hpQ) (Ne.symm hpq)
      have hpS : p ∈ Erdos851.sievePrimes q y :=
        Erdos851.mem_sievePrimes.mpr
          ⟨hqp, hQupper p hpQ, hQprime p hpQ⟩
      simp [T, hpS]
  have hF0 : ∀ p ∈ F, 0 ≤ invFactor p := by
    intro p hp
    have hpQ : p ∈ Q := List.mem_toFinset.mp hp
    have hp2 : 2 < p := hq2.trans_le (hqmin p hpQ)
    exact (inv_pos.mpr
      (sub_pos.mpr (hg p (hQprime p hpQ) hp2).2)).le
  have hTone : ∀ p ∈ T, p ∉ F → 1 ≤ invFactor p := by
    intro p hpT _hpF
    have hpCases : p = q ∨ p ∈ Erdos851.sievePrimes q y := by
      simpa [T] using hpT
    have hpPrime : p.Prime := by
      rcases hpCases with rfl | hpS
      · exact hQprime p hqmem
      · exact (Erdos851.mem_sievePrimes.mp hpS).2.2
    have hp2 : 2 < p := by
      rcases hpCases with rfl | hpS
      · exact hq2
      · exact hq2.trans (Erdos851.mem_sievePrimes.mp hpS).1
    have hgp := hg p hpPrime hp2
    exact (one_le_inv₀ (sub_pos.mpr hgp.2)).2
      (sub_le_self _ hgp.1)
  have hprod : (∏ p ∈ F, invFactor p) ≤
      ∏ p ∈ T, invFactor p :=
    Finset.prod_le_prod_of_subset_of_one_le hFsub hF0 hTone
  calc
    (Erdos851.buchstabProduct g Q)⁻¹ =
        ∏ p ∈ F, invFactor p := by
      unfold Erdos851.buchstabProduct invFactor F
      rw [← List.prod_toFinset (fun p ↦ 1 - g p) hQnodup,
        ← Finset.prod_inv_distrib]
    _ ≤ ∏ p ∈ T, invFactor p := hprod
    _ = (1 - g q)⁻¹ * Erdos851.inverseLocalEulerProduct g q y := by
      simp [T, invFactor, Erdos851.inverseLocalEulerProduct,
        Erdos851.mem_sievePrimes, mul_comm]
    _ ≤ 3 * Erdos851.inverseLocalEulerProduct g q y := by
      apply mul_le_mul_of_nonneg_right hqfactor
      unfold Erdos851.inverseLocalEulerProduct
      apply Finset.prod_nonneg
      intro p hp
      have hpData := Erdos851.mem_sievePrimes.mp hp
      exact (inv_pos.mpr (sub_pos.mpr
        (hg p hpData.2.2 (by omega)).2)).le

private theorem residualPrimeDensity_inverseFactor_le_three
    {q : ℕ} (hq : q.Prime) (hq2 : 2 < q) :
    (1 - residualPrimeDensity q)⁻¹ ≤ (3 : ℝ) := by
  have hqR : (3 : ℝ) ≤ q := by exact_mod_cast (show 3 ≤ q by omega)
  have hpred : (2 : ℝ) ≤ ((q - 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 2 ≤ q - 1 by omega)
  have hinv : (((q - 1 : ℕ) : ℝ))⁻¹ ≤ (2 : ℝ)⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le
      (by norm_num : (0 : ℝ) < 2) hpred
  rw [← residualPrimeDensity_eq_inv_pred hq] at hinv
  have hden : 0 < 1 - residualPrimeDensity q :=
    sub_pos.mpr (residualPrimeDensity_lt_one hq hq2)
  apply (inv_le_comm₀ hden (by norm_num : (0 : ℝ) < 3)).2
  norm_num at hinv ⊢
  linarith

/-- Dimension-one inverse product estimate on every filtered cutoff prefix. -/
theorem residualBetaCutoffPrefix_inverse_bound
    {C : ℝ} (hC : 1 ≤ C)
    (hdimension : ∀ z y : ℕ, 2 ≤ z → z ≤ y →
      Erdos851.inverseLocalEulerProduct residualPrimeDensity z y ≤
        C * (Real.log (y : ℝ) / Real.log (z : ℝ)))
    {y m r : ℕ} (hmEven : Even m) :
    (Erdos851.buchstabProduct residualPrimeDensity
        (residualBetaCutoffPrefix y m r))⁻¹ ≤
      (3 * C) * Real.rpow betaRatio ((1 : ℝ) * r) := by
  classical
  let Q := residualBetaCutoffPrefix y m r
  change (Erdos851.buchstabProduct residualPrimeDensity Q)⁻¹ ≤ _
  by_cases hQ : Q = []
  · rw [hQ]
    simp only [Erdos851.buchstabProduct, List.map_nil, List.prod_nil,
      inv_one]
    have hrpow : 1 ≤ Real.rpow betaRatio ((1 : ℝ) * r) :=
      Real.one_le_rpow (by norm_num [betaRatio]) (by positivity)
    calc
      (1 : ℝ) ≤ 3 * C := by nlinarith
      _ ≤ (3 * C) * Real.rpow betaRatio ((1 : ℝ) * r) := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hrpow
          (by positivity : 0 ≤ (3 : ℝ) * C)
  · let q := Q.getLast hQ
    have hqQ : q ∈ Q := List.getLast_mem hQ
    have hqQ' : q ∈ residualBetaCutoffPrefix y m r := by
      simpa [Q] using hqQ
    have hqData : q ∈ residualSievePrimes y m ∧
        1 < q ∧ betaEligible y r q := by
      simpa [residualBetaCutoffPrefix] using hqQ'
    have hqP : q ∈ descendingResidualSievePrimes y m := by
      exact mem_descendingResidualSievePrimes.mpr hqData.1
    have hqResidual₀ : q ∈ residualSievePrimes y m :=
      mem_descendingResidualSievePrimes.mp hqP
    have hy : 1 ≤ y :=
      (residualSievePrime_prime hqResidual₀).one_lt.le.trans
        (residualSievePrime_le hqResidual₀)
    have hQsub : Q.Sublist (descendingResidualSievePrimes y m) :=
      (residualBetaCutoffPrefix_isPrefix y m r hy).sublist
    have hqResidual : q ∈ residualSievePrimes y m :=
      mem_descendingResidualSievePrimes.mp (hQsub.subset hqQ)
    have hqPrime := residualSievePrime_prime hqResidual
    have hqUpper := residualSievePrime_le hqResidual
    have hq2 := residualSievePrime_gt_two_of_even hmEven hqResidual
    have hQdesc : Q.Pairwise (fun p q ↦ q < p) :=
      (descendingResidualSievePrimes_pairwise y m).sublist hQsub
    have hqmin : ∀ p ∈ Q, q ≤ p :=
      getLast_le_of_pairwise_desc hQ hQdesc
    have hqEligible : betaEligible y r q := by
      exact hqData.2.2
    have hcut : Real.log (y : ℝ) / Real.log (q : ℝ) ≤
        betaRatio ^ r := by
      exact hqEligible.le.trans
        (pow_le_pow_right₀ (by norm_num [betaRatio]) (by omega))
    have hbase :=
      inverse_buchstabProduct_le_three_mul_inverseLocalEulerProduct
        (g := residualPrimeDensity) (Q := Q) (q := q) (y := y)
        (hQsub.nodup (descendingResidualSievePrimes_nodup y m)) hqQ
        hqmin
        (fun p hp ↦ residualSievePrime_prime
          (mem_descendingResidualSievePrimes.mp (hQsub.subset hp)))
        (fun p hp ↦ residualSievePrime_le
          (mem_descendingResidualSievePrimes.mp (hQsub.subset hp)))
        hq2
        (fun p hp hp2 ↦ ⟨(residualPrimeDensity_pos hp).le,
          residualPrimeDensity_lt_one hp hp2⟩)
        (residualPrimeDensity_inverseFactor_le_three hqPrime hq2)
    calc
      (Erdos851.buchstabProduct residualPrimeDensity Q)⁻¹ ≤
          3 * Erdos851.inverseLocalEulerProduct
            residualPrimeDensity q y := hbase
      _ ≤ 3 * (C * (Real.log (y : ℝ) / Real.log (q : ℝ))) := by
        gcongr
        exact hdimension q y (by omega) hqUpper
      _ ≤ (3 * C) * betaRatio ^ r := by nlinarith
      _ = (3 * C) * Real.rpow betaRatio ((1 : ℝ) * r) := by
        congr 1
        rw [one_mul]
        exact (Real.rpow_natCast betaRatio r).symm

/-- The filtered residual-prime list satisfies both concrete depth-product
ratio estimates with a single absolute constant. -/
theorem exists_residualPrime_concrete_hasDepthProductRatio :
    ∃ A : ℝ, 1 ≤ A ∧
      ∀ y m S fuel : ℕ, Even m → 1 < y → 101 ≤ S →
        let P := descendingResidualSievePrimes y m
        let stop := descendingRosserStop 100 (y ^ S)
        HasDepthProductRatio residualPrimeDensity
            (upperFailureTerms stop fuel [] P)
            (residualPrimeLocalEulerProduct y m)
            A 1 (S - 100) fuel ∧
          HasDepthProductRatio residualPrimeDensity
            (lowerFailureTerms stop fuel [] P)
            (residualPrimeLocalEulerProduct y m)
            A 1 (S - 100) fuel := by
  obtain ⟨C, hC, hdimension⟩ :=
    exists_residualPrimeDensity_dimension_bound
  let C₀ := max 1 C
  have hC₀ : 1 ≤ C₀ := le_max_left _ _
  have hdimension₀ : ∀ z y : ℕ, 2 ≤ z → z ≤ y →
      Erdos851.inverseLocalEulerProduct residualPrimeDensity z y ≤
        C₀ * (Real.log (y : ℝ) / Real.log (z : ℝ)) := by
    intro z y hz hzy
    have hratio : 0 ≤ Real.log (y : ℝ) / Real.log (z : ℝ) := by
      exact div_nonneg
        (Real.log_nonneg (by exact_mod_cast (show 1 ≤ y by omega)))
        (Real.log_pos (by exact_mod_cast (show 1 < z by omega))).le
    exact (hdimension z y hz hzy).trans
      (mul_le_mul_of_nonneg_right (le_max_right 1 C) hratio)
  refine ⟨3 * C₀, by nlinarith, ?_⟩
  intro y m S fuel hmEven hy hS
  dsimp only
  let P := descendingResidualSievePrimes y m
  let stop := descendingRosserStop 100 (y ^ S)
  have hx₀ : ∀ p, 0 ≤ residualPrimeDensity p := by
    intro p
    unfold residualPrimeDensity
    positivity
  have hx₁ : ∀ p ∈ P, residualPrimeDensity p < 1 := by
    intro p hp
    have hpResidual : p ∈ residualSievePrimes y m :=
      mem_descendingResidualSievePrimes.mp hp
    exact residualPrimeDensity_lt_one
      (residualSievePrime_prime hpResidual)
      (residualSievePrime_gt_two_of_even hmEven hpResidual)
  have hV : residualPrimeLocalEulerProduct y m =
      Erdos851.buchstabProduct residualPrimeDensity P := by
    exact (buchstabProduct_descendingResidualSievePrimes y m).symm
  have hprefix : ∀ r ≤ fuel,
      residualBetaCutoffPrefix y m r <+: P := by
    intro r _hr
    exact residualBetaCutoffPrefix_isPrefix y m r hy.le
  constructor
  · apply upper_hasDepthProductRatio_of_prefixProductRatio
      stop residualPrimeDensity fuel [] (residualBetaCutoffPrefix y m)
      hx₀ hx₁ (descendingResidualSievePrimes_nodup y m) hV hprefix
    · intro r _hr t ht hlen
      exact upperFailureTerm_chain_sublist_residualBetaCutoffPrefix
        ht hS hlen
    · intro t ht
      exact upperResidualFailureTerm_start_depth hy ht
    · nlinarith
    · intro r _hr _hstart
      exact residualBetaCutoffPrefix_inverse_bound hC₀ hdimension₀
        hmEven
  · apply lower_hasDepthProductRatio_of_prefixProductRatio
      stop residualPrimeDensity fuel [] (residualBetaCutoffPrefix y m)
      hx₀ hx₁ (descendingResidualSievePrimes_nodup y m) hV hprefix
    · intro r _hr t ht hlen
      exact lowerFailureTerm_chain_sublist_residualBetaCutoffPrefix
        ht hS hlen
    · intro t ht
      exact lowerResidualFailureTerm_start_depth hy ht
    · nlinarith
    · intro r _hr _hstart
      exact residualBetaCutoffPrefix_inverse_bound hC₀ hdimension₀
        hmEven

/-- Recursive finite fundamental lemma for the residual prime density. -/
theorem exists_residualPrime_concrete_mainTerm_bounds :
    ∃ A : ℝ, 1 ≤ A ∧
      ∀ y m S fuel : ℕ, Even m → 1 < y → 101 ≤ S →
        (descendingResidualSievePrimes y m).length ≤ fuel →
        Real.log A ≤ 2 * (S - 100 : ℕ) / 99 →
        let P := descendingResidualSievePrimes y m
        let stop := descendingRosserStop 100 (y ^ S)
        let V := residualPrimeLocalEulerProduct y m
        let eta := (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)
        (1 - eta) * V ≤
            Erdos851.rosserLowerEval stop residualPrimeDensity fuel [] P ∧
          Erdos851.rosserUpperEval stop residualPrimeDensity fuel [] P ≤
            (1 + eta) * V := by
  obtain ⟨A, hA, hdepth⟩ :=
    exists_residualPrime_concrete_hasDepthProductRatio
  refine ⟨A, hA, ?_⟩
  intro y m S fuel hmEven hy hS hfuel hlog
  dsimp only
  let P := descendingResidualSievePrimes y m
  let stop := descendingRosserStop 100 (y ^ S)
  let V := residualPrimeLocalEulerProduct y m
  have hratios := hdepth y m S fuel hmEven hy hS
  have hbounds := rosserBoundaries_le_geometric_of_depthProductRatio
    stop residualPrimeDensity ([] : List ℕ) P
    (residualPrimeLocalEulerProduct_pos hmEven).le
    hA (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (1 : ℝ) ≤ 2)
    hratios.1 hratios.2 (by
      intro r hrstart _hrfuel
      have hstartR : ((S - 100 : ℕ) : ℝ) ≤ r := by
        exact_mod_cast hrstart
      norm_num
      nlinarith)
  have heq := Erdos851.rosser_eval_sub_product_eq_boundary
    stop residualPrimeDensity fuel [] P hfuel
  have hV : Erdos851.buchstabProduct residualPrimeDensity P = V :=
    buchstabProduct_descendingResidualSievePrimes y m
  rw [hV] at heq
  change
    (1 - (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)) * V ≤
        Erdos851.rosserLowerEval stop residualPrimeDensity fuel [] P ∧
      Erdos851.rosserUpperEval stop residualPrimeDensity fuel [] P ≤
        (1 + (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)) * V
  constructor
  · nlinarith [hbounds.2, heq.2]
  · nlinarith [hbounds.1, heq.1]

/-- Increasing-list form consumed by the abstract `BoundingSieve`. -/
theorem exists_residualPrime_concrete_finiteMainTerm_bounds :
    ∃ A : ℝ, 1 ≤ A ∧
      ∀ y m S : ℕ, Even m → 1 < y → 101 ≤ S →
        Real.log A ≤ 2 * (S - 100 : ℕ) / 99 →
        let P := ascendingResidualSievePrimes y m
        let V := residualPrimeLocalEulerProduct y m
        let eta := (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)
        (1 - eta) * V ≤
            lowerMainTerm (rosserStoppingPredicate 100 (y ^ S))
              residualPrimeDensity P ∧
          upperMainTerm (rosserStoppingPredicate 100 (y ^ S))
              residualPrimeDensity P ≤ (1 + eta) * V := by
  classical
  obtain ⟨A, hA, hmain⟩ := exists_residualPrime_concrete_mainTerm_bounds
  refine ⟨A, hA, ?_⟩
  intro y m S hmEven hy hS hlog
  dsimp only
  let P := ascendingResidualSievePrimes y m
  have hrecursive := hmain y m S P.length hmEven hy hS (by
    simp [P, descendingResidualSievePrimes]) hlog
  have hstop : descendingRosserStop 100 (y ^ S) =
      (fun s ↦ decide
        (rosserStoppingPredicate 100 (y ^ S) s.reverse)) := by
    funext s
    rw [Bool.eq_iff_iff]
    simp [descendingRosserStoppingPredicate]
  rw [Erdos851.FiniteRecursiveBridge.lowerMainTerm_eq_rosserLowerEval,
    Erdos851.FiniteRecursiveBridge.upperMainTerm_eq_rosserUpperEval]
  rw [← hstop]
  simpa [P, descendingResidualSievePrimes] using hrecursive

private noncomputable def residualAdmissibilityFlag
    (Adm : List ℕ → Prop) (t : List ℕ) : Bool := by
  classical
  exact if Adm t then true else false

@[simp] private theorem residualAdmissibilityFlag_eq_true
    (Adm : List ℕ → Prop) (t : List ℕ) :
    residualAdmissibilityFlag Adm t = true ↔ Adm t := by
  classical
  simp [residualAdmissibilityFlag]

private theorem admissibleRemainderAbs_eq_residual_filter
    (Adm : List ℕ → Prop) (R : List ℕ → ℝ) (P : List ℕ) :
    admissibleRemainderAbs Adm R P =
      (((P.sublists.filter (residualAdmissibilityFlag Adm)).map
        fun t ↦ |R t|).sum) := by
  classical
  unfold admissibleRemainderAbs
  generalize P.sublists = L
  induction L with
  | nil => simp
  | cons t L ih =>
      by_cases ht : Adm t <;>
        simp [residualAdmissibilityFlag, ht, ih]

/-- Injectivity of products of sublists turns the admissible-chain error
into the divisor-indexed level remainder, with no square-level loss. -/
theorem admissibleRemainderAbs_le_levelRemainder
    (s : BoundingSieve) (P : List ℕ) (Adm : List ℕ → Prop)
    (D : ℕ)
    (hsort : P.Pairwise (· ≤ ·)) (hnodup : P.Nodup)
    (hprime : ∀ p ∈ P, p.Prime)
    (hprod : P.prod = s.prodPrimes)
    (hsupport : ∀ t ∈ P.sublists, Adm t → t.prod ≤ D) :
    admissibleRemainderAbs Adm (fun t ↦ s.rem t.prod) P ≤
      levelRemainder s D := by
  classical
  let L := P.sublists.filter (residualAdmissibilityFlag Adm)
  have hLsub : ∀ t ∈ L, t ∈ P.sublists := by
    intro t ht
    exact (List.mem_filter.mp ht).1
  have hLadm : ∀ t ∈ L, Adm t := by
    intro t ht
    exact (residualAdmissibilityFlag_eq_true Adm t).mp
      (List.mem_filter.mp ht).2
  have hLnodup : L.Nodup := hnodup.sublists.filter _
  have hprodNodup : (L.map List.prod).Nodup := by
    apply hLnodup.map_on
    intro t ht u hu htu
    exact prod_injective_on_sublists P hsort hnodup hprime
      (hLsub t ht) (hLsub u hu) htu
  have hproducts : (L.map List.prod).toFinset ⊆
      (Nat.divisors s.prodPrimes).filter fun d ↦ d ≤ D := by
    intro d hd
    rw [List.mem_toFinset] at hd
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hd
    rw [Finset.mem_filter, Nat.mem_divisors]
    refine ⟨⟨?_, s.prodPrimes_squarefree.ne_zero⟩,
      hsupport t (hLsub t ht) (hLadm t ht)⟩
    rw [← hprod]
    exact (List.mem_sublists.mp (hLsub t ht)).prod_dvd_prod
  rw [admissibleRemainderAbs_eq_residual_filter]
  change (L.map fun t ↦ |s.rem t.prod|).sum ≤ _
  have hsum := List.sum_toFinset (fun d ↦ |s.rem d|) hprodNodup
  have hsum' : (L.map fun t ↦ |s.rem t.prod|).sum =
      ∑ d ∈ (L.map List.prod).toFinset, |s.rem d| := by
    simpa [Function.comp_def] using hsum.symm
  rw [hsum']
  unfold levelRemainder
  exact Finset.sum_le_sum_of_subset_of_nonneg hproducts
    (fun d _hd _hdL ↦ abs_nonneg (s.rem d))

/-- Abstract upper beta-sieve application retaining the full divisor-level
remainder instead of replacing it by `D²`. -/
theorem boundingSieve_siftedSum_le_upperMain_add_levelRemainder
    (s : BoundingSieve) (P : List ℕ) (Astop : List ℕ → Prop)
    (D : ℕ)
    (hprod : P.prod = s.prodPrimes)
    (hsort : P.Pairwise (· ≤ ·)) (hnodup : P.Nodup)
    (hprime : ∀ p ∈ P, p.Prime)
    (hsupport : ∀ t ∈ P.sublists,
      UpperAdmissible Astop t → t.prod ≤ D) :
    s.siftedSum ≤
      s.totalMass * upperMainTerm Astop (fun p ↦ s.nu p) P +
        levelRemainder s D := by
  have happrox : ∀ t ∈ P.sublists,
      intersectionMass s.support s.weights (fun n p ↦ p ∣ n) t =
        s.totalMass * chainWeight (fun p ↦ s.nu p) t +
          s.rem t.prod := by
    intro t ht
    have htsub := List.mem_sublists.mp ht
    have htnodup := hnodup.sublist htsub
    have htprime : ∀ p ∈ t, p.Prime := by
      intro p hp
      exact hprime p (htsub.subset hp)
    rw [intersectionMass_dvd_eq_multSum s t htnodup htprime,
      s.multSum_eq_main_err,
      nu_prod_eq_chainWeight s t htnodup htprime]
    ring
  have hbase := siftedMass_le_upperMain_add_remainder
    s.support s.weights s.weights_nonneg (fun n p ↦ p ∣ n)
    Astop (fun p ↦ s.nu p) s.totalMass (fun t ↦ s.rem t.prod)
    P happrox
  have herr := admissibleRemainderAbs_le_levelRemainder
    s P (UpperAdmissible Astop) D hsort hnodup hprime hprod hsupport
  rw [siftedMass_dvd_eq_siftedSum s P hprod hprime] at hbase
  linarith

/-- End-to-end finite beta-sieve upper bound for a residual prime fibre,
with the two Bombieri--Vinogradov endpoint losses displayed explicitly. -/
theorem exists_residualPrimeFiber_beta_upper_bound :
    ∃ Aβ : ℝ, 1 ≤ Aβ ∧
      ∀ {theta B C : ℝ} {X₀ U y z m S : ℕ},
        0 < m → Even m → z ≤ U / m → 1 < y → 101 ≤ S →
        Real.log Aβ ≤ 2 * (S - 100 : ℕ) / 99 →
        BoundedGaps.Maynard.PrimeLevelWitness theta B C X₀ →
        X₀ ≤ U / m → X₀ ≤ z →
        y ^ S ≤ BoundedGaps.Maynard.modulusCutoff theta (U / m) →
        y ^ S ≤ BoundedGaps.Maynard.modulusCutoff theta z →
        let eta := (4 * Aβ / 3) * (1 / 4 : ℝ) ^ (S - 100)
        ((residualPrimeFiber U y z m).card : ℝ) ≤
          ((residualPrimeCandidates U z m).card : ℝ) *
              ((1 + eta) * residualPrimeLocalEulerProduct y m) +
            C * ((U / m : ℕ) : ℝ) /
              Real.rpow (Real.log ((U / m : ℕ) : ℝ)) B +
            C * (z : ℝ) / Real.rpow (Real.log (z : ℝ)) B := by
  classical
  obtain ⟨Aβ, hAβ, hmain⟩ :=
    exists_residualPrime_concrete_finiteMainTerm_bounds
  refine ⟨Aβ, hAβ, ?_⟩
  intro theta B C X₀ U y z m S hm hmEven hzU hy hS hlog hw
    hupper hlower hDupper hDlower
  dsimp only
  let P := ascendingResidualSievePrimes y m
  let D := y ^ S
  let Astop := rosserStoppingPredicate 100 D
  let sieve := residualPrimeBoundingSieve U y z m hm hmEven
  have hprod : P.prod = sieve.prodPrimes := by
    change P.prod = residualSieveProduct y m
    exact ascendingResidualSievePrimes_prod y m
  have hsort : P.Pairwise (· ≤ ·) := by
    exact Finset.pairwise_sort _ _
  have hnodup : P.Nodup := ascendingResidualSievePrimes_nodup y m
  have hprime : ∀ p ∈ P, p.Prime := by
    intro p hp
    exact residualSievePrime_prime
      (mem_ascendingResidualSievePrimes.mp hp)
  have hDone : 1 ≤ D := by
    dsimp [D]
    exact one_le_pow₀ (by omega)
  have hlevel : ∀ p ∈ P, p ≤ D := by
    intro p hp
    have hpy := residualSievePrime_le
      (mem_ascendingResidualSievePrimes.mp hp)
    exact hpy.trans (le_self_pow (by omega : 1 ≤ y) (by omega))
  have hsupport : ∀ t ∈ P.sublists,
      UpperAdmissible Astop t → t.prod ≤ D := by
    intro t ht hadm
    apply prod_le_of_upperAdmissible_rosserStoppingPredicate
      (by norm_num : 1 ≤ 100) hDone
      (hsort.sublist (List.mem_sublists.mp ht))
      (by
        intro p hp
        exact (hprime p ((List.mem_sublists.mp ht).subset hp)).one_le)
      hadm
  have hupperSieve :=
    boundingSieve_siftedSum_le_upperMain_add_levelRemainder
      sieve P Astop D hprod hsort hnodup hprime hsupport
  have hnu : ∀ p ∈ P, sieve.nu p = residualPrimeDensity p := by
    intro p hp
    exact residualPrimeSieveNu_prime_eq_density (m := m) (hprime p hp)
  have hmainBound := hmain y m S hmEven hy hS hlog
  dsimp only at hmainBound
  have hmainUpper :
      upperMainTerm Astop (fun p ↦ sieve.nu p) P ≤
        (1 + (4 * Aβ / 3) * (1 / 4 : ℝ) ^ (S - 100)) *
          residualPrimeLocalEulerProduct y m := by
    rw [Erdos851.upperMainTerm_congr_on Astop (fun p ↦ sieve.nu p)
      residualPrimeDensity P hnu]
    simpa [Astop, D, P] using hmainBound.2
  have hrem :=
    residualPrimeBoundingSieve_levelRemainder_le_primeLevelWitness
      (U := U) (y := y) (z := z) (m := m) (D := D)
      (hm := hm) (hmEven := hmEven)
      hw hzU hupper hlower hDupper hDlower
  rw [residualPrimeBoundingSieve_siftedSum,
    residualPrimeBoundingSieve_totalMass] at hupperSieve
  calc
    ((residualPrimeFiber U y z m).card : ℝ) ≤
        ((residualPrimeCandidates U z m).card : ℝ) *
            upperMainTerm Astop (fun p ↦ sieve.nu p) P +
          levelRemainder sieve D := hupperSieve
    _ ≤ ((residualPrimeCandidates U z m).card : ℝ) *
          ((1 + (4 * Aβ / 3) * (1 / 4 : ℝ) ^ (S - 100)) *
            residualPrimeLocalEulerProduct y m) +
          levelRemainder sieve D := by
      simpa only [add_comm] using
        add_le_add_right
          (mul_le_mul_of_nonneg_left hmainUpper
            (Nat.cast_nonneg (residualPrimeCandidates U z m).card))
          (levelRemainder sieve D)
    _ ≤ ((residualPrimeCandidates U z m).card : ℝ) *
          ((1 + (4 * Aβ / 3) * (1 / 4 : ℝ) ^ (S - 100)) *
            residualPrimeLocalEulerProduct y m) +
        C * ((U / m : ℕ) : ℝ) /
            Real.rpow (Real.log ((U / m : ℕ) : ℝ)) B +
          C * (z : ℝ) / Real.rpow (Real.log (z : ℝ)) B := by
      simpa only [add_assoc, add_comm, add_left_comm] using
        add_le_add_left hrem
          (((residualPrimeCandidates U z m).card : ℝ) *
            ((1 + (4 * Aβ / 3) * (1 / 4 : ℝ) ^ (S - 100)) *
              residualPrimeLocalEulerProduct y m))

end

end Erdos4b
