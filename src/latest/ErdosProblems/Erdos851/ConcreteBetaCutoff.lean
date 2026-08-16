/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos851.BetaChainLogBridge
import ErdosProblems.Erdos851.BetaProductRatioDepth
import ErdosProblems.Erdos851.BetaStoppingGeometry
import ErdosProblems.Erdos851.FiniteRecursiveBridge
import ErdosProblems.Erdos851.RosserBoundaryEstimate

/-!
# Concrete cutoff prefixes for the beta-100 sieve

The beta-chain ratio selects, at each depth, an initial segment of the
decreasing prime list.  This file constructs that segment and proves its
one- and two-dimensional inverse Euler-product estimates.
-/

namespace Erdos851.BetaSieveFundamental

open scoped BigOperators
open Erdos851.FiniteCombinatorialSieve

/-- The prime interval `(z,y]`, listed in provably decreasing order.  We use
`Finset.sort` rather than `Finset.toList`, whose order is unspecified. -/
def descendingSievePrimes (z y : ℕ) : List ℕ :=
  (sievePrimes z y).sort (fun a b ↦ a ≤ b) |>.reverse

private theorem pairwise_lt_of_pairwise_le_nodup :
    ∀ l : List ℕ, l.Pairwise (· ≤ ·) → l.Nodup → l.Pairwise (· < ·) := by
  intro l hle hnodup
  induction l with
  | nil => simp
  | cons a l ih =>
      simp only [List.pairwise_cons] at hle ⊢
      simp only [List.nodup_cons] at hnodup
      refine ⟨?_, ih hle.2 hnodup.2⟩
      intro b hb
      exact lt_of_le_of_ne (hle.1 b hb) (Ne.symm (fun hab ↦ hnodup.1 (hab ▸ hb)))

theorem descendingSievePrimes_pairwise (z y : ℕ) :
    (descendingSievePrimes z y).Pairwise (fun p q ↦ q < p) := by
  rw [descendingSievePrimes, List.pairwise_reverse]
  exact pairwise_lt_of_pairwise_le_nodup
    ((sievePrimes z y).sort (fun a b ↦ a ≤ b))
    (Finset.pairwise_sort _ _) (Finset.sort_nodup _ _)

theorem descendingSievePrimes_nodup (z y : ℕ) :
    (descendingSievePrimes z y).Nodup := by
  simp [descendingSievePrimes, Finset.sort_nodup]

@[simp] theorem mem_descendingSievePrimes {z y p : ℕ} :
    p ∈ descendingSievePrimes z y ↔ p ∈ sievePrimes z y := by
  simp [descendingSievePrimes, Finset.mem_sort]

/-- The strict logarithmic eligibility condition at depth `r`. -/
def betaEligible (y r p : ℕ) : Prop :=
  Real.log (y : ℝ) / Real.log (p : ℝ) < betaRatio ^ (r - 1)

/-- The common depth-`r` cutoff prefix. -/
noncomputable def betaCutoffPrefix (z y r : ℕ) : List ℕ := by
  classical
  exact (descendingSievePrimes z y).filter fun p ↦
    decide (1 < p ∧ betaEligible y r p)

theorem betaEligible_of_lt {y r p q : ℕ}
    (hy : 1 ≤ y) (hq : 1 < q) (hqp : q < p)
    (hqEligible : betaEligible y r q) : betaEligible y r p := by
  have hlogy : 0 ≤ Real.log (y : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hy)
  have hlogq : 0 < Real.log (q : ℝ) :=
    Real.log_pos (by exact_mod_cast hq)
  have hlogqp : Real.log (q : ℝ) ≤ Real.log (p : ℝ) := by
    apply Real.log_le_log
    · positivity
    · exact_mod_cast hqp.le
  exact (div_le_div_of_nonneg_left hlogy hlogq hlogqp).trans_lt hqEligible

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

theorem betaCutoffPrefix_isPrefix (z y r : ℕ) (hy : 1 ≤ y) :
    betaCutoffPrefix z y r <+: descendingSievePrimes z y := by
  classical
  apply filter_isPrefix_of_pairwise_upward
    (fun p ↦ decide (1 < p ∧ betaEligible y r p))
    (fun {p q} hqp hq ↦ by
      simp only [decide_eq_true_eq] at hq ⊢
      exact ⟨hq.1.trans hqp, betaEligible_of_lt hy hq.1 hqp hq.2⟩)
    (descendingSievePrimes_pairwise z y)

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

private theorem chain_sublist_betaCutoffPrefix_of_terminal
    {z y r : ℕ} {chain : List ℕ}
    (hy : 1 ≤ y) (hsub : chain.Sublist (descendingSievePrimes z y))
    (hnonempty : chain ≠ [])
    (hterminal : Real.log (y : ℝ) /
        Real.log (chain.getD (chain.length - 1) 2 : ℝ) <
      betaRatio ^ (r - 1)) :
    chain.Sublist (betaCutoffPrefix z y r) := by
  classical
  have hdesc : chain.Pairwise (fun p q ↦ q < p) :=
    (descendingSievePrimes_pairwise z y).sublist hsub
  let q := chain.getLast hnonempty
  have hlenpos : 0 < chain.length := by
    apply Nat.pos_of_ne_zero
    intro hz
    exact hnonempty (List.length_eq_zero_iff.mp hz)
  have hqmem : q ∈ chain := List.getLast_mem hnonempty
  have hqLarge : 1 < q := by
    have hqP : q ∈ descendingSievePrimes z y := hsub.subset hqmem
    exact (mem_sievePrimes.mp (mem_descendingSievePrimes.mp hqP)).2.2.one_lt
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
  have hchainEligible : ∀ p ∈ chain, 1 < p ∧ betaEligible y r p := by
    intro p hp
    have hpP : p ∈ descendingSievePrimes z y := hsub.subset hp
    have hpLarge : 1 < p :=
      (mem_sievePrimes.mp (mem_descendingSievePrimes.mp hpP)).2.2.one_lt
    refine ⟨hpLarge, ?_⟩
    have hqp := getLast_le_of_pairwise_desc hnonempty hdesc p hp
    rcases hqp.eq_or_lt with hEq | hlt
    · exact hEq ▸ hqEligible
    · exact betaEligible_of_lt hy hqLarge hlt hqEligible
  have hfiltered : chain.filter
      (fun p ↦ decide (1 < p ∧ betaEligible y r p)) = chain :=
    List.filter_eq_self.mpr (fun p hp ↦ by simp [hchainEligible p hp])
  have hf := hsub.filter
    (fun p ↦ decide (1 < p ∧ betaEligible y r p))
  simpa only [hfiltered, betaCutoffPrefix] using hf

/-- Every upper depth-`r` first-failure chain lies in the common concrete
cutoff prefix. -/
theorem upperFailureTerm_chain_sublist_betaCutoffPrefix
    {z y S fuel r : ℕ} {t : List ℕ × List ℕ}
    (ht : t ∈ upperFailureTerms (descendingRosserStop 100 (y ^ S))
      fuel [] (descendingSievePrimes z y))
    (hS : 101 ≤ S) (hlen : t.1.length = r) :
    t.1.Sublist (betaCutoffPrefix z y r) := by
  have hsub := upperFailureTerms_chain_sublist
    (descendingRosserStop 100 (y ^ S)) fuel []
      (descendingSievePrimes z y) ht
  have hlarge : ∀ p ∈ descendingSievePrimes z y, 1 < p := by
    intro p hp
    exact (mem_sievePrimes.mp (mem_descendingSievePrimes.mp hp)).2.2.one_lt
  have hupper : ∀ p ∈ descendingSievePrimes z y, p ≤ y := by
    intro p hp
    exact (mem_sievePrimes.mp (mem_descendingSievePrimes.mp hp)).2.1
  have hcut := upperFailureTerm_log_ratio_lt_betaRatio_pow ht hlarge hupper
    (descendingSievePrimes_pairwise z y) hS
  have hnonempty : t.1 ≠ [] := by
    obtain ⟨k, hk⟩ := upperFailureTerms_chain_length_odd
      (descendingRosserStop 100 (y ^ S)) fuel []
        (descendingSievePrimes z y) ht
    intro hempty
    rw [hempty] at hk
    simp at hk
  have hy : 1 ≤ y := by
    have hlastmem := List.getLast_mem hnonempty
    exact (hlarge _ (hsub.subset hlastmem)).le.trans
      (hupper _ (hsub.subset hlastmem))
  apply chain_sublist_betaCutoffPrefix_of_terminal
    hy hsub hnonempty
  simpa [hlen] using hcut

/-- Every lower depth-`r` first-failure chain lies in the same cutoff
prefix. -/
theorem lowerFailureTerm_chain_sublist_betaCutoffPrefix
    {z y S fuel r : ℕ} {t : List ℕ × List ℕ}
    (ht : t ∈ lowerFailureTerms (descendingRosserStop 100 (y ^ S))
      fuel [] (descendingSievePrimes z y))
    (hS : 101 ≤ S) (hlen : t.1.length = r) :
    t.1.Sublist (betaCutoffPrefix z y r) := by
  have hsub := lowerFailureTerms_chain_sublist
    (descendingRosserStop 100 (y ^ S)) fuel []
      (descendingSievePrimes z y) ht
  have hlarge : ∀ p ∈ descendingSievePrimes z y, 1 < p := by
    intro p hp
    exact (mem_sievePrimes.mp (mem_descendingSievePrimes.mp hp)).2.2.one_lt
  have hupper : ∀ p ∈ descendingSievePrimes z y, p ≤ y := by
    intro p hp
    exact (mem_sievePrimes.mp (mem_descendingSievePrimes.mp hp)).2.1
  have hcut := lowerFailureTerm_log_ratio_lt_betaRatio_pow ht hlarge hupper
    (descendingSievePrimes_pairwise z y) hS
  have hnonempty : t.1 ≠ [] := by
    obtain ⟨_init, _last, _before, hchain, _hrem⟩ :=
      ((failureTerms_structure (descendingRosserStop 100 (y ^ S))
        fuel [] (descendingSievePrimes z y)).2 t ht).2
    rw [hchain]
    simp
  have hy : 1 ≤ y := by
    have hlastmem := List.getLast_mem hnonempty
    exact (hlarge _ (hsub.subset hlastmem)).le.trans
      (hupper _ (hsub.subset hlastmem))
  apply chain_sublist_betaCutoffPrefix_of_terminal
    hy hsub hnonempty
  simpa [hlen] using hcut

private theorem inverse_buchstabProduct_le_three_mul_inverseLocalEulerProduct
    {g : ℕ → ℝ} {Q : List ℕ} {q y : ℕ}
    (hQnodup : Q.Nodup) (hqmem : q ∈ Q)
    (hqmin : ∀ p ∈ Q, q ≤ p)
    (hQprime : ∀ p ∈ Q, p.Prime)
    (hQupper : ∀ p ∈ Q, p ≤ y)
    (hq2 : 2 < q)
    (hg : ∀ p, p.Prime → 2 < p → 0 ≤ g p ∧ g p < 1)
    (hqfactor : (1 - g q)⁻¹ ≤ 3) :
    (buchstabProduct g Q)⁻¹ ≤
      3 * inverseLocalEulerProduct g q y := by
  classical
  let F := Q.toFinset
  let T := insert q (sievePrimes q y)
  let invFactor : ℕ → ℝ := fun p ↦ (1 - g p)⁻¹
  have hFsub : F ⊆ T := by
    intro p hp
    have hpQ : p ∈ Q := List.mem_toFinset.mp hp
    by_cases hpq : p = q
    · simp [T, hpq]
    · have hqp : q < p := lt_of_le_of_ne (hqmin p hpQ) (Ne.symm hpq)
      have hpS : p ∈ sievePrimes q y := mem_sievePrimes.mpr
        ⟨hqp, hQupper p hpQ, hQprime p hpQ⟩
      simp [T, hpS]
  have hF0 : ∀ p ∈ F, 0 ≤ invFactor p := by
    intro p hp
    have hpQ : p ∈ Q := List.mem_toFinset.mp hp
    have hp2 : 2 < p := hq2.trans_le (hqmin p hpQ)
    exact (inv_pos.mpr (sub_pos.mpr (hg p (hQprime p hpQ) hp2).2)).le
  have hTone : ∀ p ∈ T, p ∉ F → 1 ≤ invFactor p := by
    intro p hpT _hpF
    have hpCases : p = q ∨ p ∈ sievePrimes q y := by simpa [T] using hpT
    have hpPrime : p.Prime := by
      rcases hpCases with rfl | hpS
      · exact hQprime p hqmem
      · exact (mem_sievePrimes.mp hpS).2.2
    have hp2 : 2 < p := by
      rcases hpCases with rfl | hpS
      · exact hq2
      · exact hq2.trans (mem_sievePrimes.mp hpS).1
    have hgp := hg p hpPrime hp2
    exact (one_le_inv₀ (sub_pos.mpr hgp.2)).2 (by linarith)
  have hprod : (∏ p ∈ F, invFactor p) ≤ ∏ p ∈ T, invFactor p :=
    Finset.prod_le_prod_of_subset_of_one_le hFsub hF0 hTone
  calc
    (buchstabProduct g Q)⁻¹ = ∏ p ∈ F, invFactor p := by
      unfold buchstabProduct invFactor F
      rw [← List.prod_toFinset (fun p ↦ 1 - g p) hQnodup]
      rw [← Finset.prod_inv_distrib]
    _ ≤ ∏ p ∈ T, invFactor p := hprod
    _ = (1 - g q)⁻¹ * inverseLocalEulerProduct g q y := by
      simp [T, invFactor, inverseLocalEulerProduct, mem_sievePrimes, mul_comm]
    _ ≤ 3 * inverseLocalEulerProduct g q y := by
      apply mul_le_mul_of_nonneg_right hqfactor
      unfold inverseLocalEulerProduct
      apply Finset.prod_nonneg
      intro p hp
      have hp' := mem_sievePrimes.mp hp
      exact (inv_pos.mpr (sub_pos.mpr (hg p hp'.2.2 (by omega)).2)).le

private theorem oneShift_inverseFactor_le_three {q : ℕ} (hq : 3 ≤ q) :
    (1 - oneShiftDensity q)⁻¹ ≤ (3 : ℝ) := by
  have hqR : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have hinv : (q : ℝ)⁻¹ ≤ (3 : ℝ)⁻¹ := by
    simpa [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 3) hqR
  have hden : 0 < 1 - oneShiftDensity q := by
    unfold oneShiftDensity
    have : (q : ℝ)⁻¹ < 1 :=
      inv_lt_one_of_one_lt₀ (lt_of_lt_of_le (by norm_num) hqR)
    linarith
  apply (inv_le_comm₀ hden (by norm_num : (0 : ℝ) < 3)).2
  norm_num [oneShiftDensity] at hinv ⊢
  linarith

private theorem pairShift_inverseFactor_le_three (h : ℕ)
    {q : ℕ} (hq : 3 ≤ q) :
    (1 - pairShiftDensity h q)⁻¹ ≤ (3 : ℝ) := by
  have hqR : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have hinv : (q : ℝ)⁻¹ ≤ (3 : ℝ)⁻¹ := by
    simpa [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 3) hqR
  have hg : pairShiftDensity h q ≤ 2 / 3 := by
    unfold pairShiftDensity
    split_ifs <;> norm_num at hinv ⊢ <;> linarith
  have hden : 0 < 1 - pairShiftDensity h q := by linarith
  apply (inv_le_comm₀ hden (by norm_num : (0 : ℝ) < 3)).2
  norm_num at hg ⊢
  linarith

/-- Dimension-one inverse product bound on the concrete cutoff prefix. -/
theorem oneShift_betaCutoffPrefix_inverse_bound
    {C : ℝ} (hC : 1 ≤ C)
    (hdimension : ∀ z y : ℕ, 2 ≤ z → z ≤ y →
      inverseLocalEulerProduct oneShiftDensity z y ≤
        C * (Real.log (y : ℝ) / Real.log (z : ℝ)))
    {z y r : ℕ} (hz : 2 ≤ z) (hzy : z ≤ y) :
    (buchstabProduct oneShiftDensity (betaCutoffPrefix z y r))⁻¹ ≤
      (3 * C) * Real.rpow betaRatio ((1 : ℝ) * r) := by
  classical
  let Q := betaCutoffPrefix z y r
  change (buchstabProduct oneShiftDensity Q)⁻¹ ≤
    (3 * C) * Real.rpow betaRatio ((1 : ℝ) * r)
  by_cases hQ : Q = []
  · rw [hQ]
    simp only [buchstabProduct, List.map_nil, List.prod_nil, inv_one]
    have hrpow : 1 ≤ Real.rpow betaRatio ((1 : ℝ) * r) :=
      Real.one_le_rpow (by norm_num [betaRatio]) (by positivity)
    calc
      (1 : ℝ) ≤ 3 * C := by nlinarith
      _ ≤ (3 * C) * Real.rpow betaRatio ((1 : ℝ) * r) := by
        simpa only [mul_one] using
          (mul_le_mul_of_nonneg_left hrpow (by positivity : 0 ≤ (3 : ℝ) * C))
  · let q := Q.getLast hQ
    have hqQ : q ∈ Q := List.getLast_mem hQ
    have hQsub : Q.Sublist (descendingSievePrimes z y) := by
      exact (betaCutoffPrefix_isPrefix z y r (by omega)).sublist
    have hqS := mem_sievePrimes.mp
      (mem_descendingSievePrimes.mp (hQsub.subset hqQ))
    have hQdesc : Q.Pairwise (fun p q ↦ q < p) :=
      (descendingSievePrimes_pairwise z y).sublist hQsub
    have hqmin : ∀ p ∈ Q, q ≤ p :=
      getLast_le_of_pairwise_desc hQ hQdesc
    have hqEligible : betaEligible y r q := by
      have hqCut : q ∈ betaCutoffPrefix z y r := by simpa [Q] using hqQ
      have hqBoth : 1 < q ∧ betaEligible y r q := by
        simpa [betaCutoffPrefix] using (List.mem_filter.mp hqCut).2
      exact hqBoth.2
    have hcut : Real.log (y : ℝ) / Real.log (q : ℝ) ≤ betaRatio ^ r := by
      have hpow : betaRatio ^ (r - 1) ≤ betaRatio ^ r :=
        pow_le_pow_right₀ (by norm_num [betaRatio]) (by omega)
      exact hqEligible.le.trans hpow
    have hbase := inverse_buchstabProduct_le_three_mul_inverseLocalEulerProduct
      (g := oneShiftDensity) (Q := Q) (q := q) (y := y)
      (hQsub.nodup (descendingSievePrimes_nodup z y)) hqQ hqmin
      (fun p hp ↦ (mem_sievePrimes.mp
        (mem_descendingSievePrimes.mp (hQsub.subset hp))).2.2)
      (fun p hp ↦ (mem_sievePrimes.mp
        (mem_descendingSievePrimes.mp (hQsub.subset hp))).2.1)
      (by omega)
      (fun p hp _hp2 ↦ ⟨(oneShiftDensity_pos hp).le,
        oneShiftDensity_lt_one hp⟩)
      (oneShift_inverseFactor_le_three (by omega))
    calc
      (buchstabProduct oneShiftDensity Q)⁻¹ ≤
          3 * inverseLocalEulerProduct oneShiftDensity q y := hbase
      _ ≤ 3 * (C * (Real.log (y : ℝ) / Real.log (q : ℝ))) := by
        gcongr
        exact hdimension q y (by omega) hqS.2.1
      _ ≤ (3 * C) * betaRatio ^ r := by
        nlinarith
      _ = (3 * C) * Real.rpow betaRatio ((1 : ℝ) * r) := by
        congr 1
        rw [one_mul]
        exact (Real.rpow_natCast betaRatio r).symm

/-- Dimension-two inverse product bound on the concrete cutoff prefix. -/
theorem pairShift_betaCutoffPrefix_inverse_bound
    {C : ℝ} (hC : 1 ≤ C)
    (hdimension : ∀ h z y : ℕ, 2 ≤ z → z ≤ y →
      inverseLocalEulerProduct (pairShiftDensity h) z y ≤
        C * (Real.log (y : ℝ) / Real.log (z : ℝ)) ^ 2)
    (h : ℕ) {z y r : ℕ} (hz : 2 ≤ z) (hzy : z ≤ y) :
    (buchstabProduct (pairShiftDensity h) (betaCutoffPrefix z y r))⁻¹ ≤
      (3 * C) * Real.rpow betaRatio ((2 : ℝ) * r) := by
  classical
  let Q := betaCutoffPrefix z y r
  change (buchstabProduct (pairShiftDensity h) Q)⁻¹ ≤
    (3 * C) * Real.rpow betaRatio ((2 : ℝ) * r)
  by_cases hQ : Q = []
  · rw [hQ]
    simp only [buchstabProduct, List.map_nil, List.prod_nil, inv_one]
    have hrpow : 1 ≤ Real.rpow betaRatio ((2 : ℝ) * r) :=
      Real.one_le_rpow (by norm_num [betaRatio]) (by positivity)
    calc
      (1 : ℝ) ≤ 3 * C := by nlinarith
      _ ≤ (3 * C) * Real.rpow betaRatio ((2 : ℝ) * r) := by
        simpa only [mul_one] using
          (mul_le_mul_of_nonneg_left hrpow (by positivity : 0 ≤ (3 : ℝ) * C))
  · let q := Q.getLast hQ
    have hqQ : q ∈ Q := List.getLast_mem hQ
    have hQsub : Q.Sublist (descendingSievePrimes z y) :=
      (betaCutoffPrefix_isPrefix z y r (by omega)).sublist
    have hqS := mem_sievePrimes.mp
      (mem_descendingSievePrimes.mp (hQsub.subset hqQ))
    have hQdesc : Q.Pairwise (fun p q ↦ q < p) :=
      (descendingSievePrimes_pairwise z y).sublist hQsub
    have hqmin : ∀ p ∈ Q, q ≤ p :=
      getLast_le_of_pairwise_desc hQ hQdesc
    have hqEligible : betaEligible y r q := by
      have hqCut : q ∈ betaCutoffPrefix z y r := by simpa [Q] using hqQ
      have hqBoth : 1 < q ∧ betaEligible y r q := by
        simpa [betaCutoffPrefix] using (List.mem_filter.mp hqCut).2
      exact hqBoth.2
    have hratio0 : 0 ≤ Real.log (y : ℝ) / Real.log (q : ℝ) := by
      exact div_nonneg (Real.log_nonneg (by exact_mod_cast (show 1 ≤ y by omega)))
        (Real.log_pos (by exact_mod_cast hqS.2.2.one_lt)).le
    have hcut : Real.log (y : ℝ) / Real.log (q : ℝ) ≤ betaRatio ^ r := by
      exact hqEligible.le.trans
        (pow_le_pow_right₀ (by norm_num [betaRatio]) (by omega))
    have hbase := inverse_buchstabProduct_le_three_mul_inverseLocalEulerProduct
      (g := pairShiftDensity h) (Q := Q) (q := q) (y := y)
      (hQsub.nodup (descendingSievePrimes_nodup z y)) hqQ hqmin
      (fun p hp ↦ (mem_sievePrimes.mp
        (mem_descendingSievePrimes.mp (hQsub.subset hp))).2.2)
      (fun p hp ↦ (mem_sievePrimes.mp
        (mem_descendingSievePrimes.mp (hQsub.subset hp))).2.1)
      (by omega)
      (fun p hp hp2 ↦ ⟨(pairShiftDensity_pos hp).le,
        pairShiftDensity_lt_one hp hp2⟩)
      (pairShift_inverseFactor_le_three h (by omega))
    calc
      (buchstabProduct (pairShiftDensity h) Q)⁻¹ ≤
          3 * inverseLocalEulerProduct (pairShiftDensity h) q y := hbase
      _ ≤ 3 * (C * (Real.log (y : ℝ) / Real.log (q : ℝ)) ^ 2) := by
        gcongr
        exact hdimension h q y (by omega) hqS.2.1
      _ ≤ 3 * (C * (betaRatio ^ r) ^ 2) := by
        gcongr
      _ = (3 * C) * Real.rpow betaRatio ((2 : ℝ) * r) := by
        have hrpow : Real.rpow betaRatio ((2 : ℝ) * r) =
            betaRatio ^ (2 * r) := by
          rw [show (2 : ℝ) * (r : ℝ) = ((2 * r : ℕ) : ℝ) by norm_num]
          exact Real.rpow_natCast betaRatio (2 * r)
        rw [hrpow]
        rw [← pow_mul]
        ring

theorem buchstabProduct_descendingSievePrimes
    (g : ℕ → ℝ) (z y : ℕ) :
    buchstabProduct g (descendingSievePrimes z y) =
      localEulerProduct g z y := by
  classical
  unfold buchstabProduct localEulerProduct descendingSievePrimes
  rw [List.map_reverse, List.prod_reverse]
  symm
  simpa using List.prod_toFinset (fun p ↦ 1 - g p)
    (Finset.sort_nodup (sievePrimes z y) (fun a b : ℕ ↦ a ≤ b))

/-- The stopping failure forces every upper boundary term to start at depth
`S-100`. -/
theorem upperFailureTerm_start_depth
    {z y S fuel : ℕ} {t : List ℕ × List ℕ}
    (hy : 1 < y)
    (ht : t ∈ upperFailureTerms (descendingRosserStop 100 (y ^ S))
      fuel [] (descendingSievePrimes z y)) :
    S - 100 ≤ t.1.length := by
  have hfail : ¬ rosserStoppingPredicate 100 (y ^ S) t.1.reverse :=
    upperFailureTerms_not_descendingRosserStoppingPredicate ht
  have hupper : ∀ p ∈ t.1.reverse, p ≤ y := by
    intro p hp
    have hpChain : p ∈ t.1 := by simpa using hp
    have hsub := upperFailureTerms_chain_sublist
      (descendingRosserStop 100 (y ^ S)) fuel []
        (descendingSievePrimes z y) ht
    exact (mem_sievePrimes.mp
      (mem_descendingSievePrimes.mp (hsub.subset hpChain))).2.1
  have hdepth := Erdos851.RosserBoundaryEstimate.stopping_failure_forces_depth
    hy rfl hupper hfail
  simp only [List.length_reverse] at hdepth
  omega

/-- Lower boundary terms have the same forced starting depth. -/
theorem lowerFailureTerm_start_depth
    {z y S fuel : ℕ} {t : List ℕ × List ℕ}
    (hy : 1 < y)
    (ht : t ∈ lowerFailureTerms (descendingRosserStop 100 (y ^ S))
      fuel [] (descendingSievePrimes z y)) :
    S - 100 ≤ t.1.length := by
  have hfail : ¬ rosserStoppingPredicate 100 (y ^ S) t.1.reverse :=
    lowerFailureTerms_not_descendingRosserStoppingPredicate ht
  have hupper : ∀ p ∈ t.1.reverse, p ≤ y := by
    intro p hp
    have hpChain : p ∈ t.1 := by simpa using hp
    have hsub := lowerFailureTerms_chain_sublist
      (descendingRosserStop 100 (y ^ S)) fuel []
        (descendingSievePrimes z y) ht
    exact (mem_sievePrimes.mp
      (mem_descendingSievePrimes.mp (hsub.subset hpChain))).2.1
  have hdepth := Erdos851.RosserBoundaryEstimate.stopping_failure_forces_depth
    hy rfl hupper hfail
  simp only [List.length_reverse] at hdepth
  omega

/-- The LocalEulerProducts dimension-one estimate constructs both concrete
upper and lower per-depth product-ratio bounds, with no abstract sieve
hypothesis remaining. -/
theorem exists_oneShift_concrete_hasDepthProductRatio :
    ∃ A : ℝ, 1 ≤ A ∧
      ∀ z y S fuel : ℕ, 2 ≤ z → z ≤ y → 1 < y → 101 ≤ S →
        let P := descendingSievePrimes z y
        let stop := descendingRosserStop 100 (y ^ S)
        HasDepthProductRatio oneShiftDensity
            (upperFailureTerms stop fuel [] P)
            (localEulerProduct oneShiftDensity z y) A 1 (S - 100) fuel ∧
          HasDepthProductRatio oneShiftDensity
            (lowerFailureTerms stop fuel [] P)
            (localEulerProduct oneShiftDensity z y) A 1 (S - 100) fuel := by
  obtain ⟨C, hC, hdimension⟩ := exists_oneShift_dimension_bound_one_le
  refine ⟨3 * C, by nlinarith, ?_⟩
  intro z y S fuel hz hzy hy hS
  dsimp only
  let P := descendingSievePrimes z y
  let stop := descendingRosserStop 100 (y ^ S)
  have hx0 : ∀ p, 0 ≤ oneShiftDensity p := by
    intro p
    unfold oneShiftDensity
    positivity
  have hx1 : ∀ p ∈ P, oneShiftDensity p < 1 := by
    intro p hp
    exact oneShiftDensity_lt_one
      (mem_sievePrimes.mp (mem_descendingSievePrimes.mp hp)).2.2
  have hV : localEulerProduct oneShiftDensity z y =
      buchstabProduct oneShiftDensity P := by
    exact (buchstabProduct_descendingSievePrimes oneShiftDensity z y).symm
  have hprefix : ∀ r ≤ fuel, betaCutoffPrefix z y r <+: P := by
    intro r _hr
    exact betaCutoffPrefix_isPrefix z y r hy.le
  constructor
  · apply upper_hasDepthProductRatio_of_prefixProductRatio
      stop oneShiftDensity fuel [] (betaCutoffPrefix z y)
      hx0 hx1 (descendingSievePrimes_nodup z y) hV hprefix
    · intro r _hr t ht hlen
      exact upperFailureTerm_chain_sublist_betaCutoffPrefix ht hS hlen
    · intro t ht
      exact upperFailureTerm_start_depth hy ht
    · nlinarith
    · intro r _hr _hstart
      exact oneShift_betaCutoffPrefix_inverse_bound hC hdimension hz hzy
  · apply lower_hasDepthProductRatio_of_prefixProductRatio
      stop oneShiftDensity fuel [] (betaCutoffPrefix z y)
      hx0 hx1 (descendingSievePrimes_nodup z y) hV hprefix
    · intro r _hr t ht hlen
      exact lowerFailureTerm_chain_sublist_betaCutoffPrefix ht hS hlen
    · intro t ht
      exact lowerFailureTerm_start_depth hy ht
    · nlinarith
    · intro r _hr _hstart
      exact oneShift_betaCutoffPrefix_inverse_bound hC hdimension hz hzy

/-- Uniform dimension-two analogue, independent of the shift difference. -/
theorem exists_pairShift_concrete_hasDepthProductRatio :
    ∃ A : ℝ, 1 ≤ A ∧
      ∀ h z y S fuel : ℕ, 2 ≤ z → z ≤ y → 1 < y → 101 ≤ S →
        let P := descendingSievePrimes z y
        let stop := descendingRosserStop 100 (y ^ S)
        HasDepthProductRatio (pairShiftDensity h)
            (upperFailureTerms stop fuel [] P)
            (localEulerProduct (pairShiftDensity h) z y)
            A 2 (S - 100) fuel ∧
          HasDepthProductRatio (pairShiftDensity h)
            (lowerFailureTerms stop fuel [] P)
            (localEulerProduct (pairShiftDensity h) z y)
            A 2 (S - 100) fuel := by
  obtain ⟨C, hC, hdimension⟩ := exists_pairShift_dimension_bound_one_le
  refine ⟨3 * C, by nlinarith, ?_⟩
  intro h z y S fuel hz hzy hy hS
  dsimp only
  let P := descendingSievePrimes z y
  let stop := descendingRosserStop 100 (y ^ S)
  have hx0 : ∀ p, 0 ≤ pairShiftDensity h p := by
    intro p
    unfold pairShiftDensity
    split_ifs <;> positivity
  have hx1 : ∀ p ∈ P, pairShiftDensity h p < 1 := by
    intro p hp
    have hp' := mem_sievePrimes.mp (mem_descendingSievePrimes.mp hp)
    exact pairShiftDensity_lt_one hp'.2.2 (by omega)
  have hV : localEulerProduct (pairShiftDensity h) z y =
      buchstabProduct (pairShiftDensity h) P := by
    exact (buchstabProduct_descendingSievePrimes (pairShiftDensity h) z y).symm
  have hprefix : ∀ r ≤ fuel, betaCutoffPrefix z y r <+: P := by
    intro r _hr
    exact betaCutoffPrefix_isPrefix z y r hy.le
  constructor
  · apply upper_hasDepthProductRatio_of_prefixProductRatio
      stop (pairShiftDensity h) fuel [] (betaCutoffPrefix z y)
      hx0 hx1 (descendingSievePrimes_nodup z y) hV hprefix
    · intro r _hr t ht hlen
      exact upperFailureTerm_chain_sublist_betaCutoffPrefix ht hS hlen
    · intro t ht
      exact upperFailureTerm_start_depth hy ht
    · nlinarith
    · intro r _hr _hstart
      exact pairShift_betaCutoffPrefix_inverse_bound hC hdimension h hz hzy
  · apply lower_hasDepthProductRatio_of_prefixProductRatio
      stop (pairShiftDensity h) fuel [] (betaCutoffPrefix z y)
      hx0 hx1 (descendingSievePrimes_nodup z y) hV hprefix
    · intro r _hr t ht hlen
      exact lowerFailureTerm_chain_sublist_betaCutoffPrefix ht hS hlen
    · intro t ht
      exact lowerFailureTerm_start_depth hy ht
    · nlinarith
    · intro r _hr _hstart
      exact pairShift_betaCutoffPrefix_inverse_bound hC hdimension h hz hzy

/-- Concrete dimension-one finite fundamental lemma in recursive main-term
form.  The displayed logarithmic threshold is the only largeness condition
on `S`; all product-ratio and boundary hypotheses have been discharged. -/
theorem exists_oneShift_concrete_mainTerm_bounds :
    ∃ A : ℝ, 1 ≤ A ∧
      ∀ z y S fuel : ℕ, 2 ≤ z → z ≤ y → 1 < y → 101 ≤ S →
        (descendingSievePrimes z y).length ≤ fuel →
        Real.log A ≤ 2 * (S - 100 : ℕ) / 99 →
        let P := descendingSievePrimes z y
        let stop := descendingRosserStop 100 (y ^ S)
        let V := localEulerProduct oneShiftDensity z y
        let eta := (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)
        (1 - eta) * V ≤ rosserLowerEval stop oneShiftDensity fuel [] P ∧
          rosserUpperEval stop oneShiftDensity fuel [] P ≤ (1 + eta) * V := by
  obtain ⟨A, hA, hdepth⟩ := exists_oneShift_concrete_hasDepthProductRatio
  refine ⟨A, hA, ?_⟩
  intro z y S fuel hz hzy hy hS hfuel hlog
  dsimp only
  let P := descendingSievePrimes z y
  let stop := descendingRosserStop 100 (y ^ S)
  let V := localEulerProduct oneShiftDensity z y
  have hratios := hdepth z y S fuel hz hzy hy hS
  have hbounds := rosserBoundaries_le_geometric_of_depthProductRatio
    stop oneShiftDensity ([] : List ℕ) P
    (oneShift_localEulerProduct_pos (z := z) (y := y)).le
    hA (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (1 : ℝ) ≤ 2)
    hratios.1 hratios.2 (by
      intro r hrstart _hrfuel
      have hstartR : ((S - 100 : ℕ) : ℝ) ≤ r := by exact_mod_cast hrstart
      norm_num
      nlinarith)
  have heq := rosser_eval_sub_product_eq_boundary
    stop oneShiftDensity fuel [] P hfuel
  have hV : buchstabProduct oneShiftDensity P = V := by
    exact buchstabProduct_descendingSievePrimes oneShiftDensity z y
  rw [hV] at heq
  change
    (1 - (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)) * V ≤
        rosserLowerEval stop oneShiftDensity fuel [] P ∧
      rosserUpperEval stop oneShiftDensity fuel [] P ≤
        (1 + (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)) * V
  constructor
  · nlinarith [hbounds.2, heq.2]
  · nlinarith [hbounds.1, heq.1]

/-- Uniform concrete dimension-two finite fundamental lemma. -/
theorem exists_pairShift_concrete_mainTerm_bounds :
    ∃ A : ℝ, 1 ≤ A ∧
      ∀ h z y S fuel : ℕ, 2 ≤ z → z ≤ y → 1 < y → 101 ≤ S →
        (descendingSievePrimes z y).length ≤ fuel →
        Real.log A ≤ 4 * (S - 100 : ℕ) / 99 →
        let P := descendingSievePrimes z y
        let stop := descendingRosserStop 100 (y ^ S)
        let V := localEulerProduct (pairShiftDensity h) z y
        let eta := (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)
        (1 - eta) * V ≤
            rosserLowerEval stop (pairShiftDensity h) fuel [] P ∧
          rosserUpperEval stop (pairShiftDensity h) fuel [] P ≤
            (1 + eta) * V := by
  obtain ⟨A, hA, hdepth⟩ := exists_pairShift_concrete_hasDepthProductRatio
  refine ⟨A, hA, ?_⟩
  intro h z y S fuel hz hzy hy hS hfuel hlog
  dsimp only
  let P := descendingSievePrimes z y
  let stop := descendingRosserStop 100 (y ^ S)
  let V := localEulerProduct (pairShiftDensity h) z y
  have hratios := hdepth h z y S fuel hz hzy hy hS
  have hbounds := rosserBoundaries_le_geometric_of_depthProductRatio
    stop (pairShiftDensity h) ([] : List ℕ) P
    (pairShift_localEulerProduct_pos h (z := z) (y := y) hz).le
    hA (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (2 : ℝ) ≤ 2)
    hratios.1 hratios.2 (by
      intro r hrstart _hrfuel
      have hstartR : ((S - 100 : ℕ) : ℝ) ≤ r := by exact_mod_cast hrstart
      norm_num
      nlinarith)
  have heq := rosser_eval_sub_product_eq_boundary
    stop (pairShiftDensity h) fuel [] P hfuel
  have hV : buchstabProduct (pairShiftDensity h) P = V := by
    exact buchstabProduct_descendingSievePrimes (pairShiftDensity h) z y
  rw [hV] at heq
  change
    (1 - (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)) * V ≤
        rosserLowerEval stop (pairShiftDensity h) fuel [] P ∧
      rosserUpperEval stop (pairShiftDensity h) fuel [] P ≤
        (1 + (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)) * V
  constructor
  · nlinarith [hbounds.2, heq.2]
  · nlinarith [hbounds.1, heq.1]

/-! ### Finite ascending-list formulation -/

/-- Concrete one-dimensional beta-sieve fundamental lemma in the finite
combinatorial-sieve convention.  The input primes are sorted increasingly;
the recursive proof above reads exactly their reverse. -/
theorem exists_oneShift_concrete_finiteMainTerm_bounds :
    ∃ A : ℝ, 1 ≤ A ∧
      ∀ z y S : ℕ, 2 ≤ z → z ≤ y → 1 < y → 101 ≤ S →
        Real.log A ≤ 2 * (S - 100 : ℕ) / 99 →
        let P := (sievePrimes z y).sort (fun a b ↦ a ≤ b)
        let V := localEulerProduct oneShiftDensity z y
        let eta := (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)
        (1 - eta) * V ≤
            lowerMainTerm (rosserStoppingPredicate 100 (y ^ S))
              oneShiftDensity P ∧
          upperMainTerm (rosserStoppingPredicate 100 (y ^ S))
              oneShiftDensity P ≤ (1 + eta) * V := by
  classical
  obtain ⟨A, hA, hmain⟩ := exists_oneShift_concrete_mainTerm_bounds
  refine ⟨A, hA, ?_⟩
  intro z y S hz hzy hy hS hlog
  dsimp only
  let P := (sievePrimes z y).sort (fun a b ↦ a ≤ b)
  have hrecursive := hmain z y S P.length hz hzy hy hS (by
    simp [P, descendingSievePrimes]) hlog
  have hstop : descendingRosserStop 100 (y ^ S) =
      (fun s ↦ decide (rosserStoppingPredicate 100 (y ^ S) s.reverse)) := by
    funext s
    rw [Bool.eq_iff_iff]
    simp [descendingRosserStoppingPredicate]
  rw [Erdos851.FiniteRecursiveBridge.lowerMainTerm_eq_rosserLowerEval,
    Erdos851.FiniteRecursiveBridge.upperMainTerm_eq_rosserUpperEval]
  rw [← hstop]
  simpa [P, descendingSievePrimes] using hrecursive

/-- Concrete two-dimensional finite beta-sieve fundamental lemma, uniformly
in the shift difference `h`. -/
theorem exists_pairShift_concrete_finiteMainTerm_bounds :
    ∃ A : ℝ, 1 ≤ A ∧
      ∀ h z y S : ℕ, 2 ≤ z → z ≤ y → 1 < y → 101 ≤ S →
        Real.log A ≤ 4 * (S - 100 : ℕ) / 99 →
        let P := (sievePrimes z y).sort (fun a b ↦ a ≤ b)
        let V := localEulerProduct (pairShiftDensity h) z y
        let eta := (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)
        (1 - eta) * V ≤
            lowerMainTerm (rosserStoppingPredicate 100 (y ^ S))
              (pairShiftDensity h) P ∧
          upperMainTerm (rosserStoppingPredicate 100 (y ^ S))
              (pairShiftDensity h) P ≤ (1 + eta) * V := by
  classical
  obtain ⟨A, hA, hmain⟩ := exists_pairShift_concrete_mainTerm_bounds
  refine ⟨A, hA, ?_⟩
  intro h z y S hz hzy hy hS hlog
  dsimp only
  let P := (sievePrimes z y).sort (fun a b ↦ a ≤ b)
  have hrecursive := hmain h z y S P.length hz hzy hy hS (by
    simp [P, descendingSievePrimes]) hlog
  have hstop : descendingRosserStop 100 (y ^ S) =
      (fun s ↦ decide (rosserStoppingPredicate 100 (y ^ S) s.reverse)) := by
    funext s
    rw [Bool.eq_iff_iff]
    simp [descendingRosserStoppingPredicate]
  rw [Erdos851.FiniteRecursiveBridge.lowerMainTerm_eq_rosserLowerEval,
    Erdos851.FiniteRecursiveBridge.upperMainTerm_eq_rosserUpperEval]
  rw [← hstop]
  simpa [P, descendingSievePrimes] using hrecursive

end Erdos851.BetaSieveFundamental
