/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos980.External.Erdos387.GeneralBetaChainLogBridge
import ErdosProblems.Erdos851.ConcreteBetaCutoff

/-!
# Concrete cutoff prefixes for a variable-beta sieve

The beta parameter is no longer hardcoded to 100.  At depth `r`, all
first-failure chains lie in the initial segment cut out by

`log y / log p < ((beta+1)/(beta-1))^(r-1)`.
-/

namespace Erdos387.GeneralBetaCutoff

open Erdos851
open Erdos851.BetaSieveFundamental
open Erdos851.FiniteCombinatorialSieve
open Erdos387.GeneralBetaChainRatio
open Erdos387.GeneralBetaChainLogBridge

def betaEligible (beta y r p : ℕ) : Prop :=
  Real.log (y : ℝ) / Real.log (p : ℝ) <
    inflation (beta + 1 : ℝ) ^ (r - 1)

noncomputable def betaCutoffPrefix (beta z y r : ℕ) : List ℕ := by
  classical
  exact (descendingSievePrimes z y).filter fun p ↦
    decide (1 < p ∧ betaEligible beta y r p)

theorem betaEligible_of_lt {beta y r p q : ℕ}
    (hy : 1 ≤ y) (hq : 1 < q) (hqp : q < p)
    (hqEligible : betaEligible beta y r q) : betaEligible beta y r p := by
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
    {α : Type*} {R : α → α → Prop}
    (keep : α → Bool)
    (hup : ∀ {a b}, R a b → keep b = true → keep a = true) :
    ∀ {l : List α}, l.Pairwise R → l.filter keep <+: l := by
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

theorem betaCutoffPrefix_isPrefix (beta z y r : ℕ) (hy : 1 ≤ y) :
    betaCutoffPrefix beta z y r <+: descendingSievePrimes z y := by
  classical
  apply filter_isPrefix_of_pairwise_upward
    (fun p ↦ decide (1 < p ∧ betaEligible beta y r p))
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
    {beta z y r : ℕ} {chain : List ℕ}
    (hy : 1 ≤ y) (hsub : chain.Sublist (descendingSievePrimes z y))
    (hnonempty : chain ≠ [])
    (hterminal : Real.log (y : ℝ) /
        Real.log (chain.getD (chain.length - 1) 2 : ℝ) <
      inflation (beta + 1 : ℝ) ^ (r - 1)) :
    chain.Sublist (betaCutoffPrefix beta z y r) := by
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
  have hqEligible : betaEligible beta y r q := by
    unfold betaEligible
    rw [hget] at hterminal
    exact hterminal
  have hchainEligible : ∀ p ∈ chain, 1 < p ∧ betaEligible beta y r p := by
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
      (fun p ↦ decide (1 < p ∧ betaEligible beta y r p)) = chain :=
    List.filter_eq_self.mpr (fun p hp ↦ by simp [hchainEligible p hp])
  have hf := hsub.filter
    (fun p ↦ decide (1 < p ∧ betaEligible beta y r p))
  simpa only [hfiltered, betaCutoffPrefix] using hf

theorem upperFailureTerm_chain_sublist_betaCutoffPrefix
    {beta z y S fuel r : ℕ} {t : List ℕ × List ℕ}
    (ht : t ∈ upperFailureTerms (descendingRosserStop beta (y ^ S))
      fuel [] (descendingSievePrimes z y))
    (hbeta : 2 ≤ beta) (hS : beta + 1 ≤ S)
    (hlen : t.1.length = r) :
    t.1.Sublist (betaCutoffPrefix beta z y r) := by
  have hsub := upperFailureTerms_chain_sublist
    (descendingRosserStop beta (y ^ S)) fuel []
      (descendingSievePrimes z y) ht
  have hlarge : ∀ p ∈ descendingSievePrimes z y, 1 < p := by
    intro p hp
    exact (mem_sievePrimes.mp (mem_descendingSievePrimes.mp hp)).2.2.one_lt
  have hupper : ∀ p ∈ descendingSievePrimes z y, p ≤ y := by
    intro p hp
    exact (mem_sievePrimes.mp (mem_descendingSievePrimes.mp hp)).2.1
  have hcut := upperFailureTerm_log_ratio_lt_inflation_pow ht hlarge hupper
    (descendingSievePrimes_pairwise z y) hbeta hS
  have hnonempty : t.1 ≠ [] := by
    obtain ⟨k, hk⟩ := upperFailureTerms_chain_length_odd
      (descendingRosserStop beta (y ^ S)) fuel []
        (descendingSievePrimes z y) ht
    intro hempty
    rw [hempty] at hk
    simp at hk
  have hy : 1 ≤ y := by
    have hlastmem := List.getLast_mem hnonempty
    exact (hlarge _ (hsub.subset hlastmem)).le.trans
      (hupper _ (hsub.subset hlastmem))
  apply chain_sublist_betaCutoffPrefix_of_terminal hy hsub hnonempty
  simpa [hlen] using hcut

theorem lowerFailureTerm_chain_sublist_betaCutoffPrefix
    {beta z y S fuel r : ℕ} {t : List ℕ × List ℕ}
    (ht : t ∈ lowerFailureTerms (descendingRosserStop beta (y ^ S))
      fuel [] (descendingSievePrimes z y))
    (hbeta : 2 ≤ beta) (hS : beta + 1 ≤ S)
    (hlen : t.1.length = r) :
    t.1.Sublist (betaCutoffPrefix beta z y r) := by
  have hsub := lowerFailureTerms_chain_sublist
    (descendingRosserStop beta (y ^ S)) fuel []
      (descendingSievePrimes z y) ht
  have hlarge : ∀ p ∈ descendingSievePrimes z y, 1 < p := by
    intro p hp
    exact (mem_sievePrimes.mp (mem_descendingSievePrimes.mp hp)).2.2.one_lt
  have hupper : ∀ p ∈ descendingSievePrimes z y, p ≤ y := by
    intro p hp
    exact (mem_sievePrimes.mp (mem_descendingSievePrimes.mp hp)).2.1
  have hcut := lowerFailureTerm_log_ratio_lt_inflation_pow ht hlarge hupper
    (descendingSievePrimes_pairwise z y) hbeta hS
  have hnonempty : t.1 ≠ [] := by
    obtain ⟨_init, _last, _before, hchain, _hrem⟩ :=
      ((failureTerms_structure (descendingRosserStop beta (y ^ S))
        fuel [] (descendingSievePrimes z y)).2 t ht).2
    rw [hchain]
    simp
  have hy : 1 ≤ y := by
    have hlastmem := List.getLast_mem hnonempty
    exact (hlarge _ (hsub.subset hlastmem)).le.trans
      (hupper _ (hsub.subset hlastmem))
  apply chain_sublist_betaCutoffPrefix_of_terminal hy hsub hnonempty
  simpa [hlen] using hcut

/-- Generic forced starting depth `S-beta`. -/
theorem upperFailureTerm_start_depth
    {beta z y S fuel : ℕ} {t : List ℕ × List ℕ}
    (hy : 1 < y)
    (ht : t ∈ upperFailureTerms (descendingRosserStop beta (y ^ S))
      fuel [] (descendingSievePrimes z y)) :
    S - beta ≤ t.1.length := by
  have hfail : ¬ rosserStoppingPredicate beta (y ^ S) t.1.reverse :=
    upperFailureTerms_not_descendingRosserStoppingPredicate ht
  have hupper : ∀ p ∈ t.1.reverse, p ≤ y := by
    intro p hp
    have hpChain : p ∈ t.1 := by simpa using hp
    have hsub := upperFailureTerms_chain_sublist
      (descendingRosserStop beta (y ^ S)) fuel []
        (descendingSievePrimes z y) ht
    exact (mem_sievePrimes.mp
      (mem_descendingSievePrimes.mp (hsub.subset hpChain))).2.1
  have hdepth := Erdos851.RosserBoundaryEstimate.stopping_failure_forces_depth
    hy rfl hupper hfail
  simp only [List.length_reverse] at hdepth
  omega

theorem lowerFailureTerm_start_depth
    {beta z y S fuel : ℕ} {t : List ℕ × List ℕ}
    (hy : 1 < y)
    (ht : t ∈ lowerFailureTerms (descendingRosserStop beta (y ^ S))
      fuel [] (descendingSievePrimes z y)) :
    S - beta ≤ t.1.length := by
  have hfail : ¬ rosserStoppingPredicate beta (y ^ S) t.1.reverse :=
    lowerFailureTerms_not_descendingRosserStoppingPredicate ht
  have hupper : ∀ p ∈ t.1.reverse, p ≤ y := by
    intro p hp
    have hpChain : p ∈ t.1 := by simpa using hp
    have hsub := lowerFailureTerms_chain_sublist
      (descendingRosserStop beta (y ^ S)) fuel []
        (descendingSievePrimes z y) ht
    exact (mem_sievePrimes.mp
      (mem_descendingSievePrimes.mp (hsub.subset hpChain))).2.1
  have hdepth := Erdos851.RosserBoundaryEstimate.stopping_failure_forces_depth
    hy rfl hupper hfail
  simp only [List.length_reverse] at hdepth
  omega

end Erdos387.GeneralBetaCutoff
