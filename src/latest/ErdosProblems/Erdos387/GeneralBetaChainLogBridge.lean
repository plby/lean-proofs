/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos387.GeneralBetaChainRatio
import ErdosProblems.Erdos851.BetaStoppingGeometry

/-!
# Variable-beta Rosser stopping decisions as logarithmic cutoffs

This transports `GeneralBetaChainRatio` to the decreasing prime chains used
by the finite Rosser recursion.  It is the arbitrary-beta counterpart of the
beta-100-only `Erdos851.BetaChainLogBridge`.
-/

namespace Erdos387.GeneralBetaChainLogBridge

open scoped BigOperators
open Erdos851
open Erdos851.FiniteCombinatorialSieve
open Erdos851.BetaSieveFundamental
open Erdos387.GeneralBetaChainRatio

private theorem sum_range_getD_eq_sum_map_take
    {α M : Type*} [AddCommMonoid M]
    (f : α → M) (fallback : α) (l : List α) :
    ∀ {n : ℕ}, n ≤ l.length →
      (∑ i ∈ Finset.range n, f (l.getD i fallback)) =
        (l.take n |>.map f).sum := by
  intro n hn
  induction n with
  | zero => simp
  | succ n ih =>
      have hnlt : n < l.length := by omega
      rw [Finset.sum_range_succ, ih (by omega)]
      simp only [List.map_take]
      rw [List.take_add_one]
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hnlt]

theorem betaFunctional_log_getD_eq
    {beta : ℕ} {chain : List ℕ} (hlarge : ∀ q ∈ chain, 1 < q)
    {j : ℕ} (hj : j < chain.length) :
    functional (beta + 1 : ℝ)
        (fun i ↦ Real.log (chain.getD i 2 : ℝ)) j =
      Real.log (((chain.take j).prod *
        (chain.getD j 2) ^ (beta + 1) : ℕ) : ℝ) := by
  have hget : chain.getD j 2 = chain[j] := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
  have hprodne : ∀ x ∈ (chain.take j).map (fun q : ℕ ↦ (q : ℝ)), x ≠ 0 := by
    intro x hx
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx
    have hqmem : q ∈ chain := List.mem_of_mem_take hq
    exact_mod_cast (Nat.ne_of_gt (lt_trans Nat.zero_lt_one (hlarge q hqmem)))
  rw [functional]
  rw [sum_range_getD_eq_sum_map_take (fun q : ℕ ↦ Real.log (q : ℝ)) 2
    chain hj.le]
  rw [hget]
  simp only [Nat.cast_mul, Nat.cast_pow]
  rw [Nat.cast_list_prod]
  rw [Real.log_mul]
  · rw [Real.log_list_prod hprodne, Real.log_pow]
    simp [List.map_map, Function.comp_def]
  · exact List.prod_ne_zero (fun hz ↦ hprodne 0 hz rfl)
  · have hjlarge : 1 < chain[j] := hlarge chain[j] (List.getElem_mem hj)
    apply pow_ne_zero
    exact_mod_cast (Nat.ne_of_gt (lt_trans Nat.zero_lt_one hjlarge))

theorem betaFunctional_le_of_descendingRosserStop_take
    {beta : ℕ} {chain : List ℕ} {y S j : ℕ}
    (hlarge : ∀ q ∈ chain, 1 < q) (_hy : 1 < y)
    (hj : j < chain.length)
    (hpass : descendingRosserStop beta (y ^ S) (chain.take (j + 1)) = true) :
    functional (beta + 1 : ℝ)
        (fun i ↦ Real.log (chain.getD i 2 : ℝ)) j ≤
      (S : ℝ) * Real.log (y : ℝ) := by
  have hpred : descendingRosserStoppingPredicate beta (y ^ S)
      (chain.take (j + 1)) := descendingRosserStop_eq_true.mp hpass
  have htake : chain.take (j + 1) = chain.take j ++ [chain[j]] :=
    (List.take_append_getElem hj).symm
  have hnat : (chain.take j).prod * chain[j] ^ (beta + 1) ≤ y ^ S := by
    rw [htake, descendingRosserStoppingPredicate_append_singleton] at hpred
    simpa using hpred
  have hcast :
      (((chain.take j).prod * chain[j] ^ (beta + 1) : ℕ) : ℝ) ≤
        ((y ^ S : ℕ) : ℝ) := by exact_mod_cast hnat
  have hleft : (0 : ℝ) <
      (((chain.take j).prod * chain[j] ^ (beta + 1) : ℕ) : ℝ) := by
    have hprod : (chain.take j).prod ≠ 0 := by
      apply List.prod_ne_zero
      intro hz
      have hzmem : 0 ∈ chain := List.mem_of_mem_take hz
      exact (Nat.not_succ_le_zero 1) (hlarge 0 hzmem)
    have hq : chain[j] ≠ 0 := Nat.ne_of_gt (lt_trans Nat.zero_lt_one
      (hlarge chain[j] (List.getElem_mem hj)))
    exact_mod_cast Nat.pos_of_ne_zero (mul_ne_zero hprod (pow_ne_zero _ hq))
  have hlog := Real.log_le_log hleft hcast
  rw [betaFunctional_log_getD_eq (beta := beta) hlarge hj]
  simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj,
    Nat.cast_pow, Real.log_pow] using hlog

theorem betaFunctional_gt_of_not_descendingRosserStop_take
    {beta : ℕ} {chain : List ℕ} {y S j : ℕ}
    (hlarge : ∀ q ∈ chain, 1 < q) (hy : 1 < y)
    (hj : j < chain.length)
    (hfail : descendingRosserStop beta (y ^ S) (chain.take (j + 1)) = false) :
    (S : ℝ) * Real.log (y : ℝ) <
      functional (beta + 1 : ℝ)
        (fun i ↦ Real.log (chain.getD i 2 : ℝ)) j := by
  have hnot : ¬ descendingRosserStoppingPredicate beta (y ^ S)
      (chain.take (j + 1)) := descendingRosserStop_eq_false.mp hfail
  have htake : chain.take (j + 1) = chain.take j ++ [chain[j]] :=
    (List.take_append_getElem hj).symm
  have hnat : y ^ S < (chain.take j).prod * chain[j] ^ (beta + 1) := by
    rw [htake, descendingRosserStoppingPredicate_append_singleton] at hnot
    norm_num at hnot
    omega
  have hcast : ((y ^ S : ℕ) : ℝ) <
      (((chain.take j).prod * chain[j] ^ (beta + 1) : ℕ) : ℝ) := by
    exact_mod_cast hnat
  have hleft : (0 : ℝ) < ((y ^ S : ℕ) : ℝ) := by
    exact_mod_cast pow_pos (lt_trans Nat.zero_lt_one hy) S
  have hlog := Real.log_lt_log hleft hcast
  rw [betaFunctional_log_getD_eq (beta := beta) hlarge hj]
  simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj,
    Nat.cast_pow, Real.log_pow] using hlog

/-- Rigorous logarithmic cutoff for a variable-beta first-failure chain. -/
theorem log_ratio_lt_inflation_pow_of_firstFailureChain
    {beta : ℕ} {chain : List ℕ} {y S : ℕ}
    (hnonempty : chain ≠ [])
    (hlarge : ∀ q ∈ chain, 1 < q)
    (hupper : ∀ q ∈ chain, q ≤ y)
    (hdesc : chain.Pairwise (fun p q ↦ q < p))
    (hbeta : 2 ≤ beta) (hS : beta + 1 ≤ S)
    (hproper : ∀ n, 0 < n → n < chain.length →
      n % 2 = chain.length % 2 →
      descendingRosserStop beta (y ^ S) (chain.take n) = true)
    (hterminal : descendingRosserStop beta (y ^ S) chain = false) :
    Real.log (y : ℝ) /
        Real.log (chain.getD (chain.length - 1) 2 : ℝ) <
      inflation (beta + 1 : ℝ) ^ (chain.length - 1) := by
  let r := chain.length - 1
  let a : ℕ → ℝ := fun i ↦ Real.log (chain.getD i 2 : ℝ)
  have hlenpos : 0 < chain.length := by
    apply Nat.pos_of_ne_zero
    simpa [List.length_eq_zero_iff] using hnonempty
  have hfirstmem : chain[0] ∈ chain := List.getElem_mem hlenpos
  have hy : 1 < y := (hlarge chain[0] hfirstmem).trans_le
    (hupper chain[0] hfirstmem)
  have hrlt : r < chain.length := by dsimp [r]; omega
  have hget (i : ℕ) (hi : i < chain.length) : chain.getD i 2 = chain[i] := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  have hpos : ∀ i ≤ r, 0 < a i := by
    intro i hi
    have hil : i < chain.length := by dsimp [r] at hi; omega
    have hilarge : 1 < chain[i] := hlarge chain[i] (List.getElem_mem hil)
    dsimp [a]
    rw [hget i hil]
    exact Real.log_pos (by exact_mod_cast hilarge)
  have hcap : ∀ i ≤ r, a i ≤ Real.log (y : ℝ) := by
    intro i hi
    have hil : i < chain.length := by dsimp [r] at hi; omega
    have himem : chain[i] ∈ chain := List.getElem_mem hil
    have hiupper : chain[i] ≤ y := hupper chain[i] himem
    have hilarge : 1 < chain[i] := hlarge chain[i] himem
    dsimp [a]
    rw [hget i hil]
    apply Real.log_le_log
    · exact_mod_cast (lt_trans Nat.zero_lt_one hilarge)
    · exact_mod_cast hiupper
  have hmono : ∀ i < r, a (i + 1) ≤ a i := by
    intro i hi
    have hi0 : i < chain.length := by dsimp [r] at hi; omega
    have hi1 : i + 1 < chain.length := by dsimp [r] at hi; omega
    have hpq : chain[i + 1] < chain[i] :=
      List.pairwise_iff_getElem.mp hdesc i (i + 1) hi0 hi1 (by omega)
    dsimp [a]
    rw [hget i hi0, hget (i + 1) hi1]
    apply Real.log_le_log
    · exact_mod_cast lt_trans Nat.zero_lt_one
        (hlarge chain[i + 1] (List.getElem_mem hi1))
    · exact_mod_cast hpq.le
  have hproper' : ∀ j < r, j % 2 = r % 2 →
      functional (beta + 1 : ℝ) a j ≤
        (S : ℝ) * Real.log (y : ℝ) := by
    intro j hj hjpar
    have hjl : j < chain.length := by omega
    apply betaFunctional_le_of_descendingRosserStop_take hlarge hy hjl
    apply hproper (j + 1) (by omega) (by omega)
    dsimp [r] at hjpar
    omega
  have hterminalTake :
      descendingRosserStop beta (y ^ S) (chain.take (r + 1)) = false := by
    have hrlen : r + 1 = chain.length := by dsimp [r]; omega
    simpa [hrlen] using hterminal
  have hterminal' : (S : ℝ) * Real.log (y : ℝ) <
      functional (beta + 1 : ℝ) a r := by
    exact betaFunctional_gt_of_not_descendingRosserStop_take
      hlarge hy hrlt hterminalTake
  apply terminal_ratio (beta + 1 : ℝ) a (Real.log (y : ℝ)) (S : ℝ) r
  · exact_mod_cast (show 2 < beta + 1 by omega)
  · exact_mod_cast hS
  · exact hpos
  · exact hcap
  · exact hmono
  · exact hproper'
  · exact hterminal'

theorem upperFailureTerm_log_ratio_lt_inflation_pow
    {beta fuel y S : ℕ} {remaining : List ℕ} {t : List ℕ × List ℕ}
    (ht : t ∈ upperFailureTerms (descendingRosserStop beta (y ^ S))
      fuel [] remaining)
    (hlarge : ∀ q ∈ remaining, 1 < q)
    (hupper : ∀ q ∈ remaining, q ≤ y)
    (hdesc : remaining.Pairwise (fun p q ↦ q < p))
    (hbeta : 2 ≤ beta) (hS : beta + 1 ≤ S) :
    Real.log (y : ℝ) /
        Real.log (t.1.getD (t.1.length - 1) 2 : ℝ) <
      inflation (beta + 1 : ℝ) ^ (t.1.length - 1) := by
  have hsub := upperFailureTerms_chain_sublist
    (descendingRosserStop beta (y ^ S)) fuel [] remaining ht
  have htodd := upperFailureTerms_chain_length_odd
    (descendingRosserStop beta (y ^ S)) fuel [] remaining ht
  have hnonempty : t.1 ≠ [] := by
    intro hempty
    obtain ⟨k, hk⟩ := htodd
    rw [hempty] at hk
    simp at hk
  have hproper : ∀ n, 0 < n → n < t.1.length →
      n % 2 = t.1.length % 2 →
      descendingRosserStop beta (y ^ S) (t.1.take n) = true := by
    intro n hnpos hnlt hpar
    have hnodd : Odd n := by
      apply Nat.odd_iff.mpr
      rw [hpar]
      exact Nat.odd_iff.mp htodd
    simpa using upperFailureTerms_sameParity_prefix_passes
      (descendingRosserStop beta (y ^ S)) fuel [] remaining ht
      hnpos hnlt hnodd
  have hterminal : descendingRosserStop beta (y ^ S) t.1 = false := by
    simpa using upperFailureTerms_terminal_failure
      (descendingRosserStop beta (y ^ S)) fuel [] remaining ht
  exact log_ratio_lt_inflation_pow_of_firstFailureChain hnonempty
    (fun q hq ↦ hlarge q (hsub.subset hq))
    (fun q hq ↦ hupper q (hsub.subset hq))
    (hdesc.sublist hsub) hbeta hS hproper hterminal

theorem lowerFailureTerm_log_ratio_lt_inflation_pow
    {beta fuel y S : ℕ} {remaining : List ℕ} {t : List ℕ × List ℕ}
    (ht : t ∈ lowerFailureTerms (descendingRosserStop beta (y ^ S))
      fuel [] remaining)
    (hlarge : ∀ q ∈ remaining, 1 < q)
    (hupper : ∀ q ∈ remaining, q ≤ y)
    (hdesc : remaining.Pairwise (fun p q ↦ q < p))
    (hbeta : 2 ≤ beta) (hS : beta + 1 ≤ S) :
    Real.log (y : ℝ) /
        Real.log (t.1.getD (t.1.length - 1) 2 : ℝ) <
      inflation (beta + 1 : ℝ) ^ (t.1.length - 1) := by
  have hsub := lowerFailureTerms_chain_sublist
    (descendingRosserStop beta (y ^ S)) fuel [] remaining ht
  have hteven := lowerFailureTerms_chain_length_even
    (descendingRosserStop beta (y ^ S)) fuel [] remaining ht
  have hnonempty : t.1 ≠ [] := by
    obtain ⟨_init, _last, _before, hchain, _hrem⟩ :=
      ((failureTerms_structure (descendingRosserStop beta (y ^ S))
        fuel [] remaining).2 t ht).2
    rw [hchain]
    simp
  have hproper : ∀ n, 0 < n → n < t.1.length →
      n % 2 = t.1.length % 2 →
      descendingRosserStop beta (y ^ S) (t.1.take n) = true := by
    intro n hnpos hnlt hpar
    have hneven : Even n := by
      apply Nat.even_iff.mpr
      rw [hpar]
      exact Nat.even_iff.mp hteven
    simpa using lowerFailureTerms_sameParity_prefix_passes
      (descendingRosserStop beta (y ^ S)) fuel [] remaining ht
      hnpos hnlt hneven
  have hterminal : descendingRosserStop beta (y ^ S) t.1 = false := by
    simpa using lowerFailureTerms_terminal_failure
      (descendingRosserStop beta (y ^ S)) fuel [] remaining ht
  exact log_ratio_lt_inflation_pow_of_firstFailureChain hnonempty
    (fun q hq ↦ hlarge q (hsub.subset hq))
    (fun q hq ↦ hupper q (hsub.subset hq))
    (hdesc.sublist hsub) hbeta hS hproper hterminal

end Erdos387.GeneralBetaChainLogBridge
