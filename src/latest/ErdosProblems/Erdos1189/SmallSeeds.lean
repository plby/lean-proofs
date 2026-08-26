/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Squarefree seeds of bounded size, supported on smaller primes.
Informal source: Section 6.3 of Pickhardt and Omniscience Research Agent,
"Irreducible Covering Sets: A Solution of Erdős Problem 1189".
The quarter-density estimate suffices in place of the exact squarefree asymptotic.
Formal author: OpenAI Codex.
-/

import ErdosProblems.Erdos1189.SquarefreeSupply
import ErdosProblems.Erdos1189.PrimeEstimates

namespace Erdos1189

open Finset Filter

def largePrimeDivisorUpto (q N : ℕ) : Finset ℕ :=
  (Ioc 0 N).filter fun n => ∃ p ∈ n.primeFactors, q ≤ p

def smallSquarefreeSeeds (q N : ℕ) : Finset ℕ :=
  (squarefreeUpto N).filter fun n => ∀ p ∈ n.primeFactors, p < q

lemma largePrimeDivisor_count_le (q C : ℕ) :
    (largePrimeDivisorUpto q (C * q)).card ≤ C * Nat.primeCounting (C * q) := by
  have hsub : largePrimeDivisorUpto q (C * q) ⊆
      ((Nat.primesLE (C * q)) ×ˢ Icc 1 C).image (fun t : ℕ × ℕ => t.1 * t.2) := by
    intro n hn
    obtain ⟨hnI, p, hpn, hqp⟩ := mem_filter.mp hn
    obtain ⟨hn0, hnN⟩ := mem_Ioc.mp hnI
    have hp := Nat.prime_of_mem_primeFactors hpn
    have hpd := Nat.dvd_of_mem_primeFactors hpn
    have hpnle : p ≤ n := Nat.le_of_dvd hn0 hpd
    have hpN : p ∈ Nat.primesLE (C * q) := Nat.mem_primesLE.mpr ⟨hpnle.trans hnN, hp⟩
    have ha : 0 < n / p := Nat.div_pos hpnle hp.pos
    have hmul : p * (n / p) ≤ p * C := by
      rw [Nat.mul_div_cancel' hpd]
      exact hnN.trans (by nlinarith)
    have haC : n / p ≤ C := Nat.le_of_mul_le_mul_left hmul hp.pos
    exact mem_image.mpr ⟨(p, n / p), mem_product.mpr ⟨hpN, mem_Icc.mpr ⟨ha, haC⟩⟩,
      Nat.mul_div_cancel' hpd⟩
  calc
    _ ≤ (((Nat.primesLE (C * q)) ×ˢ Icc 1 C).image
        (fun t : ℕ × ℕ => t.1 * t.2)).card := card_le_card hsub
    _ ≤ ((Nat.primesLE (C * q)) ×ˢ Icc 1 C).card := card_image_le
    _ = C * Nat.primeCounting (C * q) := by
      rw [card_product, Nat.primesLE_card_eq_primeCounting, Nat.card_Icc]
      simp [Nat.mul_comm]

lemma squarefree_count_le_seed_add_large (q N : ℕ) :
    (squarefreeUpto N).card ≤
      (smallSquarefreeSeeds q N).card + (largePrimeDivisorUpto q N).card := by
  have hsub : squarefreeUpto N ⊆ smallSquarefreeSeeds q N ∪ largePrimeDivisorUpto q N := by
    intro n hn
    by_cases hsmall : ∀ p ∈ n.primeFactors, p < q
    · exact mem_union_left _ (mem_filter.mpr ⟨hn, hsmall⟩)
    · apply mem_union_right
      apply mem_filter.mpr
      refine ⟨(mem_filter.mp hn).1, ?_⟩
      simpa only [not_forall, not_lt, exists_prop] using hsmall
  exact (card_le_card hsub).trans (card_union_le _ _)

/-- For every sufficiently large cutoff `q`, there are at least `3q` squarefree
seeds at most `16q` whose prime factors are all smaller than `q`. -/
theorem eventually_small_squarefree_seeds :
    ∀ᶠ q : ℕ in atTop, 3 * q ≤ (smallSquarefreeSeeds q (16 * q)).card := by
  filter_upwards [eventually_primeCounting_mul_le 16 (ε := 1 / 16) (by norm_num)] with q hpi
  have hpi' : 16 * Nat.primeCounting (16 * q) ≤ q := by
    have hh : (16 : ℝ) * Nat.primeCounting (16 * q) ≤ q := by linarith
    exact_mod_cast hh
  have hbad := (largePrimeDivisor_count_le q 16).trans hpi'
  have hsf := squarefree_count_quarter (16 * q)
  have hpart := squarefree_count_le_seed_add_large q (16 * q)
  omega

end Erdos1189
