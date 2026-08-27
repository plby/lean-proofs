/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTTensorDenominators

/-!
# Exact density cancellation between the full and face main constants

The final shifted denominator is `p - 1`. Its rough Euler factors are
exactly one, so its harmonic main constant is the totient density.
-/

namespace Erdos4b.FGKMT

noncomputable section

open Filter
open scoped BigOperators Topology

theorem sieveEulerFactor_primeMinusOne {M p : ℕ} (hp : p.Prime) :
    sieveEulerFactor M (fun q => (q : ℝ) - 1) p =
      if p ∣ M then 1 - 1 / (p : ℝ) else 1 := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hp1 : (p : ℝ) - 1 ≠ 0 := by
    have h : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    linarith
  unfold sieveEulerFactor
  split_ifs <;> field_simp <;> ring

theorem sieveMainConstant_primeMinusOne {M : ℕ} (hM : 0 < M) :
    sieveMainConstant M (fun p => (p : ℝ) - 1) = (M.totient : ℝ) / M := by
  have hs := (harmonicCorrection_roughSieveWeight_moments (k := 1) (by omega) hM
    (fun p hp hpk => by have hp2 := hp.two_le; norm_num at hpk; omega)
    (fun p => (p : ℝ) - 1)
    (fun p hp _ => by
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
      linarith)
    (fun p _ _ => by norm_num)).1
  have hevent : (fun N : ℕ => ∏ p ∈ N.primesBelow,
      sieveEulerFactor M (fun q => (q : ℝ) - 1) p) =ᶠ[atTop]
        (fun _ => (M.totient : ℝ) / M) := by
    filter_upwards [eventually_ge_atTop (M + 1)] with N hN
    calc
      _ = ∏ p ∈ N.primesBelow, (if p ∣ M then 1 - 1 / (p : ℝ) else 1) := by
        apply Finset.prod_congr rfl
        intro p hp
        exact sieveEulerFactor_primeMinusOne (Nat.prime_of_mem_primesBelow hp)
      _ = ∏ p ∈ N.primesBelow.filter (fun p => p ∣ M), (1 - 1 / (p : ℝ)) := by
        rw [Finset.prod_filter]
      _ = _ := by
        rw [primeFactors_eq_filtered_primesBelow hM (by omega), primeFactors_totientProduct hM]
  exact tendsto_nhds_unique (sieveMainConstant_eulerProduct hs)
    (tendsto_const_nhds.congr' hevent.symm)

theorem actual_multivariateSieveConstant_last_coordinate (m : ℕ) {M : ℕ} (hM : 0 < M) :
    multivariateSieveConstant M (actualSieveDenominator false (m + 1)) (m + 1) =
      multivariateSieveConstant M (actualSieveDenominator false (m + 1)) m *
        ((M.totient : ℝ) / M) := by
  have hg : (fun p => actualSieveDenominator false (m + 1) p + (m : ℝ)) =
      (fun p : ℕ => (p : ℝ) - 1) := by
    funext p
    simp only [actualSieveDenominator, Bool.false_eq_true, if_false,
      Nat.cast_add, Nat.cast_one]
    ring
  unfold multivariateSieveConstant
  rw [Finset.prod_range_succ, hg, sieveMainConstant_primeMinusOne hM]

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.sieveMainConstant_primeMinusOne
#print axioms Erdos4b.FGKMT.actual_multivariateSieveConstant_last_coordinate
