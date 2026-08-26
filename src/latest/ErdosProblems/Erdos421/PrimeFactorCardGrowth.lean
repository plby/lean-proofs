import Mathlib.Data.Nat.Squarefree
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Tactic

/-! # Any fixed exponential in the number of prime factors has subpower growth -/

namespace Erdos421

open Filter

theorem primeFactorCard_power_bound {c ε : ℝ} (hc : 1 ≤ c) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n →
      c ^ n.primeFactors.card ≤ C * (n : ℝ) ^ ε := by
  have hlarge : ∀ᶠ n : ℕ in atTop, c ≤ (n : ℝ) ^ ε :=
    ((tendsto_rpow_atTop hε).comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop c)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hlarge
  refine ⟨c ^ N, pow_pos (lt_of_lt_of_le zero_lt_one hc) _, ?_⟩
  intro n hn
  let S := n.primeFactors.filter (fun p ↦ p < N)
  let T := n.primeFactors.filter (fun p ↦ ¬p < N)
  have hsplit : n.primeFactors = S ∪ T := by
    simp only [S, T, Finset.filter_union_filter_not_eq]
  have hdisj : Disjoint S T := Finset.disjoint_filter_filter_not _ _ _
  have hSN : S.card ≤ N := by
    calc
      _ ≤ (Finset.range N).card := Finset.card_le_card (by
        intro p hp
        exact Finset.mem_range.mpr (Finset.mem_filter.mp hp).2)
      _ = _ := Finset.card_range N
  have hT : c ^ T.card ≤ ∏ p ∈ T, (p : ℝ) ^ ε := by
    rw [← Finset.prod_const]
    apply Finset.prod_le_prod (fun _ _ ↦ (zero_le_one.trans hc))
    intro p hp
    exact hN p (by have := (Finset.mem_filter.mp hp).2; omega)
  have hprod : (∏ p ∈ T, (p : ℝ) ^ ε) ≤ (n : ℝ) ^ ε := by
    calc
      _ ≤ ∏ p ∈ n.primeFactors, (p : ℝ) ^ ε := by
        apply Finset.prod_le_prod_of_subset_of_one_le (Finset.filter_subset _ _)
          (fun p _ ↦ Real.rpow_nonneg (Nat.cast_nonneg p) _)
        intro p hp _
        apply Real.one_le_rpow
        · exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_le
        · exact hε.le
      _ = (∏ p ∈ n.primeFactors, (p : ℝ)) ^ ε := by
        exact Real.finsetProd_rpow _ _ (fun p _ ↦ Nat.cast_nonneg p) ε
      _ ≤ (n : ℝ) ^ ε := by
        apply Real.rpow_le_rpow (by positivity) _ hε.le
        rw [← Nat.cast_prod]
        exact_mod_cast Nat.le_of_dvd hn n.prod_primeFactors_dvd
  rw [hsplit, Finset.card_union_of_disjoint hdisj, pow_add]
  exact mul_le_mul (pow_le_pow_right₀ hc hSN) (hT.trans hprod) (by positivity) (by positivity)

end Erdos421
