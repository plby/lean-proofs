import ErdosProblems.Erdos4.FGKMTFiniteLaw
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Exp

/-! Finite Euler expansions turn divisor-event estimates into moment estimates. -/

open scoped BigOperators

namespace Erdos4.Tilted

open FGKMT

theorem prod_one_add_eq_one_add_subsets {α : Type*} [DecidableEq α]
    (S H : Finset α) (hHS : H ⊆ S) (f : α → ℝ) :
    (∏ p ∈ H, (1 + f p)) = 1 +
      ∑ T ∈ S.powerset.erase ∅, if T ⊆ H then ∏ p ∈ T, f p else 0 := by
  classical
  have heq : (∑ T ∈ S.powerset, if T ⊆ H then ∏ p ∈ T, f p else 0) =
      ∑ T ∈ H.powerset, ∏ p ∈ T, f p := by
    rw [← Finset.sum_filter]
    congr 1
    ext T
    simp only [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨fun h => h.2, fun h => ⟨h.trans hHS, h⟩⟩
  rw [← Finset.prod_one_add] at heq
  rw [← heq, ← Finset.sum_erase_add _ _ (Finset.empty_mem_powerset S)]
  simp only [Finset.empty_subset, if_true, Finset.prod_empty]
  ring

theorem mean_prod_one_add_le {Ω α : Type*} [Fintype Ω] [DecidableEq α]
    (μ : FiniteLaw Ω) (S : Finset α) (H : Ω → Finset α)
    (hHS : ∀ o, H o ⊆ S) (f g : α → ℝ) (D : ℝ)
    (hf : ∀ p ∈ S, 0 ≤ f p)
    (hprob : ∀ T ∈ S.powerset.erase ∅,
      μ.prob (fun o => T ⊆ H o) ≤ D * ∏ p ∈ T, g p) :
    μ.mean (fun o => ∏ p ∈ H o, (1 + f p)) ≤
      1 + D * ((∏ p ∈ S, (1 + f p * g p)) - 1) := by
  classical
  have heq : μ.mean (fun o => ∏ p ∈ H o, (1 + f p)) =
      1 + ∑ T ∈ S.powerset.erase ∅, (∏ p ∈ T, f p) * μ.prob (fun o => T ⊆ H o) := by
    rw [μ.mean_congr (fun o => prod_one_add_eq_one_add_subsets S (H o) (hHS o) f),
      μ.mean_add, μ.mean_const, μ.mean_finset_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro T hT
    rw [FiniteLaw.prob_eq_mean, ← μ.mean_const_mul]
    apply μ.mean_congr
    intro o
    by_cases ho : T ⊆ H o <;> simp [ho]
  have hsum : (∑ T ∈ S.powerset.erase ∅, ∏ p ∈ T, (f p * g p)) =
      (∏ p ∈ S, (1 + f p * g p)) - 1 := by
    have hh := Finset.sum_erase_add (S.powerset) (fun T => ∏ p ∈ T, (f p * g p))
      (Finset.empty_mem_powerset S)
    rw [Finset.prod_empty, ← Finset.prod_one_add] at hh
    linarith
  rw [heq]
  apply add_le_add le_rfl
  calc
    _ ≤ ∑ T ∈ S.powerset.erase ∅, (∏ p ∈ T, f p) * (D * ∏ p ∈ T, g p) := by
      apply Finset.sum_le_sum
      intro T hT
      apply mul_le_mul_of_nonneg_left (hprob T hT)
      exact Finset.prod_nonneg (fun p hp => hf p ((Finset.mem_powerset.mp (Finset.mem_of_mem_erase hT)) hp))
    _ = D * ∑ T ∈ S.powerset.erase ∅, ∏ p ∈ T, (f p * g p) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro T _
      rw [Finset.prod_mul_distrib]
      ring
    _ = _ := by rw [hsum]

theorem prod_one_add_le_exp_sum {α : Type*} (S : Finset α) (f : α → ℝ)
    (hf : ∀ p ∈ S, 0 ≤ f p) :
    (∏ p ∈ S, (1 + f p)) ≤ Real.exp (∑ p ∈ S, f p) := by
  rw [Real.exp_sum]
  apply Finset.prod_le_prod
  · intro p hp
    linarith [hf p hp]
  · intro p _
    linarith [Real.add_one_le_exp (f p)]

end Erdos4.Tilted
