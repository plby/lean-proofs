import ErdosProblems.Erdos19.SubsetSampling
import ErdosProblems.Erdos19.SamplingArithmetic

/-! # One sample controlling degrees and exponentially many cuts -/

namespace Erdos19

open Finset

theorem eventually_sample_linear_and_quadratic_families
    (k : ℕ) (hk : 0 < k) (eta : ℝ) (heta : 0 < eta) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ (V I J : Type*) [Fintype V] [DecidableEq V] [Fintype I] [Fintype J],
      Fintype.card I ≤ n → Fintype.card J ≤ 4 ^ n →
      ∀ U : Finset V, ∀ A : I → Finset V, ∀ B : J → Finset V,
      (∀ i, A i ⊆ U) → (∀ j, B j ⊆ U) →
      (∀ i, (A i).card ≤ n) → (∀ j, (B j).card ≤ n ^ 2) →
      ∃ R : Finset V, R ⊆ U ∧
        (∀ i, |((A i ∩ R).card : ℝ) - (A i).card / k| < eta * n) ∧
        (∀ j, |((B j ∩ R).card : ℝ) - (B j).card / k| < eta * (n : ℝ) ^ 2) := by
  classical
  let c := eta ^ 2 / 2
  have hc : 0 < c := by dsimp only [c]; positivity
  obtain ⟨N₀, hN₀⟩ := exists_linear_quadratic_tail_budget c hc
  refine ⟨max N₀ 1, ?_⟩
  intro n hn V I J _ _ _ _ hI hJ U A B hAU hBU hA hB
  have hnpos : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  letI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  let S : I ⊕ J → Finset V := Sum.elim A B
  let t : I ⊕ J → ℝ := Sum.elim (fun _ ↦ eta * n) (fun _ ↦ eta * (n : ℝ) ^ 2)
  let L : I ⊕ J → ℝ := Sum.elim (fun _ ↦ n) (fun _ ↦ (n : ℝ) ^ 2)
  have hexp₁ : -(eta * (n : ℝ)) ^ 2 / (2 * n) = -c * n := by
    dsimp only [c]
    field_simp
  have hexp₂ : -(eta * (n : ℝ) ^ 2) ^ 2 / (2 * (n : ℝ) ^ 2) =
      -c * (n : ℝ) ^ 2 := by
    dsimp only [c]
    field_simp
  have hprob : (∑ i : I ⊕ J, 2 * Real.exp (-(t i) ^ 2 / (2 * L i))) < 1 := by
    rw [Fintype.sum_sum_type]
    simp only [t, L, Sum.elim_inl, Sum.elim_inr, hexp₁, hexp₂,
      sum_const, card_univ, nsmul_eq_mul]
    have hIR : (Fintype.card I : ℝ) ≤ n := by exact_mod_cast hI
    have hJR : (Fintype.card J : ℝ) ≤ (4 : ℝ) ^ n := by exact_mod_cast hJ
    calc
      (Fintype.card I : ℝ) * (2 * Real.exp (-c * n)) +
          (Fintype.card J : ℝ) * (2 * Real.exp (-c * (n : ℝ) ^ 2)) ≤
        (n : ℝ) * (2 * Real.exp (-c * n)) +
          (4 : ℝ) ^ n * (2 * Real.exp (-c * (n : ℝ) ^ 2)) := by
        exact add_le_add (mul_le_mul_of_nonneg_right hIR (by positivity))
          (mul_le_mul_of_nonneg_right hJR (by positivity))
      _ = 2 * (n : ℝ) * Real.exp (-c * n) +
          2 * (4 : ℝ) ^ n * Real.exp (-c * (n : ℝ) ^ 2) := by ring
      _ < 1 := hN₀ n ((le_max_left _ _).trans hn)
  obtain ⟨R, hRU, hR⟩ := exists_subset_with_simultaneous_counts U S
    (by intro i; cases i with | inl i => exact hAU i | inr j => exact hBU j)
    (⟨0, hk⟩ : Fin k) t L
    (by intro i; cases i <;> dsimp only [t, Sum.elim_inl, Sum.elim_inr] <;> positivity)
    (by intro i; cases i <;> dsimp only [L, Sum.elim_inl, Sum.elim_inr] <;> positivity)
    (by
      intro i
      cases i with
      | inl i =>
        dsimp only [S, L, Sum.elim_inl]
        exact_mod_cast hA i
      | inr j =>
        dsimp only [S, L, Sum.elim_inr]
        exact_mod_cast hB j)
    hprob
  refine ⟨R, hRU, ?_, ?_⟩
  · intro i
    simpa only [S, t, Sum.elim_inl, Fintype.card_fin] using hR (Sum.inl i)
  · intro j
    simpa only [S, t, Sum.elim_inr, Fintype.card_fin] using hR (Sum.inr j)

#print axioms eventually_sample_linear_and_quadratic_families

end Erdos19
