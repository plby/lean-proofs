import Arxiv.Arxiv2411_18291.VariableCountSampling

/-! # Halving a finite family of sets simultaneously -/

open Finset
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291

theorem exists_balanced_subset_family {I T : Type*} [DecidableEq I]
    (D : Finset I) (tests : Finset T) (s : T → Finset I)
    (hsub : ∀ t ∈ tests, s t ⊆ D) {c d : ℝ} (hc : 0 ≤ c)
    (hlower : ∀ t ∈ tests, d ≤ ((s t).card : ℝ))
    (hsmall : tests.card * (2 * Real.exp (-(d * c ^ 2 / (4 * (1 + 2 * c))))) < 1) :
    ∃ A : Finset I, A ⊆ D ∧ ∀ t ∈ tests,
      |((A ∩ s t).card : ℝ) - ((s t).card : ℝ) / 2| ≤ c * (((s t).card : ℝ) / 2) := by
  let p (_ : I) : unitInterval := ⟨1 / 2, by constructor <;> norm_num⟩
  have hmean (t : T) (_ : t ∈ tests) : (∑ i ∈ s t, (p i : ℝ)) = ((s t).card : ℝ) / 2 := by
    simp only [p, sum_const, nsmul_eq_mul]
    ring
  have heq : (d / 2) * c ^ 2 / (2 * (1 + 2 * c)) = d * c ^ 2 / (4 * (1 + 2 * c)) := by
    field_simp
    ring
  apply IndependentBernoulliChoice.exists_subset_with_variable_concentrated_counts
    D tests s hsub p (fun t => ((s t).card : ℝ) / 2) hc hmean
    (fun t ht => div_le_div_of_nonneg_right (hlower t ht) (by norm_num : (0 : ℝ) ≤ 2))
  simpa only [heq] using hsmall

end Arxiv2411_18291
