import ErdosProblems.Erdos346.Proof

/-!
Liam Price and GPT-5.5's formalized proof claim, ported to Lean 4.33.0.
The source and the distinction from the limit-exists variant are documented
in Erdos346/README.md.
-/

namespace Erdos346

/-- A sequence with the two deletion properties and nonconvergent quotients. -/
theorem erdos_346_counterexample :
    ∃ a : ℕ → ℕ, StrictMono a ∧ (∀ n, 0 < a n) ∧
      (∀ D : Set ℕ, D.Finite →
        ∃ H, ∀ n, H ≤ n → n ∈ subsetSums a Dᶜ) ∧
      (∀ D : Set ℕ, D.Infinite →
        ∀ H, ∃ n, H ≤ n ∧ n ∉ subsetSums a Dᶜ) ∧
      (∀ n, (6 : ℝ) / 5 ≤ (a (n + 1) : ℝ) / a n) ∧
      (∃ N : ℕ → ℕ, StrictMono N ∧
        Filter.Tendsto (fun j => (a (N j) : ℝ) / a (N j - 1)) Filter.atTop
          (nhds Real.goldenRatio) ∧
        Filter.Tendsto (fun j => (a (N j + 1) : ℝ) / a (N j)) Filter.atTop
          (nhds (Real.goldenRatio + (1 : ℝ) / 4))) ∧
      ¬ ∃ x : ℝ, Filter.Tendsto (fun n => (a (n + 1) : ℝ) / a n)
        Filter.atTop (nhds x) := by
  exact erdos346

/-- The deletion hypotheses and a uniform ratio gap do not force convergence. -/
theorem not_erdos_346 :
    ¬ ∀ a : ℕ → ℕ, StrictMono a → (∀ n, 0 < a n) →
      (∀ D : Set ℕ, D.Finite →
        ∃ H, ∀ n, H ≤ n → n ∈ subsetSums a Dᶜ) →
      (∀ D : Set ℕ, D.Infinite →
        ∀ H, ∃ n, H ≤ n ∧ n ∉ subsetSums a Dᶜ) →
      (∃ ε : ℝ, 0 < ε ∧ ∀ n, 1 + ε ≤ (a (n + 1) : ℝ) / a n) →
      Filter.Tendsto (fun n => (a (n + 1) : ℝ) / a n) Filter.atTop
        (nhds Real.goldenRatio) := by
  intro hall
  obtain ⟨a, ha, hp, hf, hi, hgap, _, hnot⟩ := erdos_346_counterexample
  apply hnot
  refine ⟨Real.goldenRatio, hall a ha hp hf hi ?_⟩
  refine ⟨(1 : ℝ) / 5, by norm_num, fun n => ?_⟩
  norm_num at ⊢
  exact hgap n

end Erdos346

#print axioms Erdos346.erdos_346_counterexample
#print axioms Erdos346.not_erdos_346
