import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyPuncturedDbarOneStep
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationExhaustionSeries

/-!
# The actual compatible sequence of punctured primitives

Dependent recursion uses the proved Laurent correction step, so all
smoothness, derivative identities, and geometric bounds are constructed.
-/

noncomputable section

open Set
open scoped ContDiff

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.PuncturedDbarOne

open PeriodTorusLineBundleClassification

theorem exists_compatible_primitiveSequence {f g : ℂ × ℂ → ℂ}
    (hf : ContDiffOn ℝ ∞ f domain) (hg : ContDiffOn ℝ ∞ g domain)
    (hclosed : ∀ q ∈ domain, dbarFirst g q = dbarSecond f q) :
    ∃ u : ℕ → ℂ × ℂ → ℂ,
      (∀ n, ContDiffOn ℝ ∞ (u n) domain) ∧
      (∀ n, ∀ q ∈ exhaustionDomain n, dbarFirst (u n) q = f q ∧ dbarSecond (u n) q = g q) ∧
      ∀ n, ∀ q ∈ exhaustionDomain n,
        ‖correctionDifference u n q‖ ≤ (1 / 2 : ℝ) ^ n := by
  classical
  obtain ⟨u₀, hu₀⟩ := exists_primitiveStage hf hg hclosed 0
  let next (n : ℕ) (x : {u // IsPrimitiveStage f g n u}) :
      {u // IsPrimitiveStage f g (n + 1) u} :=
    ⟨Classical.choose (primitiveStage_successor hf hg hclosed n x.1 x.2),
      (Classical.choose_spec (primitiveStage_successor hf hg hclosed n x.1 x.2)).1⟩
  have hnext (n : ℕ) (x : {u // IsPrimitiveStage f g n u}) (q : ℂ × ℂ)
      (hq : q ∈ annularClosed ((n : ℝ) + 2)) :
      ‖(next n x).1 q - x.1 q‖ < (1 / 2 : ℝ) ^ n :=
    (Classical.choose_spec (primitiveStage_successor hf hg hclosed n x.1 x.2)).2 q hq
  let stages : (n : ℕ) → {u // IsPrimitiveStage f g n u} :=
    Nat.rec (motive := fun n => {u // IsPrimitiveStage f g n u})
      ⟨u₀, hu₀⟩ (fun n x => next n x)
  refine ⟨fun n => (stages n).1, fun n => (stages n).2.1, ?_, ?_⟩
  · intro n q hq
    exact (stages n).2.2 q (exhaustionDomain_subset_primitiveStageSet n hq)
  · intro n q hq
    have hqc : q ∈ annularClosed ((n : ℝ) + 2) := annularOpen_subset_closed _ hq
    change ‖(next n (stages n)).1 q - (stages n).1 q‖ ≤ (1 / 2 : ℝ) ^ n
    exact (hnext n (stages n) q hqc).le

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.PuncturedDbarOne
