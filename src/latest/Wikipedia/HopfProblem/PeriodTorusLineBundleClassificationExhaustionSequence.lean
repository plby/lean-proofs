import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationExhaustionStep
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationExhaustionSeries

/-!
# The actual compatible sequence of local primitives

Dependent recursion repeatedly uses the proved polynomial correction step.
Thus the smoothness, derivative identities, and geometric bounds required
by the gluing theorem are all proved for a constructed sequence.
-/

noncomputable section

open Set Metric
open scoped ContDiff

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassification

theorem exists_compatible_primitiveSequence {f g : ℂ × ℂ → ℂ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (hclosed : IsDbarClosed f g) :
    ∃ u : ℕ → ℂ × ℂ → ℂ,
      (∀ n, ContDiff ℝ ∞ (u n)) ∧
      (∀ n, ∀ q ∈ exhaustionDomain n,
        dbarFirst (u n) q = f q ∧ dbarSecond (u n) q = g q) ∧
      ∀ n, ∀ q ∈ exhaustionDomain n,
        ‖correctionDifference u n q‖ ≤ (1 / 2 : ℝ) ^ n := by
  classical
  obtain ⟨u₀, hu₀⟩ := exists_primitiveStage hf hg hclosed 0
  let next (n : ℕ) (x : {u // IsPrimitiveStage f g n u}) :
      {u // IsPrimitiveStage f g (n + 1) u} :=
    ⟨Classical.choose (primitiveStage_successor hf hg hclosed n x.1 x.2),
      (Classical.choose_spec (primitiveStage_successor hf hg hclosed n x.1 x.2)).1⟩
  have hnext (n : ℕ) (x : {u // IsPrimitiveStage f g n u}) (q : ℂ × ℂ)
      (hq : q ∈ closedBall (0 : ℂ) ((n : ℝ) + 1) ×ˢ
        closedBall 0 ((n : ℝ) + 1)) :
      ‖(next n x).1 q - x.1 q‖ < (1 / 2 : ℝ) ^ n :=
    (Classical.choose_spec (primitiveStage_successor hf hg hclosed n x.1 x.2)).2 q hq
  let stages : (n : ℕ) → {u // IsPrimitiveStage f g n u} :=
    Nat.rec (motive := fun n => {u // IsPrimitiveStage f g n u})
      ⟨u₀, hu₀⟩ (fun n x => next n x)
  refine ⟨fun n => (stages n).1, fun n => (stages n).2.1, ?_, ?_⟩
  · intro n q hq
    exact (stages n).2.2 q (exhaustionDomain_subset_primitiveStageSet n hq)
  · intro n q hq
    have hqc : q ∈ closedBall (0 : ℂ) ((n : ℝ) + 1) ×ˢ
        closedBall 0 ((n : ℝ) + 1) :=
      ⟨ball_subset_closedBall hq.1, ball_subset_closedBall hq.2⟩
    change ‖(next n (stages n)).1 q - (stages n).1 q‖ ≤ (1 / 2 : ℝ) ^ n
    exact (hnext n (stages n) q hqc).le

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassification
