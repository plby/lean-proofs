import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationExhaustionDomains
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationDbarAnalytic
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationPolydiscApproximationError

/-!
# Constructing the next compatible primitive

The difference of two local primitives is genuinely analytic.  Its explicit
entire polynomial approximation corrects the next primitive without changing
either antiholomorphic derivative, and gives the geometric error bound.
-/

noncomputable section

open Set Metric
open scoped ContDiff

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassification

open PeriodTorusLineBundleClassificationPolydiscApproximation
  (exists_entire_polynomial_approximation)

theorem primitiveStage_successor {f g : ℂ × ℂ → ℂ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (hclosed : IsDbarClosed f g)
    (n : ℕ) (u : ℂ × ℂ → ℂ) (hu : IsPrimitiveStage f g n u) :
    ∃ v, IsPrimitiveStage f g (n + 1) v ∧
      ∀ q ∈ closedBall (0 : ℂ) ((n : ℝ) + 1) ×ˢ closedBall 0 ((n : ℝ) + 1),
        ‖v q - u q‖ < (1 / 2 : ℝ) ^ n := by
  obtain ⟨w, hw⟩ := exists_primitiveStage hf hg hclosed (n + 1)
  let V : Set (ℂ × ℂ) := ball (0 : ℂ) ((n : ℝ) + 2) ×ˢ ball 0 ((n : ℝ) + 2)
  have hV : IsOpen V := isOpen_ball.prod isOpen_ball
  have hVs : V ⊆ primitiveStageSet n := Set.prod_mono ball_subset_closedBall ball_subset_closedBall
  have hVs' : V ⊆ primitiveStageSet (n + 1) :=
    hVs.trans (monotone_primitiveStageSet (Nat.le_succ n))
  have hdiff : AnalyticOnNhd ℂ (fun q => w q - u q) V := by
    apply analyticOnNhd_sub_of_coordinate_dbar_eq hV
      (hw.1.differentiable (by simp)).differentiableOn
      (hu.1.differentiable (by simp)).differentiableOn
    · intro q hq
      exact (hw.2 q (hVs' hq)).1.trans (hu.2 q (hVs hq)).1.symm
    · intro q hq
      exact (hw.2 q (hVs' hq)).2.trans (hu.2 q (hVs hq)).2.symm
  have hmid : closedBall (0 : ℂ) ((n : ℝ) + 3 / 2) ×ˢ
      closedBall 0 ((n : ℝ) + 3 / 2) ⊆ V :=
    Set.prod_mono (closedBall_subset_ball (by linarith))
      (closedBall_subset_ball (by linarith))
  obtain ⟨N, a, P, _, hP, herr⟩ := exists_entire_polynomial_approximation
    (r := (n : ℝ) + 1) (R := (n : ℝ) + 3 / 2) (ε := (1 / 2 : ℝ) ^ n)
    (by positivity) (by linarith) (by positivity) (hdiff.mono hmid)
  have hPr : ContDiff ℝ ∞ P := (hP.of_le le_top).restrict_scalars ℝ
  have hPzero (q : ℂ × ℂ) : dbarFirst P q = 0 ∧ dbarSecond P q = 0 :=
    coordinate_dbar_zero_of_analyticAt (hP.contDiffAt.analyticAt)
  refine ⟨fun q => w q - P q, ⟨hw.1.sub hPr, ?_⟩, ?_⟩
  · intro q hq
    constructor
    · rw [dbarFirst_sub (hw.1.differentiable (by simp) q)
        (hPr.differentiable (by simp) q), (hPzero q).1, sub_zero]
      exact (hw.2 q hq).1
    · rw [dbarSecond_sub (hw.1.differentiable (by simp) q)
        (hPr.differentiable (by simp) q), (hPzero q).2, sub_zero]
      exact (hw.2 q hq).2
  · intro q hq
    dsimp only
    rw [show (w q - P q) - u q = -(P q - (w q - u q)) by ring, norm_neg]
    exact herr q hq

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassification
