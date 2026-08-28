import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationLocalDbar

/-! # The concrete bidisc exhaustion used by the global primitive -/

noncomputable section

open Set Metric
open scoped ContDiff

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassification

def exhaustionDomain (n : ℕ) : Set (ℂ × ℂ) :=
  ball (0 : ℂ) ((n : ℝ) + 1) ×ˢ ball 0 ((n : ℝ) + 1)

def primitiveStageSet (n : ℕ) : Set (ℂ × ℂ) :=
  closedBall (0 : ℂ) ((n : ℝ) + 2) ×ˢ closedBall 0 ((n : ℝ) + 2)

theorem isOpen_exhaustionDomain (n : ℕ) : IsOpen (exhaustionDomain n) :=
  isOpen_ball.prod isOpen_ball

theorem monotone_exhaustionDomain : Monotone exhaustionDomain := by
  intro n m hnm
  have hnmR : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
  have hr : (n : ℝ) + 1 ≤ (m : ℝ) + 1 := by linarith
  exact Set.prod_mono (ball_subset_ball hr) (ball_subset_ball hr)

theorem cover_exhaustionDomain (q : ℂ × ℂ) : ∃ n, q ∈ exhaustionDomain n := by
  obtain ⟨n, hn⟩ := exists_nat_gt (max ‖q.1‖ ‖q.2‖)
  refine ⟨n, ?_, ?_⟩
  · exact mem_ball_zero_iff.mpr
      (((le_max_left _ _).trans_lt hn).trans (lt_add_one _))
  · exact mem_ball_zero_iff.mpr
      (((le_max_right _ _).trans_lt hn).trans (lt_add_one _))

theorem monotone_primitiveStageSet : Monotone primitiveStageSet := by
  intro n m hnm
  have hnmR : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
  have hr : (n : ℝ) + 2 ≤ (m : ℝ) + 2 := by linarith
  exact Set.prod_mono (closedBall_subset_closedBall hr) (closedBall_subset_closedBall hr)

theorem exhaustionDomain_subset_primitiveStageSet (n : ℕ) :
    exhaustionDomain n ⊆ primitiveStageSet n := by
  have hr : (n : ℝ) + 1 ≤ (n : ℝ) + 2 := by linarith
  exact Set.prod_mono (ball_subset_closedBall.trans (closedBall_subset_closedBall hr))
    (ball_subset_closedBall.trans (closedBall_subset_closedBall hr))

/-- A stage consists of an actual global smooth function whose coordinate
antiholomorphic derivatives agree with the data on this closed bidisc. -/
def IsPrimitiveStage (f g : ℂ × ℂ → ℂ) (n : ℕ) (u : ℂ × ℂ → ℂ) : Prop :=
  ContDiff ℝ ∞ u ∧ ∀ q ∈ primitiveStageSet n,
    dbarFirst u q = f q ∧ dbarSecond u q = g q

theorem exists_primitiveStage {f g : ℂ × ℂ → ℂ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (hclosed : IsDbarClosed f g)
    (n : ℕ) : ∃ u, IsPrimitiveStage f g n u :=
  exists_smooth_primitive_on_closedBidisc hf hg hclosed ((n : ℝ) + 2) (by positivity)

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassification
