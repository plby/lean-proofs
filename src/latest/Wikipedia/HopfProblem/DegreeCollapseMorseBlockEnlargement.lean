import Wikipedia.HopfProblem.DegreeCollapseNativeMorseClosedBlocks
import Mathlib.Analysis.Normed.Module.Ball.Pointwise

/-!
# Controlled enlargement of the original closed Morse block

Compactness leaves room to enlarge a closed coordinate block inside its
open chart, while keeping the new radius below any prescribed larger
bound. The original surgery radius and its level sets are unchanged.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

theorem exists_larger_closedBall_inside_open
    {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] [ProperSpace A]
    {U : Set A} (hU : IsOpen U) {R B : ℝ} (hR : 0 ≤ R)
    (hRB : R < B) (hsub : closedBall (0 : A) R ⊆ U) :
    ∃ S, R < S ∧ S < B ∧ closedBall (0 : A) S ⊆ U := by
  obtain ⟨δ, hδ, hδU⟩ :=
    (isCompact_closedBall (0 : A) R).exists_cthickening_subset_open hU hsub
  rw [cthickening_closedBall hδ.le hR] at hδU
  obtain ⟨S, hRS, hSm⟩ := exists_between (lt_min (by linarith : R < δ + R) hRB)
  exact ⟨S, hRS, hSm.trans_le (min_le_right _ _),
    (closedBall_subset_closedBall (hSm.le.trans (min_le_left _ _))).trans hδU⟩

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  {f : M → ℝ} {p : M}

open Classical in
theorem exists_morse_block_enlargement (c : SignedMorseChart (E := E) f p)
    {r : ℝ} (hr : 0 < r)
    (hblock : closedBall (0 : c.NegativeCoordinates) (2 * r) ×ˢ
      closedBall (0 : c.PositiveCoordinates) (2 * r) ⊆ c.splitChart.target) :
    ∃ R, 2 * r < R ∧ R < 3 * r ∧
      closedBall (0 : c.NegativeCoordinates) R ×ˢ
        closedBall (0 : c.PositiveCoordinates) R ⊆ c.splitChart.target := by
  have hb : closedBall (0 : c.NegativeCoordinates × c.PositiveCoordinates) (2 * r) ⊆
      c.splitChart.target := by
    simpa only [closedBall_prod_same, Prod.mk_zero_zero] using hblock
  obtain ⟨R, hR, hR', hsub⟩ := exists_larger_closedBall_inside_open
    c.splitChart.open_target (by positivity : 0 ≤ 2 * r) (by linarith : 2 * r < 3 * r) hb
  refine ⟨R, hR, hR', ?_⟩
  simpa only [closedBall_prod_same, Prod.mk_zero_zero] using hsub

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
