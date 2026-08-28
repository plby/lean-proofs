import Wikipedia.HopfProblem.DegreeCollapseNativeMorseBlockExit

/-!
# Arbitrarily small closed model blocks for the unchanged native field

A critical field germ supplies a closed model block. Shrinking its radius
constructs a block of radius `2r` with any prescribed positive bound on
`r²`, while retaining full model germs at every point of that block.
No new adapted field or flow is chosen.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}

open Classical in
theorem exists_small_native_morse_field_block (c : SignedMorseChart (E := E) f p)
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (heq : ∀ᶠ y in 𝓝 p, V y = c.descentField y) {ε : ℝ} (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ r ^ 2 < ε ∧
      closedBall (0 : c.NegativeCoordinates) (2 * r) ×ˢ
        closedBall (0 : c.PositiveCoordinates) (2 * r) ⊆ c.splitChart.target ∧
      ∀ z ∈ closedBall (0 : c.NegativeCoordinates) (2 * r) ×ˢ
        closedBall (0 : c.PositiveCoordinates) (2 * r),
        ∀ᶠ y in 𝓝 (c.splitChart.symm z), V y = c.descentField y := by
  obtain ⟨R, hR, hblock, hfield⟩ := exists_native_morse_field_block c heq
  obtain ⟨r, hr, hsmall⟩ := exists_between (lt_min (half_pos hR) (lt_min hε (by norm_num : (0 : ℝ) < 1)))
  have h2r : 2 * r ≤ R := by linarith [hsmall.trans_le (min_le_left _ _)]
  have hrε : r < ε := (hsmall.trans_le (min_le_right _ _)).trans_le (min_le_left _ _)
  have hr1 : r < 1 := (hsmall.trans_le (min_le_right _ _)).trans_le (min_le_right _ _)
  have hr2 : r ^ 2 < ε := lt_trans (by nlinarith : r ^ 2 < r) hrε
  have hsub : closedBall (0 : c.NegativeCoordinates) (2 * r) ×ˢ
      closedBall (0 : c.PositiveCoordinates) (2 * r) ⊆
      closedBall (0 : c.NegativeCoordinates) R ×ˢ closedBall (0 : c.PositiveCoordinates) R :=
    fun z hz => ⟨closedBall_subset_closedBall h2r hz.1, closedBall_subset_closedBall h2r hz.2⟩
  exact ⟨r, hr, hr2, hsub.trans hblock, fun z hz => hfield z (hsub hz)⟩

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
