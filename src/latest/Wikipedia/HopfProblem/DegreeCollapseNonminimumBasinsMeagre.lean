import Wikipedia.HopfProblem.DegreeCollapseNativePlaneNowhereDense
import Wikipedia.HopfProblem.DegreeCollapseNativeCoreExitNeighborhood
import Wikipedia.HopfProblem.DegreeCollapseAdaptedSurgeryBasins
import Wikipedia.HopfProblem.DegreeCollapseClockNormalizedBasins
import Wikipedia.HopfProblem.DegreeCollapseIntrinsicMorseIndex

/-!
# Nonminimum forward basins are meagre

Every convergent orbit eventually enters the constructed native Morse block.
At positive index its forward basin there is the positive coordinate plane.
One compact half-radius plane piece and its countably many negative integer
time images therefore cover the entire forward basin. Every piece is nowhere
dense in the original manifold.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ}

theorem AdaptedSurgeryWindows.nonminimum_forward_basin_meagre
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (p : criticalPoints E f) (hindex : 0 < nativeMorseIndex E f p) :
    IsMeagre {x : M | Tendsto (fun t => S.flow t x) atTop (𝓝 p.val)} := by
  let c := (S.data p).chart
  obtain ⟨r, hr, hblock, hbasin⟩ := exists_descending_morse_basin_block c hf
    (S.smooth.of_le (by simp)) S.flow S.integral S.zero S.descent (S.critical_model_germ p)
  let K := c.splitChart.symm ''
    (({0} : Set c.NegativeCoordinates) ×ˢ closedBall (0 : c.PositiveCoordinates) (r / 2))
  have hKt : ({0} : Set c.NegativeCoordinates) ×ˢ
      closedBall (0 : c.PositiveCoordinates) (r / 2) ⊆ c.splitChart.target := by
    rintro ⟨a, b⟩ ⟨ha, hb⟩
    have ha0 : a = 0 := ha
    subst a
    exact hblock ⟨mem_closedBall_self hr.le,
      closedBall_subset_closedBall (by linarith : r / 2 ≤ r) hb⟩
  have hi : 0 < Module.finrank ℝ c.NegativeCoordinates := by
    rwa [nativeMorseIndex_eq_chart c] at hindex
  have hK : IsNowhereDense K := native_positive_plane_piece_nowhereDense c hi hKt
  have hcover : {x : M | Tendsto (fun t => S.flow t x) atTop (𝓝 p.val)} ⊆
      ⋃ n : ℕ, S.flow (-(n : ℝ)) '' K := by
    intro x hx
    have hlim : Tendsto (fun n : ℕ => S.flow (n : ℝ) x) atTop (𝓝 p.val) :=
      hx.comp tendsto_natCast_atTop_atTop
    obtain ⟨n, hs, hn, hp⟩ :=
      (hlim.eventually (morse_coordinate_neighborhood c (half_pos hr) (half_pos hr))).exists
    have hnew : Tendsto (fun t => S.flow t (S.flow (n : ℝ) x)) atTop (𝓝 p.val) :=
      (flow_time_atTop_limit_iff S.flow (n : ℝ) x p.val).mpr hx
    have hz : (c.splitChart (S.flow (n : ℝ) x)).1 = 0 :=
      ((hbasin _ hs (hn.trans (half_lt_self hr)) (hp.trans (half_lt_self hr))).1).mp hnew
    have hmem : S.flow (n : ℝ) x ∈ K := by
      refine ⟨c.splitChart (S.flow (n : ℝ) x), ?_, c.splitChart.left_inv' hs⟩
      exact ⟨mem_singleton_iff.mpr hz, mem_closedBall_zero_iff.mpr hp.le⟩
    exact mem_iUnion.mpr ⟨n, S.flow (n : ℝ) x, hmem,
      (S.flow.toHomeomorph (n : ℝ)).symm_apply_apply x⟩
  apply IsMeagre.mono hcover
  apply isMeagre_iUnion
  intro n
  exact ((S.flow.toHomeomorph (-(n : ℝ))).isInducing.isNowhereDense_image hK).isMeagre

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
